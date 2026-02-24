#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Binance Futures Screener v6.2 - Madrid Ribbon + Volume Spike + Level Strategies (1H) + Charts
Адаптировано для Render (asyncio, health check, env variables)
"""

import asyncio
import websockets
import json
import time
from datetime import datetime
import ccxt
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import telebot
import sys
import os
import logging
import warnings
import tempfile
import signal
import concurrent.futures
from collections import defaultdict

warnings.filterwarnings('ignore')

# ==================== КОДИРОВКА ====================
if os.name == 'nt':
    os.system('chcp 65001 > nul')
    sys.stdout.reconfigure(encoding='utf-8', errors='ignore')
    sys.stderr.reconfigure(encoding='utf-8', errors='ignore')


class EmojiSafeHandler(logging.StreamHandler):
    def emit(self, record):
        try:
            msg = self.format(record)
            self.stream.write(msg + self.terminator)
            self.flush()
        except UnicodeEncodeError:
            safe_msg = record.getMessage()
            emoji_map = {
                '✅': '[OK]', '❌': '[ERROR]', '⚠️': '[WARN]', '🌀': '[CYCLE]',
                '📊': '[INFO]', '📈': '[STAT]', '📤': '[SENT]', '📡': '[DATA]',
                '💰': '[PRICE]', '🎯': '[COND]', '🛑': '[STOP]', '🔄': '[RESTART]',
                '⏰': '[TIME]', '⏳': '[WAIT]', '⏹️': '[PAUSE]', '🚀': '[BULL]',
                '🔻': '[BEAR]', '🟢': '[GREEN]', '🔴': '[RED]', '📉': '[DOWN]',
                '📐': '[CROSS]', '🔢': '[TRADES]'
            }
            for e, r in emoji_map.items():
                safe_msg = safe_msg.replace(e, r)
            record.msg = safe_msg
            msg = self.format(record)
            self.stream.write(msg + self.terminator)
            self.flush()


# ==================== НАСТРОЙКИ (из окружения) ====================
TELEGRAM_BOT_TOKEN = os.environ.get('TELEGRAM_BOT_TOKEN', '')
TELEGRAM_CHANNEL_ID = os.environ.get('TELEGRAM_CHANNEL_ID', )

TIMEFRAME = '5m'
SCAN_INTERVAL = 2          # минуты между сканированиями
MAX_PAIRS_TO_ANALYZE = 200
MIN_VOLUME_24H_USDT = 10_000_000
MIN_TRADES_24H = 100_000
MIN_PRICE_CHANGE_24H = 1.5

ENABLE_TELEGRAM = True
SEND_CHART = True

USE_EXP_MA = True          # EMA или SMA

# === НАСТРОЙКИ ДЛЯ АНОМАЛЬНОГО ОБЪЁМА ===
ENABLE_VOLUME_SPIKE = True
VOLUME_PERIOD = 20
VOLUME_SPIKE_THRESHOLD = 3.0
MIN_PRICE_CHANGE_5M = 2.0

# === НОВЫЕ УЛУЧШЕННЫЕ ФИЛЬТРЫ ===
ENABLE_MULTI_TIMEFRAME_FILTER = True
ENABLE_ATR_FILTER = True
ATR_THRESHOLD = 0.3
ENABLE_VOLUME_SPIKE_IMPROVED = True
VOLUME_SPIKE_COEFF = 2.0
ENABLE_LOW_VOLUME_FILTER = True
MIN_LAST_VOLUME_RATIO = 0.5

# === НАСТРОЙКИ СТРАТЕГИЙ УРОВНЕЙ (1H) ===
ENABLE_LEVEL_STRATEGIES = True
LEVEL_TIMEFRAME = '1h'
LEVEL_LOOKBACK_DAYS = 3
LEVEL_MIN_DISTANCE_PERCENT = 0.2
LEVEL_BREAKOUT_CONFIRM_CANDLES = 2
LEVEL_CACHE_TTL = 1800

# ==================== НАСТРОЙКИ WEBSOCKET ====================
WS_HOST = '0.0.0.0'   # слушаем все интерфейсы
WS_PORT = int(os.environ.get('PORT', 8765))
connected_clients = set()

# ==================== ФОРМАТИРОВАНИЕ ЧИСЕЛ ====================
def format_large_number(value):
    try:
        if pd.isna(value) or value == 0:
            return "0"
        value = float(value)
        thresholds = [
            (1_000_000_000, 'B', 3),
            (1_000_000, 'M', 2),
            (1_000, 'K', 1)
        ]
        for th, suf, dec in thresholds:
            if value >= th:
                return f"{value / th:,.{dec}f}{suf}".replace(',', ' ')
        return f"{value:,.0f}".replace(',', ' ')
    except:
        return str(value)


# ==================== MADRID RIBBON ====================
class MadridMovingAverageRibbon:
    COLORS = {
        'LIME': '#00FF00',
        'MAROON': '#800000',
        'RUBI': '#FF0000',
        'GREEN': '#008000',
        'GRAY': '#808080',
    }

    BULL = 1
    BEAR = -1
    WARNING_BULL = 2
    WARNING_BEAR = -2
    WARNING_BULL_STRONG = 3
    WARNING_BEAR_STRONG = -3
    NONE = 0

    def __init__(self, use_exp=True):
        self.use_exp = use_exp
        self.periods = [5, 10, 15, 20, 25, 30, 35, 40, 45, 50,
                        55, 60, 65, 70, 75, 80, 85, 90]
        self.ref_period = 100
        self.line_widths = {5: 3, 90: 3}

    @staticmethod
    def calculate_ema(data, period):
        return pd.Series(data).ewm(span=period, adjust=False).mean().values

    @staticmethod
    def calculate_sma(data, period):
        return pd.Series(data).rolling(window=period, min_periods=1).mean().values

    def calculate_ma(self, data, period):
        return self.calculate_ema(data, period) if self.use_exp else self.calculate_sma(data, period)

    def ma_color(self, ma, ma_ref):
        colors = []
        for i in range(len(ma)):
            if i == 0 or pd.isna(ma[i]) or pd.isna(ma_ref[i]):
                colors.append(self.COLORS['GRAY'])
                continue
            diff = ma[i] - ma[i - 1]
            if diff >= 0 and ma[i] > ma_ref[i]:
                colors.append(self.COLORS['LIME'])
            elif diff < 0 and ma[i] > ma_ref[i]:
                colors.append(self.COLORS['MAROON'])
            elif diff <= 0 and ma[i] < ma_ref[i]:
                colors.append(self.COLORS['RUBI'])
            elif diff >= 0 and ma[i] < ma_ref[i]:
                colors.append(self.COLORS['GREEN'])
            else:
                colors.append(self.COLORS['GRAY'])
        return colors

    def calculate(self, data):
        if isinstance(data, pd.Series):
            data = data.values
        results = {}
        ma_dict = {}
        ma_ref = self.calculate_ma(data, self.ref_period)
        results['ma_100'] = ma_ref
        for p in self.periods:
            ma = self.calculate_ma(data, p)
            ma_dict[f'ma_{p}'] = ma
            results[f'ma_{p}'] = ma
        for p in self.periods:
            results[f'ma_{p}_color'] = self.ma_color(results[f'ma_{p}'], ma_ref)
        results['all_ma'] = pd.DataFrame(ma_dict)
        results['ma_ref'] = ma_ref
        return results

    def get_enhanced_signals(self, results):
        ma_df = results['all_ma']
        signals = []
        signal_colors = []
        total_ma = len(self.periods)

        for i in range(len(ma_df)):
            if i < min(self.periods):
                signals.append(self.NONE)
                signal_colors.append(self.COLORS['GRAY'])
                continue

            curr_vals = ma_df.iloc[i].values
            curr_colors = [results[f'ma_{p}_color'][i] for p in self.periods]

            above_ref = sum(curr_vals > results['ma_ref'][i])
            trend_strength = above_ref / total_ma

            c5 = results['ma_5_color'][i]
            p5 = results['ma_5_color'][i-1] if i > 0 else c5

            sig = self.NONE
            col = self.COLORS['GRAY']

            bullish_aligned = all(c == self.COLORS['LIME'] for c in curr_colors)
            if bullish_aligned:
                for idx in range(len(self.periods)-1):
                    if curr_vals[idx] <= curr_vals[idx+1]:
                        bullish_aligned = False
                        break

            bearish_aligned = all(c == self.COLORS['RUBI'] for c in curr_colors)
            if bearish_aligned:
                for idx in range(len(self.periods)-1):
                    if curr_vals[idx] >= curr_vals[idx+1]:
                        bearish_aligned = False
                        break

            if bullish_aligned:
                if i > 0:
                    prev_vals = ma_df.iloc[i-1].values
                    prev_colors = [results[f'ma_{p}_color'][i-1] for p in self.periods]
                    prev_bull = all(c == self.COLORS['LIME'] for c in prev_colors)
                    if prev_bull:
                        for idx in range(len(self.periods)-1):
                            if prev_vals[idx] <= prev_vals[idx+1]:
                                prev_bull = False
                                break
                    if not prev_bull:
                        sig = self.BULL
                        col = self.COLORS['LIME']
                else:
                    sig = self.BULL
                    col = self.COLORS['LIME']

            if bearish_aligned and sig == self.NONE:
                if i > 0:
                    prev_vals = ma_df.iloc[i-1].values
                    prev_colors = [results[f'ma_{p}_color'][i-1] for p in self.periods]
                    prev_bear = all(c == self.COLORS['RUBI'] for c in prev_colors)
                    if prev_bear:
                        for idx in range(len(self.periods)-1):
                            if prev_vals[idx] >= prev_vals[idx+1]:
                                prev_bear = False
                                break
                    if not prev_bear:
                        sig = self.BEAR
                        col = self.COLORS['RUBI']
                else:
                    sig = self.BEAR
                    col = self.COLORS['RUBI']

            if sig == self.NONE:
                if p5 == self.COLORS['LIME'] and c5 == self.COLORS['GREEN'] and trend_strength > 0.5:
                    sig = self.WARNING_BULL
                    col = self.COLORS['GREEN']
                elif p5 == self.COLORS['RUBI'] and c5 == self.COLORS['MAROON'] and trend_strength < 0.5:
                    sig = self.WARNING_BEAR
                    col = self.COLORS['MAROON']

            if sig == self.NONE:
                if p5 == self.COLORS['GREEN'] and c5 == self.COLORS['LIME'] and trend_strength > 0.5:
                    sig = self.WARNING_BULL_STRONG
                    col = self.COLORS['LIME']
                elif p5 == self.COLORS['MAROON'] and c5 == self.COLORS['RUBI'] and trend_strength < 0.5:
                    sig = self.WARNING_BEAR_STRONG
                    col = self.COLORS['RUBI']

            signals.append(sig)
            signal_colors.append(col)

        return {
            'signals': signals,
            'signal_colors': signal_colors,
            'bull': [s == self.BULL for s in signals],
            'bear': [s == self.BEAR for s in signals],
            'warning_bull': [s == self.WARNING_BULL for s in signals],
            'warning_bear': [s == self.WARNING_BEAR for s in signals],
            'warning_bull_strong': [s == self.WARNING_BULL_STRONG for s in signals],
            'warning_bear_strong': [s == self.WARNING_BEAR_STRONG for s in signals],
        }


# ==================== АНАЛИЗ УРОВНЕЙ (1H) ====================
class LevelAnalyzer:
    def __init__(self, exchange, cache_ttl=LEVEL_CACHE_TTL):
        self.exchange = exchange
        self.cache_ttl = cache_ttl
        self.cache = {}

    def _get_cached_levels(self, symbol):
        if symbol in self.cache:
            levels, ts = self.cache[symbol]
            if time.time() - ts < self.cache_ttl:
                return levels
        return None

    def _set_cached_levels(self, symbol, levels):
        self.cache[symbol] = (levels, time.time())

    def fetch_1h_data(self, symbol, limit=200):
        try:
            ohlcv = self.exchange.fetch_ohlcv(symbol, LEVEL_TIMEFRAME, limit=limit)
            if not ohlcv or len(ohlcv) < 50:
                return None
            df = pd.DataFrame(ohlcv, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            df.set_index('timestamp', inplace=True)
            return df
        except Exception as e:
            logging.error(f"Ошибка загрузки 1H данных для {symbol}: {e}")
            return None

    def find_swing_points(self, df, window=5):
        highs = df['high']
        lows = df['low']
        swing_highs = []
        swing_lows = []

        for i in range(window, len(df) - window):
            if all(highs.iloc[i] >= highs.iloc[i - j] for j in range(1, window + 1)) and \
               all(highs.iloc[i] >= highs.iloc[i + j] for j in range(1, window + 1)):
                swing_highs.append((df.index[i], highs.iloc[i]))
            if all(lows.iloc[i] <= lows.iloc[i - j] for j in range(1, window + 1)) and \
               all(lows.iloc[i] <= lows.iloc[i + j] for j in range(1, window + 1)):
                swing_lows.append((df.index[i], lows.iloc[i]))

        return swing_highs, swing_lows

    def cluster_prices(self, prices, threshold_percent=0.5):
        if not prices:
            return []
        prices = sorted(prices)
        clusters = []
        current_cluster = [prices[0]]

        for p in prices[1:]:
            if abs(p - current_cluster[-1]) / current_cluster[-1] * 100 < threshold_percent:
                current_cluster.append(p)
            else:
                clusters.append(np.mean(current_cluster))
                current_cluster = [p]
        clusters.append(np.mean(current_cluster))
        return clusters

    def detect_consolidation_zones(self, df, lookback=50, atr_mult=1.5):
        if len(df) < lookback:
            return []
        recent = df.iloc[-lookback:]
        high = recent['high'].max()
        low = recent['low'].min()
        atr = (recent['high'] - recent['low']).mean()

        if (high - low) < atr * atr_mult:
            return [(high + low) / 2]
        return []

    def calculate_levels(self, symbol):
        cached = self._get_cached_levels(symbol)
        if cached is not None:
            return cached

        df = self.fetch_1h_data(symbol)
        if df is None or len(df) < 100:
            return []

        swing_highs, swing_lows = self.find_swing_points(df)
        high_prices = [p[1] for p in swing_highs]
        low_prices = [p[1] for p in swing_lows]

        res_levels = self.cluster_prices(high_prices, threshold_percent=0.5)
        sup_levels = self.cluster_prices(low_prices, threshold_percent=0.5)
        cons_zones = self.detect_consolidation_zones(df)

        level_dict = defaultdict(lambda: {'price': 0, 'strength': 0, 'type': 'unknown'})
        for p in res_levels:
            rounded = round(p, 2)
            level_dict[rounded]['price'] = p
            level_dict[rounded]['strength'] += 1
            level_dict[rounded]['type'] = 'resistance'
        for p in sup_levels:
            rounded = round(p, 2)
            level_dict[rounded]['price'] = p
            level_dict[rounded]['strength'] += 1
            level_dict[rounded]['type'] = 'support' if level_dict[rounded]['type'] == 'unknown' else 'both'
        for p in cons_zones:
            rounded = round(p, 2)
            level_dict[rounded]['price'] = p
            level_dict[rounded]['strength'] += 1
            level_dict[rounded]['type'] = 'support' if level_dict[rounded]['type'] == 'unknown' else 'both'

        levels = [{'price': v['price'], 'strength': v['strength'], 'type': v['type']} for v in level_dict.values()]
        levels.sort(key=lambda x: x['price'])

        self._set_cached_levels(symbol, levels)
        return levels

    def check_level_events(self, symbol, df_5m, levels, current_price):
        if not levels:
            return []

        signals = []
        last_candle = df_5m.iloc[-1]
        prev_candle = df_5m.iloc[-2] if len(df_5m) > 1 else None
        min_dist = current_price * LEVEL_MIN_DISTANCE_PERCENT / 100

        for level in levels:
            level_price = level['price']
            dist = abs(current_price - level_price)
            if dist > min_dist * 3:
                continue

            if level['type'] in ('resistance', 'both'):
                if last_candle['close'] > level_price and prev_candle is not None and prev_candle['close'] <= level_price:
                    vol_ratio = last_candle['volume'] / df_5m['volume'].iloc[-LEVEL_BREAKOUT_CONFIRM_CANDLES-1:-1].mean()
                    if vol_ratio > 1.5:
                        signals.append({
                            'type': 'LEVEL_BREAKOUT_BULL',
                            'level_price': level_price,
                            'level_strength': level['strength'],
                            'distance_percent': dist / current_price * 100,
                            'volume_ratio': vol_ratio,
                            'strategy': 'level'
                        })

                if prev_candle is not None and prev_candle['high'] > level_price and last_candle['close'] < level_price:
                    signals.append({
                        'type': 'LEVEL_FAKEOUT_BEAR',
                        'level_price': level_price,
                        'level_strength': level['strength'],
                        'distance_percent': dist / current_price * 100,
                        'strategy': 'level'
                    })

            if level['type'] in ('support', 'both'):
                if last_candle['close'] < level_price and prev_candle is not None and prev_candle['close'] >= level_price:
                    vol_ratio = last_candle['volume'] / df_5m['volume'].iloc[-LEVEL_BREAKOUT_CONFIRM_CANDLES-1:-1].mean()
                    if vol_ratio > 1.5:
                        signals.append({
                            'type': 'LEVEL_BREAKOUT_BEAR',
                            'level_price': level_price,
                            'level_strength': level['strength'],
                            'distance_percent': dist / current_price * 100,
                            'volume_ratio': vol_ratio,
                            'strategy': 'level'
                        })

                if prev_candle is not None and prev_candle['low'] < level_price and last_candle['close'] > level_price:
                    signals.append({
                        'type': 'LEVEL_FAKEOUT_BULL',
                        'level_price': level_price,
                        'level_strength': level['strength'],
                        'distance_percent': dist / current_price * 100,
                        'strategy': 'level'
                    })

            if dist < min_dist:
                candle_range = last_candle['high'] - last_candle['low']
                body = abs(last_candle['close'] - last_candle['open'])
                if candle_range > 2 * body:
                    if last_candle['high'] > level_price and last_candle['close'] < level_price and last_candle['open'] < level_price:
                        signals.append({
                            'type': 'LEVEL_APPROACH_BEAR',
                            'level_price': level_price,
                            'level_strength': level['strength'],
                            'distance_percent': dist / current_price * 100,
                            'strategy': 'level'
                        })
                    elif last_candle['low'] < level_price and last_candle['close'] > level_price and last_candle['open'] > level_price:
                        signals.append({
                            'type': 'LEVEL_APPROACH_BULL',
                            'level_price': level_price,
                            'level_strength': level['strength'],
                            'distance_percent': dist / current_price * 100,
                            'strategy': 'level'
                        })

        return signals


# ==================== НОВЫЕ ФУНКЦИИ ДЛЯ ФИЛЬТРОВ ====================
h1_cache = {}
H1_CACHE_TTL = 300

def fetch_h1_data_cached(symbol):
    now = time.time()
    if symbol in h1_cache:
        df, ts = h1_cache[symbol]
        if now - ts < H1_CACHE_TTL:
            return df
    try:
        ohlcv = exchange.fetch_ohlcv(symbol, '1h', limit=100)
        if not ohlcv or len(ohlcv) < 20:
            return None
        df = pd.DataFrame(ohlcv, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
        df.set_index('timestamp', inplace=True)
        h1_cache[symbol] = (df, now)
        return df
    except Exception as e:
        logging.error(f"Ошибка загрузки 1H для {symbol}: {e}")
        return None

def get_trend_h1(symbol):
    df = fetch_h1_data_cached(symbol)
    if df is None or len(df) < 50:
        return None
    ema50 = df['close'].ewm(span=50).mean().iloc[-1]
    last_close = df['close'].iloc[-1]
    if last_close > ema50:
        return 'bull'
    else:
        return 'bear'

def compute_atr(df, period=14):
    high_low = df['high'] - df['low']
    high_close = np.abs(df['high'] - df['close'].shift())
    low_close = np.abs(df['low'] - df['close'].shift())
    tr = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
    atr = tr.rolling(window=period).mean()
    return atr.iloc[-1] if not pd.isna(atr.iloc[-1]) else None

def check_volume_spike_improved(df):
    if len(df) < VOLUME_PERIOD + 5:
        return None, None, None

    last_volume = df['volume'].iloc[-1]
    recent_volumes = df['volume'].iloc[-(VOLUME_PERIOD+1):-1]
    if len(recent_volumes) < VOLUME_PERIOD:
        return None, None, None

    mean_vol = recent_volumes.mean()
    if mean_vol == 0:
        return None, None, None

    spike_ratio = last_volume / mean_vol
    price_change_5m = (df['close'].iloc[-1] - df['close'].iloc[-2]) / df['close'].iloc[-2] * 100

    if spike_ratio > VOLUME_SPIKE_COEFF and abs(price_change_5m) >= MIN_PRICE_CHANGE_5M:
        signal_type = 'VOLUME_SPIKE_BULL' if price_change_5m > 0 else 'VOLUME_SPIKE_BEAR'
        return signal_type, spike_ratio, price_change_5m

    return None, spike_ratio, price_change_5m


# ==================== ЛОГГЕР ====================
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[EmojiSafeHandler()]   # только консоль
)
logger = logging.getLogger(__name__)


# ==================== ИНИЦИАЛИЗАЦИЯ БИРЖИ ====================
def init_exchange():
    try:
        ex = ccxt.binance({
            'options': {'defaultType': 'future'},
            'enableRateLimit': True,
            'rateLimit': 800,
            'timeout': 30000,
        })
        ex.fetch_time()
        logger.info("Binance API подключен")
        return ex
    except Exception as e:
        logger.error(f"Ошибка подключения: {e}")
        sys.exit(1)


exchange = init_exchange()


# ==================== TELEGRAM ====================
def init_telegram():
    if not ENABLE_TELEGRAM or not TELEGRAM_BOT_TOKEN:
        logger.info("Telegram отключён или токен не задан")
        return None
    try:
        bot = telebot.TeleBot(TELEGRAM_BOT_TOKEN)
        bot.get_me()
        filters_status = []
        if ENABLE_MULTI_TIMEFRAME_FILTER:
            filters_status.append("📈 Мультитаймфрейм (1H)")
        if ENABLE_ATR_FILTER:
            filters_status.append(f"📐 ATR (>{ATR_THRESHOLD}*ATR)")
        if ENABLE_VOLUME_SPIKE_IMPROVED:
            filters_status.append(f"📊 Объёмный спайк (>x{VOLUME_SPIKE_COEFF})")
        if ENABLE_LOW_VOLUME_FILTER:
            filters_status.append(f"🔽 Мин. объём свечи (>{MIN_LAST_VOLUME_RATIO}×средн)")
        filters_text = "\n".join(filters_status) if filters_status else "❌ Фильтры отключены"

        test = (f"🚀 <b>Madrid Ribbon + Level Strategies Screener v6.2</b>\n"
                f"Таймфрейм Madrid: <code>{TIMEFRAME}</code>\n"
                f"MA: <code>{'EMA' if USE_EXP_MA else 'SMA'}</code>\n"
                f"Объёмные сигналы: <code>{'вкл' if ENABLE_VOLUME_SPIKE else 'выкл'}</code>\n"
                f"Стратегии уровней (1H): <code>{'вкл' if ENABLE_LEVEL_STRATEGIES else 'выкл'}</code>\n"
                f"<b>Активные фильтры:</b>\n{filters_text}")
        bot.send_message(TELEGRAM_CHANNEL_ID, test, parse_mode='HTML', timeout=30)
        logger.info(f"Telegram канал: {TELEGRAM_CHANNEL_ID}")
        return bot
    except Exception as e:
        logger.error(f"Ошибка Telegram: {e}")
        return None


bot = init_telegram() if ENABLE_TELEGRAM else None


# ==================== WEBSOCKET СЕРВЕР ====================
async def ws_handler(websocket):
    connected_clients.add(websocket)
    try:
        async for message in websocket:
            pass
    except websockets.exceptions.ConnectionClosed:
        pass
    finally:
        connected_clients.remove(websocket)

async def broadcast_signal(signal):
    if connected_clients:
        message = json.dumps(signal, default=str)
        await asyncio.gather(*[client.send(message) for client in connected_clients], return_exceptions=True)

def notify_signal(signal):
    """Вызывается из синхронного кода для отправки сигнала через WebSocket"""
    try:
        asyncio.run_coroutine_threadsafe(broadcast_signal(signal), asyncio.get_running_loop())
    except RuntimeError:
        # Если нет запущенного event loop (например, при инициализации), игнорируем
        pass


# ==================== ФУНКЦИИ ГРАФИКОВ ====================
def plot_candlestick(ax, df, width=0.6, volume_spike_indices=None):
    for i, (idx, row) in enumerate(df.iterrows()):
        color = 'green' if row['close'] >= row['open'] else 'red'
        edgecolor = 'yellow' if volume_spike_indices and i in volume_spike_indices else 'black'
        linewidth = 2 if volume_spike_indices and i in volume_spike_indices else 0.5

        body_bottom = min(row['open'], row['close'])
        body_top = max(row['open'], row['close'])
        ax.bar(i, body_top - body_bottom, width, bottom=body_bottom, color=color, edgecolor=edgecolor, linewidth=linewidth)
        ax.plot([i, i], [row['low'], body_bottom], color='black', linewidth=0.8)
        ax.plot([i, i], [body_top, row['high']], color='black', linewidth=0.8)
    ax.set_xticks(range(0, len(df), max(1, len(df) // 10)))
    ax.set_xticklabels([df.index[j].strftime('%H:%M') for j in range(0, len(df), max(1, len(df) // 10))], rotation=45)

def plot_ribbon_chart(df: pd.DataFrame, signal: dict, filename: str) -> str:
    ribbon = MadridMovingAverageRibbon(use_exp=USE_EXP_MA)
    results = ribbon.calculate(df['close'].values)

    fig, ax = plt.subplots(figsize=(10, 6))

    volume_spike_indices = None
    if 'spike_ratio' in signal and signal['spike_ratio'] is not None:
        volume_spike_indices = [len(df)-1]

    plot_candlestick(ax, df, volume_spike_indices=volume_spike_indices)

    for period in ribbon.periods:
        ma = results[f'ma_{period}']
        colors = results[f'ma_{period}_color']
        lw = ribbon.line_widths.get(period, 1)
        for j in range(len(ma) - 1):
            if not np.isnan(ma[j]) and not np.isnan(ma[j + 1]) and colors[j] != ribbon.COLORS['GRAY']:
                ax.plot([j, j + 1], [ma[j], ma[j + 1]], color=colors[j], linewidth=lw, alpha=0.8)

    last_idx = len(df) - 1
    sig_type = signal['type']
    marker_map = {
        'BULL': ('^', 'green', 'RIBON ПОКУПКА'),
        'BEAR': ('v', 'red', 'RIBON ПРОДАЖА'),
        'WARNING_BULL': ('s', 'orange', 'RIBОН ПРЕДУПР. ПОКУПКА'),
        'WARNING_BEAR': ('s', 'orange', 'RIBОН ПРЕДУПР. ПРОДАЖА'),
        'WARNING_BULL_STRONG': ('D', 'lime', 'RIBОН УСИЛЕНИЕ БЫЧЬЕГО'),
        'WARNING_BEAR_STRONG': ('D', 'red', 'RIBОН УСИЛЕНИЕ МЕДВЕЖЬЕГО'),
        'VOLUME_SPIKE_BULL': ('*', 'gold', 'ВСПЛЕСК ОБЪЁМА (бычий)'),
        'VOLUME_SPIKE_BEAR': ('*', 'orange', 'ВСПЛЕСК ОБЪЁМА (медвежий)'),
    }
    marker, mcolor, label = marker_map.get(sig_type, ('o', 'gray', 'СИГНАЛ'))
    ax.scatter(last_idx, signal['price'], marker=marker, s=200, color=mcolor,
               edgecolor='black', zorder=10, label=label)

    ax.set_title(f"Madrid Ribbon – {signal['symbol']} ({TIMEFRAME})", fontsize=14)
    ax.set_ylabel('Price')
    ax.legend(loc='upper left')
    ax.grid(True, alpha=0.2)
    plt.tight_layout()
    plt.savefig(filename, dpi=80, bbox_inches='tight')
    plt.close(fig)
    return filename

def plot_level_chart(df: pd.DataFrame, signal: dict, levels: list, filename: str) -> str:
    fig, (ax, ax_vol) = plt.subplots(2, 1, figsize=(12, 8), gridspec_kw={'height_ratios': [3, 1]})

    volume_spike_indices = None
    if 'volume_ratio' in signal and signal['volume_ratio'] is not None:
        volume_spike_indices = [len(df)-1]

    plot_candlestick(ax, df, volume_spike_indices=volume_spike_indices)

    for lvl in levels:
        price = lvl['price']
        ltype = lvl['type']
        strength = lvl['strength']
        if ltype == 'support':
            color = 'green'
            linestyle = '--'
            alpha = 0.5 + 0.1 * min(strength, 5)
        elif ltype == 'resistance':
            color = 'red'
            linestyle = '--'
            alpha = 0.5 + 0.1 * min(strength, 5)
        else:
            color = 'blue'
            linestyle = ':'
            alpha = 0.4
        ax.axhline(y=price, color=color, linestyle=linestyle, linewidth=1, alpha=alpha)

    last_idx = len(df) - 1
    sig_type = signal['type']
    marker_map = {
        'LEVEL_BREAKOUT_BULL': ('^', 'blue', 'ПРОБОЙ УРОВНЯ (БЫЧИЙ)'),
        'LEVEL_BREAKOUT_BEAR': ('v', 'blue', 'ПРОБОЙ УРОВНЯ (МЕДВЕЖИЙ)'),
        'LEVEL_FAKEOUT_BULL': ('s', 'purple', 'ЛОЖНЫЙ ПРОБОЙ (БЫЧИЙ)'),
        'LEVEL_FAKEOUT_BEAR': ('s', 'purple', 'ЛОЖНЫЙ ПРОБОЙ (МЕДВЕЖИЙ)'),
        'LEVEL_APPROACH_BULL': ('D', 'cyan', 'ПОДХОД К УРОВНЮ (БЫЧИЙ)'),
        'LEVEL_APPROACH_BEAR': ('D', 'cyan', 'ПОДХОД К УРОВНЮ (МЕДВЕЖИЙ)'),
    }
    marker, mcolor, label = marker_map.get(sig_type, ('o', 'gray', 'СИГНАЛ'))
    ax.scatter(last_idx, signal['price'], marker=marker, s=200, color=mcolor,
               edgecolor='black', zorder=10, label=label)

    ax.set_title(f"Уровни поддержки/сопротивления – {signal['symbol']} ({TIMEFRAME})", fontsize=14)
    ax.set_ylabel('Price')
    ax.legend(loc='upper left')
    ax.grid(True, alpha=0.2)

    colors_vol = ['green' if df['close'].iloc[i] >= df['open'].iloc[i] else 'red' for i in range(len(df))]
    ax_vol.bar(range(len(df)), df['volume'], color=colors_vol, alpha=0.6)
    ax_vol.set_ylabel('Volume')
    ax_vol.set_xlabel('Candle')
    ax_vol.grid(True, alpha=0.2)

    if volume_spike_indices:
        for idx in volume_spike_indices:
            ax_vol.patches[idx].set_edgecolor('yellow')
            ax_vol.patches[idx].set_linewidth(2)

    plt.tight_layout()
    plt.savefig(filename, dpi=80, bbox_inches='tight')
    plt.close(fig)
    return filename


# ==================== ПОЛУЧЕНИЕ ДАННЫХ ====================
def fetch_all_futures_pairs():
    try:
        tickers = exchange.fapiPublicGetTicker24hr()
        pairs = []
        for t in tickers:
            sym = t['symbol']
            if sym.endswith('USDT'):
                vol = float(t['quoteVolume'])
                trades = int(t['count'])
                change = float(t['priceChangePercent'])
                if vol >= MIN_VOLUME_24H_USDT and trades >= MIN_TRADES_24H and abs(change) >= MIN_PRICE_CHANGE_24H:
                    ccxt_sym = f"{sym.replace('USDT', '')}/USDT:USDT"
                    pairs.append({
                        'symbol': ccxt_sym,
                        'binance_symbol': sym,
                        'volume_24h': vol,
                        'trades_24h': trades,
                        'change_24h': change,
                        'formatted_volume': format_large_number(vol),
                        'formatted_trades': format_large_number(trades)
                    })
        pairs.sort(key=lambda x: x['volume_24h'], reverse=True)
        selected = pairs[:MAX_PAIRS_TO_ANALYZE]
        logger.info(f"Найдено {len(pairs)} пар, отобрано {len(selected)}")
        return selected
    except Exception as e:
        logger.error(f"Ошибка получения пар: {e}")
        return []

def fetch_ohlcv(symbol, timeframe, limit=200):
    try:
        time.sleep(0.05)  # небольшая задержка для соблюдения лимитов
        ohlcv = exchange.fetch_ohlcv(symbol, timeframe, limit=limit)
        if not ohlcv or len(ohlcv) < 100:
            return None
        df = pd.DataFrame(ohlcv, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
        for col in ['open', 'high', 'low', 'close', 'volume']:
            df[col] = pd.to_numeric(df[col], errors='coerce')
        df.dropna(inplace=True)
        df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
        df.set_index('timestamp', inplace=True)
        return df if len(df) >= 100 else None
    except Exception:
        return None

def check_volume_spike(df):
    if not ENABLE_VOLUME_SPIKE or len(df) < VOLUME_PERIOD + 5:
        return None, None, None

    last_volume = df['volume'].iloc[-1]
    recent_volumes = df['volume'].iloc[-(VOLUME_PERIOD+1):-1]
    if len(recent_volumes) < VOLUME_PERIOD:
        return None, None, None

    mean_vol = recent_volumes.mean()
    std_vol = recent_volumes.std()
    if std_vol == 0:
        return None, None, None

    spike_ratio = (last_volume - mean_vol) / std_vol
    price_change_5m = (df['close'].iloc[-1] - df['close'].iloc[-2]) / df['close'].iloc[-2] * 100

    if spike_ratio > VOLUME_SPIKE_THRESHOLD and abs(price_change_5m) >= MIN_PRICE_CHANGE_5M:
        signal_type = 'VOLUME_SPIKE_BULL' if price_change_5m > 0 else 'VOLUME_SPIKE_BEAR'
        return signal_type, spike_ratio, price_change_5m

    return None, spike_ratio, price_change_5m


# ==================== АНАЛИЗ ПАРЫ ====================
level_analyzer = LevelAnalyzer(exchange) if ENABLE_LEVEL_STRATEGIES else None

def analyze_pair(symbol, pair_info=None, df_5m=None):
    if df_5m is None:
        df_5m = fetch_ohlcv(symbol, TIMEFRAME)
        if df_5m is None:
            return None

    trend_h1 = None
    if ENABLE_MULTI_TIMEFRAME_FILTER:
        trend_h1 = get_trend_h1(symbol)

    atr_value = None
    if ENABLE_ATR_FILTER:
        atr_value = compute_atr(df_5m)

    price_move = abs(df_5m['close'].iloc[-1] - df_5m['close'].iloc[-2])

    if ENABLE_LOW_VOLUME_FILTER:
        last_vol = df_5m['volume'].iloc[-1]
        avg_vol_10 = df_5m['volume'].iloc[-10:].mean()
        if avg_vol_10 == 0 or last_vol < avg_vol_10 * MIN_LAST_VOLUME_RATIO:
            return None

    signals_to_send = []

    # --- 1. Аномальный объём ---
    spike_signal = None
    spike_ratio = None
    price_change_5m = None
    if ENABLE_VOLUME_SPIKE:
        if ENABLE_VOLUME_SPIKE_IMPROVED:
            spike_signal, spike_ratio, price_change_5m = check_volume_spike_improved(df_5m)
        else:
            spike_signal, spike_ratio, price_change_5m = check_volume_spike(df_5m)

        if spike_signal:
            volume_signal = {
                'strategy': 'ribbon',
                'type': spike_signal,
                'symbol': symbol.replace('/USDT:USDT', '').replace('USDT', ''),
                'price': df_5m['close'].iloc[-1],
                'timestamp': datetime.now().strftime('%H:%M:%S'),
                'spike_ratio': spike_ratio,
                'price_change_5m': price_change_5m,
            }
            if pair_info:
                volume_signal.update({
                    'volume_24h': pair_info['volume_24h'],
                    'trades_24h': pair_info['trades_24h'],
                    'formatted_volume': pair_info['formatted_volume'],
                    'formatted_trades': pair_info['formatted_trades'],
                    'change_24h': pair_info['change_24h']
                })
            signals_to_send.append(volume_signal)

    # --- 2. Madrid Ribbon ---
    ribbon = MadridMovingAverageRibbon(use_exp=USE_EXP_MA)
    results = ribbon.calculate(df_5m['close'].values)
    rib_signals = ribbon.get_enhanced_signals(results)

    last_sig = rib_signals['signals'][-1]
    sig_type = None
    if last_sig == ribbon.BULL:
        sig_type = 'BULL'
    elif last_sig == ribbon.BEAR:
        sig_type = 'BEAR'
    elif last_sig == ribbon.WARNING_BULL:
        sig_type = 'WARNING_BULL'
    elif last_sig == ribbon.WARNING_BEAR:
        sig_type = 'WARNING_BEAR'
    elif last_sig == ribbon.WARNING_BULL_STRONG:
        sig_type = 'WARNING_BULL_STRONG'
    elif last_sig == ribbon.WARNING_BEAR_STRONG:
        sig_type = 'WARNING_BEAR_STRONG'

    if sig_type:
        if ENABLE_MULTI_TIMEFRAME_FILTER and trend_h1 is not None:
            if trend_h1 == 'bull' and sig_type in ['BEAR', 'WARNING_BEAR', 'WARNING_BEAR_STRONG']:
                return signals_to_send if signals_to_send else None
            if trend_h1 == 'bear' and sig_type in ['BULL', 'WARNING_BULL', 'WARNING_BULL_STRONG']:
                return signals_to_send if signals_to_send else None

        if ENABLE_ATR_FILTER and atr_value is not None:
            if price_move < ATR_THRESHOLD * atr_value:
                return signals_to_send if signals_to_send else None

        base_signal = {
            'strategy': 'ribbon',
            'type': sig_type,
            'symbol': symbol.replace('/USDT:USDT', '').replace('USDT', ''),
            'price': df_5m['close'].iloc[-1],
            'timestamp': datetime.now().strftime('%H:%M:%S'),
            'ma5': results['ma_5'][-1],
            'ma100': results['ma_100'][-1],
            'signal_color': rib_signals['signal_colors'][-1],
        }
        if pair_info:
            base_signal.update({
                'volume_24h': pair_info['volume_24h'],
                'trades_24h': pair_info['trades_24h'],
                'formatted_volume': pair_info['formatted_volume'],
                'formatted_trades': pair_info['formatted_trades'],
                'change_24h': pair_info['change_24h']
            })
        if spike_ratio is not None:
            base_signal['spike_ratio'] = spike_ratio
            base_signal['price_change_5m'] = price_change_5m

        signals_to_send.append(base_signal)

    # --- 3. Уровни ---
    if ENABLE_LEVEL_STRATEGIES and level_analyzer:
        levels = level_analyzer.calculate_levels(symbol)
        if levels:
            current_price = df_5m['close'].iloc[-1]
            level_events = level_analyzer.check_level_events(symbol, df_5m, levels, current_price)
            for ev in level_events:
                if ENABLE_MULTI_TIMEFRAME_FILTER and trend_h1 is not None:
                    if 'BULL' in ev['type'] and trend_h1 == 'bear':
                        continue
                    if 'BEAR' in ev['type'] and trend_h1 == 'bull':
                        continue
                if ENABLE_ATR_FILTER and atr_value is not None:
                    if price_move < ATR_THRESHOLD * atr_value:
                        continue

                level_signal = {
                    'strategy': 'level',
                    'type': ev['type'],
                    'symbol': symbol.replace('/USDT:USDT', '').replace('USDT', ''),
                    'price': current_price,
                    'timestamp': datetime.now().strftime('%H:%M:%S'),
                    'level_price': ev['level_price'],
                    'level_strength': ev['level_strength'],
                    'distance_percent': ev['distance_percent'],
                    'all_levels': levels,
                }
                if 'volume_ratio' in ev:
                    level_signal['volume_ratio'] = ev['volume_ratio']
                if pair_info:
                    level_signal.update({
                        'volume_24h': pair_info['volume_24h'],
                        'trades_24h': pair_info['trades_24h'],
                        'formatted_volume': pair_info['formatted_volume'],
                        'formatted_trades': pair_info['formatted_trades'],
                        'change_24h': pair_info['change_24h']
                    })
                signals_to_send.append(level_signal)

    return signals_to_send if signals_to_send else None


# ==================== ОТПРАВКА В TELEGRAM ====================
def send_telegram_signal(signal, chart_file=None, max_retries=3):
    if not bot:
        return False

    if signal.get('strategy') == 'ribbon':
        type_map = {
            'BULL': ('🚀', '<b>RIBON СИГНАЛ НА ПОКУПКУ</b>', '🟢'),
            'BEAR': ('🔻', '<b>RIBON СИГНАЛ НА ПРОДАЖУ</b>', '🔴'),
            'WARNING_BULL': ('⚠️🟢', '<b>RIBON ПРЕДУПРЕЖДЕНИЕ (покупка)</b>', '🟡'),
            'WARNING_BEAR': ('⚠️🔴', '<b>RIBON ПРЕДУПРЕЖДЕНИЕ (продажа)</b>', '🟡'),
            'WARNING_BULL_STRONG': ('✅🟢', '<b>RIBON УСИЛЕНИЕ БЫЧЬЕГО ТРЕНДА</b>', '🟢'),
            'WARNING_BEAR_STRONG': ('✅🔴', '<b>RIBON УСИЛЕНИЕ МЕДВЕЖЬЕГО ТРЕНДА</b>', '🔴'),
            'VOLUME_SPIKE_BULL': ('📈💥', '<b>АНОМАЛЬНЫЙ ОБЪЁМ (бычий)</b>', '🟢'),
            'VOLUME_SPIKE_BEAR': ('📉💥', '<b>АНОМАЛЬНЫЙ ОБЪЁМ (медвежий)</b>', '🔴'),
        }
    else:
        type_map = {
            'LEVEL_BREAKOUT_BULL': ('📈🧱', '<b>ПРОБОЙ УРОВНЯ (бычий)</b>', '🟢'),
            'LEVEL_BREAKOUT_BEAR': ('📉🧱', '<b>ПРОБОЙ УРОВНЯ (медвежий)</b>', '🔴'),
            'LEVEL_FAKEOUT_BULL': ('🎭🟢', '<b>ЛОЖНЫЙ ПРОБОЙ (бычий)</b>', '🟡'),
            'LEVEL_FAKEOUT_BEAR': ('🎭🔴', '<b>ЛОЖНЫЙ ПРОБОЙ (медвежий)</b>', '🟡'),
            'LEVEL_APPROACH_BULL': ('🎯🟢', '<b>ПОДХОД К УРОВНЮ (бычий)</b>', '🔵'),
            'LEVEL_APPROACH_BEAR': ('🎯🔴', '<b>ПОДХОД К УРОВНЮ (медвежий)</b>', '🔵'),
        }

    emoji, title, color = type_map.get(signal['type'], ('', '<b>СИГНАЛ</b>', ''))

    def escape_html(text):
        if text is None:
            return ''
        return str(text).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')

    symbol_esc = escape_html(signal['symbol'])
    price_esc = escape_html(f"{signal['price']:.6f}")
    timestamp_esc = escape_html(signal['timestamp'])

    message = f"{emoji} {title}\n"
    message += f"{color} <b>{symbol_esc}</b> | TF: <code>{TIMEFRAME}</code>\n\n"
    message += f"💰 <b>Цена:</b> <code>{price_esc}</code>\n"

    if signal.get('strategy') == 'ribbon':
        if 'ma5' in signal:
            ma5_esc = escape_html(f"{signal['ma5']:.6f}")
            message += f"📊 <b>MA5:</b> <code>{ma5_esc}</code>\n"
        if 'ma100' in signal:
            ma100_esc = escape_html(f"{signal['ma100']:.6f}")
            message += f"📉 <b>MA100:</b> <code>{ma100_esc}</code>\n"
    else:
        if 'level_price' in signal:
            level_esc = escape_html(f"{signal['level_price']:.6f}")
            message += f"🧱 <b>Уровень:</b> <code>{level_esc}</code>\n"
        if 'level_strength' in signal:
            message += f"⚡ <b>Сила уровня:</b> <code>{escape_html(str(signal['level_strength']))}</code>\n"
        if 'distance_percent' in signal:
            message += f"📐 <b>Расстояние:</b> <code>{escape_html(f'{signal['distance_percent']:.2f}%')}</code>\n"
        if 'volume_ratio' in signal:
            message += f"📊 <b>Объём на пробое:</b> <code>{escape_html(f'{signal['volume_ratio']:.2f}x')}</code>\n"

    if 'price_change_5m' in signal:
        arrow = '📈' if signal['price_change_5m'] > 0 else '📉'
        message += f"{arrow} <b>Изменение цены за 5м:</b> <code>{escape_html(f'{signal['price_change_5m']:.2f}%')}</code>\n"
    if 'spike_ratio' in signal:
        message += f"📊 <b>Аномалия объёма:</b> <code>{escape_html(f'{signal['spike_ratio']:.2f}')}</code>\n"

    if 'formatted_volume' in signal:
        message += f"📈 <b>Объём 24h:</b> <code>{escape_html(signal['formatted_volume'])}</code>\n"
    if 'formatted_trades' in signal:
        message += f"🔄 <b>Сделки 24h:</b> <code>{escape_html(signal['formatted_trades'])}</code>\n"
    if 'change_24h' in signal:
        chg = signal['change_24h']
        arrow = '📈' if chg > 0 else '📉'
        message += f"{arrow} <b>Изменение 24h:</b> <code>{escape_html(f'{abs(chg):.2f}%')}</code>\n"

    message += f"🕒 <b>Время:</b> <code>{timestamp_esc}</code>\n\n"
    message += f"#MadridRibbon #{signal['symbol']} #Binance"

    for attempt in range(max_retries):
        try:
            if chart_file and os.path.exists(chart_file):
                with open(chart_file, 'rb') as photo:
                    bot.send_photo(
                        TELEGRAM_CHANNEL_ID,
                        photo,
                        caption=message,
                        parse_mode='HTML',
                        timeout=30
                    )
                os.remove(chart_file)
            else:
                bot.send_message(
                    TELEGRAM_CHANNEL_ID,
                    message,
                    parse_mode='HTML',
                    disable_web_page_preview=True,
                    timeout=30
                )
            logger.info(f"Отправлен {signal['strategy']} {signal['type']}: {signal['symbol']}")
            return True
        except Exception as e:
            logger.warning(f"Попытка {attempt + 1}/{max_retries} не удалась: {e}")
            if attempt < max_retries - 1:
                time.sleep(2 ** attempt)
            else:
                logger.error(f"Не удалось отправить после {max_retries} попыток")
    return False


# ==================== СКАНИРОВАНИЕ ====================
def run_scan():
    print(f"\n{'=' * 80}")
    print(f"СКАНИРОВАНИЕ | {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print('=' * 80)

    pairs = fetch_all_futures_pairs()
    if not pairs:
        print("❌ Нет пар")
        return (0,0,0,0,0,0,0,0,0,0,0,0,0,0)

    rib_bull = rib_bear = rib_wbull = rib_wbear = rib_strong_bull = rib_strong_bear = 0
    vol_bull = vol_bear = 0
    lev_break_bull = lev_break_bear = lev_fake_bull = lev_fake_bear = lev_appr_bull = lev_appr_bear = 0

    print(f"Анализируем {len(pairs)} пар...")

    for i, pinfo in enumerate(pairs, 1):
        try:
            prog = (i / len(pairs)) * 100
            short = pinfo['symbol'].replace('/USDT:USDT', '')[:12]
            vol = pinfo['formatted_volume']
            print(f"Прогресс: {prog:.1f}% | {i}/{len(pairs)} | {short:<12} | Объём: {vol:<10}", end='\r')

            df_5m = fetch_ohlcv(pinfo['symbol'], TIMEFRAME, 150)
            if df_5m is None:
                continue

            signals = analyze_pair(pinfo['symbol'], pinfo, df_5m)
            if signals:
                for sig in signals:
                    chart = None
                    if SEND_CHART and bot:
                        with tempfile.NamedTemporaryFile(suffix='.png', delete=False) as tmp:
                            chart = tmp.name
                        if sig['strategy'] == 'ribbon':
                            plot_ribbon_chart(df_5m, sig, chart)
                        else:
                            plot_level_chart(df_5m, sig, sig['all_levels'], chart)

                    notify_signal(sig)

                    if bot:
                        send_telegram_signal(sig, chart)
                    elif chart and os.path.exists(chart):
                        os.remove(chart)

                    if sig['strategy'] == 'ribbon':
                        if sig['type'] == 'BULL':
                            rib_bull += 1
                        elif sig['type'] == 'BEAR':
                            rib_bear += 1
                        elif sig['type'] == 'WARNING_BULL':
                            rib_wbull += 1
                        elif sig['type'] == 'WARNING_BEAR':
                            rib_wbear += 1
                        elif sig['type'] == 'WARNING_BULL_STRONG':
                            rib_strong_bull += 1
                        elif sig['type'] == 'WARNING_BEAR_STRONG':
                            rib_strong_bear += 1
                        elif sig['type'] == 'VOLUME_SPIKE_BULL':
                            vol_bull += 1
                        elif sig['type'] == 'VOLUME_SPIKE_BEAR':
                            vol_bear += 1
                    else:
                        if sig['type'] == 'LEVEL_BREAKOUT_BULL':
                            lev_break_bull += 1
                        elif sig['type'] == 'LEVEL_BREAKOUT_BEAR':
                            lev_break_bear += 1
                        elif sig['type'] == 'LEVEL_FAKEOUT_BULL':
                            lev_fake_bull += 1
                        elif sig['type'] == 'LEVEL_FAKEOUT_BEAR':
                            lev_fake_bear += 1
                        elif sig['type'] == 'LEVEL_APPROACH_BULL':
                            lev_appr_bull += 1
                        elif sig['type'] == 'LEVEL_APPROACH_BEAR':
                            lev_appr_bear += 1

                    print(f"\n{sig['strategy'].upper()} {sig['type']}: {sig['symbol']} @ {sig['price']:.6f}")

            # Небольшая задержка между запросами
            time.sleep(0.1)

        except KeyboardInterrupt:
            raise
        except Exception as e:
            logger.error(f"Ошибка при анализе {pinfo['symbol']}: {e}")
            continue

    print(f"\n{'=' * 80}")
    return (rib_bull, rib_bear, rib_wbull, rib_wbear, rib_strong_bull, rib_strong_bear,
            vol_bull, vol_bear,
            lev_break_bull, lev_break_bear, lev_fake_bull, lev_fake_bear, lev_appr_bull, lev_appr_bear)


# ==================== АСИНХРОННЫЙ ЗАПУСК СКАНЕРА ====================
async def scanner_loop():
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)
    loop = asyncio.get_running_loop()
    scan_count = 0
    total = {
        'rib_bull': 0, 'rib_bear': 0, 'rib_wbull': 0, 'rib_wbear': 0,
        'rib_strong_bull': 0, 'rib_strong_bear': 0,
        'vol_bull': 0, 'vol_bear': 0,
        'lev_break_bull': 0, 'lev_break_bear': 0,
        'lev_fake_bull': 0, 'lev_fake_bear': 0,
        'lev_appr_bull': 0, 'lev_appr_bear': 0,
    }

    while True:
        scan_count += 1
        print(f"\n🌀 Цикл #{scan_count}")

        # Запускаем синхронный run_scan в потоке
        (rb, rbe, rwb, rwr, rsb, rsr, vb, vr,
         lbb, lbr, lfb, lfr, lab, lar) = await loop.run_in_executor(executor, run_scan)

        total['rib_bull'] += rb
        total['rib_bear'] += rbe
        total['rib_wbull'] += rwb
        total['rib_wbear'] += rwr
        total['rib_strong_bull'] += rsb
        total['rib_strong_bear'] += rsr
        total['vol_bull'] += vb
        total['vol_bear'] += vr
        total['lev_break_bull'] += lbb
        total['lev_break_bear'] += lbr
        total['lev_fake_bull'] += lfb
        total['lev_fake_bear'] += lfr
        total['lev_appr_bull'] += lab
        total['lev_appr_bear'] += lar

        print(f"ИТОГИ ЦИКЛА:")
        print(f"  RIBON: BULL={rb} BEAR={rbe} WARN_B={rwb} WARN_S={rwr} STRONG_B={rsb} STRONG_S={rsr}")
        print(f"  VOLUME SPIKE: BULL={vb} BEAR={vr}")
        print(f"  LEVELS: BREAK_B={lbb} BREAK_S={lbr} FAKE_B={lfb} FAKE_S={lfr} APPROACH_B={lab} APPROACH_S={lar}")
        print(f"ВСЕГО ЗА ВСЕ ЦИКЛЫ:")
        print(f"  RIBON BULL: {total['rib_bull']} | BEAR: {total['rib_bear']}")
        print(f"  RIBON WARN BULL: {total['rib_wbull']} | WARN BEAR: {total['rib_wbear']}")
        print(f"  RIBON STRONG BULL: {total['rib_strong_bull']} | STRONG BEAR: {total['rib_strong_bear']}")
        print(f"  VOLUME BULL: {total['vol_bull']} | BEAR: {total['vol_bear']}")
        print(f"  LEVEL BREAKOUT BULL: {total['lev_break_bull']} | BEAR: {total['lev_break_bear']}")
        print(f"  LEVEL FAKEOUT BULL: {total['lev_fake_bull']} | BEAR: {total['lev_fake_bear']}")
        print(f"  LEVEL APPROACH BULL: {total['lev_appr_bull']} | BEAR: {total['lev_appr_bear']}")

        print(f"⏳ Ожидание {SCAN_INTERVAL} мин...")
        for sec in range(SCAN_INTERVAL * 60, 0, -1):
            m, s = divmod(sec, 60)
            print(f"⏰ До следующего сканирования: {m:02d}:{s:02d}", end='\r')
            await asyncio.sleep(1)
        print()


# ==================== HEALTH CHECK ====================
async def health_check(path, request_headers):
    if path == "/healthz":
        return websockets.http.Response(200, "OK", [])


# ==================== ГЛАВНАЯ АСИНХРОННАЯ ФУНКЦИЯ ====================
async def main():
    loop = asyncio.get_running_loop()
    stop = loop.create_future()
    loop.add_signal_handler(signal.SIGTERM, stop.set_result, None)

    async with websockets.serve(
        ws_handler,
        WS_HOST,
        WS_PORT,
        process_request=health_check
    ) as server:
        print(f"✅ WebSocket сервер запущен на порту {WS_PORT}")
        scan_task = asyncio.create_task(scanner_loop())
        await stop
        print("👋 Получен SIGTERM, завершение...")
        scan_task.cancel()
        await scan_task


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\n🛑 Скринер остановлен пользователем")