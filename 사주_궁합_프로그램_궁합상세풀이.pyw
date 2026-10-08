# -*- coding: utf-8 -*-
"""
사주풀이 · 궁합 프로그램  (v2.2)
================================
이름/생년월일/태어난 시간을 입력하면 사주팔자와 풀이, 궁합을 보여줍니다.

[v2.2 변경: 궁합 풀이를 쉬운 말로 크게 확장 — 총평, 성격 비교, 연애·결혼, 대화·갈등, 재물, 자녀, 가족·집안, 함께 일하기, 생활·건강, 시기별 흐름, 인연의 끈(빠진 글자 안내), 관계별 점수 추가]

[v2.1 변경: 풀이 문장을 쉬운 말로 다시 쓰고, 재물운·자식운·부모/가정운·학업운·인생 시기별 흐름·분야별 별점·궁합의 재물/자녀/가정 풀이 추가]

[v2.0에서 달라진 점]
 - 일주(일지) 계산 오류 수정, 윤달 음력 변환 오류 수정
 - 절기 계산을 정밀 천문 급수(VSOP87)로 교체 (알려진 절기 시각과 1분 이내 일치)
 - 한국 표준시 이력(1908~11 / 1954~61년 UTC+8:30, 서머타임) 자동 보정
 - 진태양시(출생지 경도·균시차) 선택, 출생 도시 선택
 - 지장간·십성 이름·12운성·신살·합충형파해·신강/신약(월령 가중)·용신(억부/조후)
 - 대운·세운(올해 운세), 풀이 문장 대폭 확장
 - 궁합: 천간합·월지·시지·형해원진·오행 보완·용신 보완, 항목별 점수
 - 화면: 사주 카드(한자·오행색), 막대그래프, 접고 펼치는 풀이, HTML/텍스트 저장·복사

외부 설치 없이 파이썬 표준 라이브러리만으로 동작합니다(인터넷 불필요).

※ 참고용 프로그램입니다. 전통 명리학 이론을 바탕으로 한 하나의 해석 방식일 뿐,
  실제 성격·운세·궁합을 과학적으로 단정하는 도구가 아닙니다.
"""
import html as _html
import math
import os
import re
import sys
import tempfile
import traceback
import webbrowser
from datetime import datetime, timedelta, date
from functools import lru_cache
from pathlib import Path

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

APP_TITLE = "사주풀이 · 궁합 프로그램"
APP_VERSION = "2.2"

# =====================================================================
#  기본 표
# =====================================================================
GAN = ["갑", "을", "병", "정", "무", "기", "경", "신", "임", "계"]
JI = ["자", "축", "인", "묘", "진", "사", "오", "미", "신", "유", "술", "해"]
GAN_H = ["甲", "乙", "丙", "丁", "戊", "己", "庚", "辛", "壬", "癸"]
JI_H = ["子", "丑", "寅", "卯", "辰", "巳", "午", "未", "申", "酉", "戌", "亥"]
OHANG_GAN = ["목", "목", "화", "화", "토", "토", "금", "금", "수", "수"]
OHANG_JI = ["수", "토", "목", "목", "토", "화", "화", "토", "금", "금", "토", "수"]
OHANG_LIST = ["목", "화", "토", "금", "수"]
SAENG = {"목": "화", "화": "토", "토": "금", "금": "수", "수": "목"}
GEUK = {"목": "토", "토": "수", "수": "화", "화": "금", "금": "목"}

# 지장간: 지지 속에 숨은 천간 (여기→중기→정기 순, 가중치 합 = 1)
JIJANGGAN = {
    0: [(8, 0.3), (9, 0.7)],
    1: [(9, 0.2), (7, 0.2), (5, 0.6)],
    2: [(4, 0.2), (2, 0.2), (0, 0.6)],
    3: [(0, 0.3), (1, 0.7)],
    4: [(1, 0.2), (9, 0.2), (4, 0.6)],
    5: [(4, 0.2), (6, 0.2), (2, 0.6)],
    6: [(2, 0.2), (5, 0.2), (3, 0.6)],
    7: [(3, 0.2), (1, 0.2), (5, 0.6)],
    8: [(4, 0.2), (8, 0.2), (6, 0.6)],
    9: [(6, 0.3), (7, 0.7)],
    10: [(7, 0.2), (3, 0.2), (4, 0.6)],
    11: [(4, 0.2), (0, 0.2), (8, 0.6)],
}


def main_stem(branch_idx):
    """지지의 정기(본기) 천간 인덱스."""
    return JIJANGGAN[branch_idx][-1][0]


def gapja(index60):
    index60 %= 60
    return GAN[index60 % 10] + JI[index60 % 12]


def gz_index(stem, branch):
    for i in range(60):
        if i % 10 == stem and i % 12 == branch:
            return i
    raise ValueError("잘못된 간지 조합")


# =====================================================================
#  날짜/시각 변환, ΔT
# =====================================================================
K9 = timedelta(hours=9)


def jd_from_utc(d):
    """UTC 기준 naive datetime → 율리우스일(JD)."""
    y, m = d.year, d.month
    dd = d.day + d.hour / 24.0 + d.minute / 1440.0 + d.second / 86400.0
    if m <= 2:
        y -= 1
        m += 12
    a = y // 100
    b = 2 - a + a // 4
    return int(365.25 * (y + 4716)) + int(30.6001 * (m + 1)) + dd + b - 1524.5


def utc_from_jd(jd):
    jd2 = jd + 0.5
    z = int(jd2)
    f = jd2 - z
    if z < 2299161:
        a = z
    else:
        alpha = int((z - 1867216.25) / 36524.25)
        a = z + 1 + alpha - alpha // 4
    b = a + 1524
    c = int((b - 122.1) / 365.25)
    d = int(365.25 * c)
    e = int((b - d) / 30.6001)
    day = b - d - int(30.6001 * e) + f
    month = e - 1 if e < 14 else e - 13
    year = c - 4716 if month > 2 else c - 4715
    di = int(day)
    return datetime(year, month, di) + timedelta(seconds=round((day - di) * 86400))


def kst_from_jd(jd):
    return utc_from_jd(jd) + K9


def jdn_of_date(d):
    """그레고리력 날짜 → 율리우스 일수(정수, 정오 기준)."""
    a = (14 - d.month) // 12
    y = d.year + 4800 - a
    m = d.month + 12 * a - 3
    return d.day + (153 * m + 2) // 5 + 365 * y + y // 4 - y // 100 + y // 400 - 32045


def delta_t_seconds(year):
    """ΔT = TT − UT (초). Espenak & Meeus 근사식(1900~2100)."""
    y = year
    if y < 1920:
        t = y - 1900
        return -2.79 + 1.494119 * t - 0.0598939 * t ** 2 + 0.0061966 * t ** 3 - 0.000197 * t ** 4
    if y < 1941:
        t = y - 1920
        return 21.20 + 0.84493 * t - 0.076100 * t ** 2 + 0.0020936 * t ** 3
    if y < 1961:
        t = y - 1950
        return 29.07 + 0.407 * t - t ** 2 / 233 + t ** 3 / 2547
    if y < 1986:
        t = y - 1975
        return 45.45 + 1.067 * t - t ** 2 / 260 - t ** 3 / 718
    if y < 2005:
        t = y - 2000
        return (63.86 + 0.3345 * t - 0.060374 * t ** 2 + 0.0017275 * t ** 3
                + 0.000651814 * t ** 4 + 0.00002373599 * t ** 5)
    if y < 2050:
        t = y - 2000
        return 62.92 + 0.32217 * t + 0.005589 * t ** 2
    return -20 + 32 * ((y - 1820) / 100) ** 2 - 0.5628 * (2150 - y)


# =====================================================================
#  태양 황경 (VSOP87 지구 궤도 급수) — 절기 계산용
# =====================================================================
_L0 = [(175347046, 0, 0), (3341656, 4.6692568, 6283.0758500), (34894, 4.62610, 12566.15170),
       (3497, 2.7441, 5753.3849), (3418, 2.8289, 3.5231), (3136, 3.6277, 77713.7715),
       (2676, 4.4181, 7860.4194), (2343, 6.1352, 3930.2097), (1324, 0.7425, 11506.7698),
       (1273, 2.0371, 529.6910), (1199, 1.1096, 1577.3435), (990, 5.233, 5884.927),
       (902, 2.045, 26.298), (857, 3.508, 398.149), (780, 1.179, 5223.694),
       (753, 2.533, 5507.553), (505, 4.583, 18849.228), (492, 4.205, 775.523),
       (357, 2.920, 0.067), (317, 5.849, 11790.629), (284, 1.899, 796.298),
       (271, 0.315, 10977.079), (243, 0.345, 5486.778), (206, 4.806, 2544.314),
       (205, 1.869, 5573.143), (202, 2.458, 6069.777), (156, 0.833, 213.299),
       (132, 3.411, 2942.463), (126, 1.083, 20.775), (115, 0.645, 0.980),
       (103, 0.636, 4694.003), (102, 0.976, 15720.839), (102, 4.267, 7.114),
       (99, 6.21, 2146.17), (98, 0.68, 155.42), (86, 5.98, 161000.69),
       (85, 1.30, 6275.96), (85, 3.67, 71430.70), (80, 1.81, 17260.15),
       (79, 3.04, 12036.46), (75, 1.76, 5088.63), (74, 3.50, 3154.69),
       (74, 4.68, 801.82), (70, 0.83, 9437.76), (62, 3.98, 8827.39),
       (61, 1.82, 7084.90), (57, 2.78, 6286.60), (56, 4.39, 14143.50),
       (56, 3.47, 6279.55), (52, 0.19, 12139.55), (52, 1.33, 1748.02),
       (51, 0.28, 5856.48), (49, 0.49, 1194.45), (41, 5.37, 8429.24),
       (41, 2.40, 19651.05), (39, 6.17, 10447.39), (37, 6.04, 10213.29),
       (37, 2.57, 1059.38), (36, 1.71, 2352.87), (36, 1.78, 6812.77),
       (33, 0.59, 17789.85), (30, 0.44, 83996.85), (30, 2.74, 1349.87),
       (25, 3.16, 4690.48)]
_L1 = [(628331966747, 0, 0), (206059, 2.678235, 6283.075850), (4303, 2.6351, 12566.1517),
       (425, 1.590, 3.523), (119, 5.796, 26.298), (109, 2.966, 1577.344),
       (93, 2.59, 18849.23), (72, 1.14, 529.69), (68, 1.87, 398.15), (67, 4.41, 5507.55),
       (59, 2.89, 5223.69), (56, 2.17, 155.42), (45, 0.40, 796.30), (36, 0.47, 775.52),
       (29, 2.65, 7.11), (21, 5.34, 0.98), (19, 1.85, 5486.78), (19, 4.97, 213.30),
       (17, 2.99, 6275.96), (16, 0.03, 2544.31), (16, 1.43, 2146.17),
       (15, 1.21, 10977.08), (12, 2.83, 1748.02), (12, 3.26, 5088.63),
       (12, 5.27, 1194.45), (12, 2.08, 4694.00), (11, 0.77, 553.57),
       (10, 1.30, 6286.60), (10, 4.24, 1349.87), (9, 2.70, 242.73),
       (9, 5.64, 951.72), (8, 5.30, 2352.87), (6, 2.65, 9437.76), (6, 4.67, 4690.48)]
_L2 = [(52919, 0, 0), (8720, 1.0721, 6283.0758), (309, 0.867, 12566.152), (27, 0.05, 3.52),
       (16, 5.19, 26.30), (16, 3.68, 155.42), (10, 0.76, 18849.23), (9, 2.06, 77713.77),
       (7, 0.83, 775.52), (5, 4.66, 1577.34), (4, 1.03, 7.11), (4, 3.44, 5573.14),
       (3, 5.14, 796.30), (3, 6.05, 5507.55), (3, 1.19, 242.73), (3, 6.12, 529.69),
       (3, 0.31, 398.15), (3, 2.28, 553.57), (2, 4.38, 5223.69), (2, 3.75, 0.98)]
_L3 = [(289, 5.844, 6283.076), (35, 0, 0), (17, 5.49, 12566.15), (3, 5.2, 155.42),
       (1, 4.72, 3.52), (1, 5.3, 18849.23), (1, 5.97, 242.73)]
_L4 = [(114, 3.142, 0), (8, 4.13, 6283.08), (1, 3.84, 12566.15)]
_L5 = [(1, 3.14, 0)]


def _vsop_series(series, t):
    return sum(a * math.cos(b + c * t) for a, b, c in series)


def sun_apparent_longitude(jd_ut):
    """태양의 겉보기 황경(도). 입력은 UT 기준 JD."""
    year = 2000 + (jd_ut - 2451545.0) / 365.25
    jde = jd_ut + delta_t_seconds(year) / 86400.0
    t = (jde - 2451545.0) / 365250.0
    big_l = (_vsop_series(_L0, t) + _vsop_series(_L1, t) * t + _vsop_series(_L2, t) * t ** 2
             + _vsop_series(_L3, t) * t ** 3 + _vsop_series(_L4, t) * t ** 4
             + _vsop_series(_L5, t) * t ** 5) / 1e8
    lon = math.degrees(big_l) + 180.0 - 0.09033 / 3600.0
    tc = t * 10.0
    om = math.radians(125.04452 - 1934.136261 * tc)
    ls = math.radians(280.4665 + 36000.7698 * tc)
    lm = math.radians(218.3165 + 481267.8813 * tc)
    dpsi = (-17.20 * math.sin(om) - 1.32 * math.sin(2 * ls)
            - 0.23 * math.sin(2 * lm) + 0.21 * math.sin(2 * om)) / 3600.0
    mm = math.radians(357.52911 + 35999.05029 * tc)
    ecc = 0.016708634 - 0.000042037 * tc
    nu = mm + 2 * ecc * math.sin(mm) + 1.25 * ecc * ecc * math.sin(2 * mm)
    r = 1.000001018 * (1 - ecc * ecc) / (1 + ecc * math.cos(nu))
    lon += dpsi - 20.4898 / 3600.0 / r
    return lon % 360.0


def _ang_diff(a, b):
    return ((a - b + 180.0) % 360.0) - 180.0


# 24절기: 황경 0°부터 15° 간격
TERM_NAMES = ["춘분", "청명", "곡우", "입하", "소만", "망종", "하지", "소서", "대서",
              "입추", "처서", "백로", "추분", "한로", "상강", "입동", "소설", "대설",
              "동지", "소한", "대한", "입춘", "우수", "경칩"]
# 월건을 바꾸는 12절(節): 입춘부터
WOLGEON_JIEQI = ["입춘", "경칩", "청명", "입하", "망종", "소서",
                 "입추", "백로", "한로", "입동", "대설", "소한"]
JUNGGI_NAMES = ["동지", "대한", "우수", "춘분", "곡우", "소만", "하지",
                "대서", "처서", "추분", "상강", "소설"]
_APPROX_MD = {
    "소한": (1, 6), "대한": (1, 20), "입춘": (2, 4), "우수": (2, 19),
    "경칩": (3, 6), "춘분": (3, 21), "청명": (4, 5), "곡우": (4, 20),
    "입하": (5, 6), "소만": (5, 21), "망종": (6, 6), "하지": (6, 21),
    "소서": (7, 7), "대서": (7, 23), "입추": (8, 8), "처서": (8, 23),
    "백로": (9, 8), "추분": (9, 23), "한로": (10, 8), "상강": (10, 23),
    "입동": (11, 7), "소설": (11, 22), "대설": (12, 7), "동지": (12, 22),
}


@lru_cache(maxsize=None)
def term_jd(name, year):
    """해당 연도의 절기 시각(UT 기준 JD)."""
    target = TERM_NAMES.index(name) * 15.0
    m, d = _APPROX_MD[name]
    guess = jd_from_utc(datetime(year, m, d) - K9)
    lo, hi = guess - 12, guess + 12
    if not (_ang_diff(sun_apparent_longitude(lo), target) < 0 < _ang_diff(sun_apparent_longitude(hi), target)):
        lo, hi = guess - 40, guess + 40
    for _ in range(60):
        mid = (lo + hi) / 2.0
        if _ang_diff(sun_apparent_longitude(mid), target) < 0:
            lo = mid
        else:
            hi = mid
        if hi - lo < 1e-7:
            break
    return (lo + hi) / 2.0


def term_kst(name, year):
    """절기 시각(한국 표준시 UTC+9 기준 naive datetime)."""
    return kst_from_jd(term_jd(name, year))


# =====================================================================
#  음력 (삭 + 중기, 날짜 단위 비교)
# =====================================================================
def _new_moon_jde(k):
    t = k / 1236.85
    t2, t3, t4 = t * t, t ** 3, t ** 4
    jde = (2451550.09766 + 29.530588861 * k + 0.00015437 * t2
           - 0.000000150 * t3 + 0.00000000073 * t4)
    e = 1 - 0.002516 * t - 0.0000074 * t2
    m = math.radians((2.5534 + 29.1053567 * k - 0.0000014 * t2 - 0.00000011 * t3) % 360)
    mp = math.radians((201.5643 + 385.81693528 * k + 0.0107582 * t2
                       + 0.00001238 * t3 - 0.000000058 * t4) % 360)
    f = math.radians((160.7108 + 390.67050284 * k - 0.0016118 * t2
                      - 0.00000227 * t3 + 0.000000011 * t4) % 360)
    om = math.radians((124.7746 - 1.56375588 * k + 0.0020672 * t2 + 0.00000215 * t3) % 360)
    corr = (-0.40720 * math.sin(mp) + 0.17241 * e * math.sin(m) + 0.01608 * math.sin(2 * mp)
            + 0.01039 * math.sin(2 * f) + 0.00739 * e * math.sin(mp - m)
            - 0.00514 * e * math.sin(mp + m) + 0.00208 * e * e * math.sin(2 * m)
            - 0.00111 * math.sin(mp - 2 * f) - 0.00057 * math.sin(mp + 2 * f)
            + 0.00056 * e * math.sin(2 * mp + m) - 0.00042 * math.sin(3 * mp)
            + 0.00042 * e * math.sin(m + 2 * f) + 0.00038 * e * math.sin(m - 2 * f)
            - 0.00024 * e * math.sin(2 * mp - m) - 0.00017 * math.sin(om)
            - 0.00007 * math.sin(mp + 2 * m) + 0.00004 * math.sin(2 * mp - 2 * f)
            + 0.00004 * math.sin(3 * m) + 0.00003 * math.sin(mp + m - 2 * f)
            + 0.00003 * math.sin(2 * mp + 2 * f) - 0.00003 * math.sin(mp + m + 2 * f)
            + 0.00003 * math.sin(mp - m + 2 * f) - 0.00002 * math.sin(mp - m - 2 * f)
            - 0.00002 * math.sin(3 * mp + m) + 0.00002 * math.sin(4 * mp))

    def arg(deg_per_k, base):
        return math.radians((base + deg_per_k * k) % 360)

    extra = (0.000325 * math.sin(arg(0.107408, 299.77) - 0.009173 * t2)
             + 0.000165 * math.sin(arg(0.016321, 251.88))
             + 0.000164 * math.sin(arg(26.651886, 251.83))
             + 0.000126 * math.sin(arg(36.412478, 349.42))
             + 0.000110 * math.sin(arg(18.206239, 84.66))
             + 0.000062 * math.sin(arg(53.303771, 141.74))
             + 0.000060 * math.sin(arg(2.453732, 207.14))
             + 0.000056 * math.sin(arg(7.306860, 154.84))
             + 0.000047 * math.sin(arg(27.261239, 34.52))
             + 0.000042 * math.sin(arg(0.121824, 207.19))
             + 0.000040 * math.sin(arg(1.844379, 291.34))
             + 0.000037 * math.sin(arg(24.198154, 161.72))
             + 0.000035 * math.sin(arg(25.513099, 239.56))
             + 0.000023 * math.sin(arg(3.592518, 331.55)))
    return jde + corr + extra


def new_moon_jd_ut(k):
    """삭(朔)의 UT 기준 JD (ΔT 보정 포함)."""
    jde = _new_moon_jde(k)
    year = 2000 + (jde - 2451545.0) / 365.25
    return jde - delta_t_seconds(year) / 86400.0


_ERA_830 = [(datetime(1908, 3, 31, 15, 30), datetime(1911, 12, 31, 15, 30)),
            (datetime(1954, 3, 20, 15, 0), datetime(1961, 8, 9, 15, 30))]


def _kst_date(jd):
    """음력 계산용 '그날의 날짜'. 한국 법정 표준시가 UTC+8:30이던 시기(1908~11, 1954~61)에는
    그 표준시 기준 날짜를 쓴다(서머타임은 음력 날짜에 영향 없음)."""
    u = utc_from_jd(jd)
    for a, b in _ERA_830:
        if a <= u < b:
            return (u + timedelta(hours=8.5)).date()
    return (u + K9).date()


@lru_cache(maxsize=64)
def lunar_table_for_year(year):
    """양력 year년의 날짜들을 포괄하는 음력 달 목록.
    (start, end, 월, 윤달여부) 튜플의 튜플. 동지가 든 달을 11월로 삼고,
    동지 달 사이가 13개월이면 '중기가 없는 첫 달'을 윤달로 둔다."""
    a_ord = date(year - 1, 10, 1).toordinal()
    b_ord = date(year + 2, 1, 31).toordinal()
    start_d, end_d = date.fromordinal(a_ord), date.fromordinal(b_ord)
    jd_a = jd_from_utc(datetime(start_d.year, start_d.month, start_d.day)) - 40
    jd_b = jd_from_utc(datetime(end_d.year, end_d.month, end_d.day)) + 40
    k0 = int((jd_a - 2451550.09766) / 29.530588861) - 2
    k1 = int((jd_b - 2451550.09766) / 29.530588861) + 2
    moons = [new_moon_jd_ut(k) for k in range(k0, k1 + 1)]
    zq = []
    for yy in range(start_d.year - 1, end_d.year + 2):
        for nm in JUNGGI_NAMES:
            zq.append((term_jd(nm, yy), nm))
    zq.sort()
    segs = []
    for i in range(len(moons) - 1):
        a, b = _kst_date(moons[i]), _kst_date(moons[i + 1])
        zin = [n for jd, n in zq if a <= _kst_date(jd) < b]
        segs.append({"start": a, "end": b, "zq": zin, "month": None, "leap": False})
    anchors = [i for i, s in enumerate(segs) if "동지" in s["zq"]]
    if not anchors:
        raise ValueError("음력 계산 범위 오류")
    # 앵커 사이 구간 라벨링
    for ai, a_idx in enumerate(anchors):
        segs[a_idx]["month"] = 11
        if ai + 1 < len(anchors):
            b_idx = anchors[ai + 1]
            n = b_idx - a_idx
            if n not in (12, 13):
                raise ValueError("음력 달 수 계산 오류")
            leap_i = None
            if n == 13:
                leap_i = next((i for i in range(a_idx + 1, b_idx) if not segs[i]["zq"]), None)
                if leap_i is None:
                    leap_i = a_idx + 1
            cur = 11
            for i in range(a_idx + 1, b_idx):
                if i == leap_i:
                    segs[i]["month"], segs[i]["leap"] = cur, True
                else:
                    cur = cur % 12 + 1
                    segs[i]["month"], segs[i]["leap"] = cur, False
        else:
            cur = 11
            for i in range(a_idx + 1, len(segs)):
                cur = cur % 12 + 1
                segs[i]["month"], segs[i]["leap"] = cur, False
    first = anchors[0]
    return tuple((s["start"], s["end"], s["month"], s["leap"]) for s in segs[first:])


def lunar_to_solar(year, month, day, is_leap=False):
    """음력 → 양력 date."""
    table = lunar_table_for_year(year)
    firsts = [i for i, (s, e, m, lp) in enumerate(table) if m == 1 and not lp]
    start_i = next((i for i in firsts if table[i][0].year == year), None)
    if start_i is None:
        raise ValueError(f"음력 {year}년을 계산하지 못했습니다.")
    nxt = [i for i in firsts if i > start_i]
    end_i = nxt[0] if nxt else len(table)
    for i in range(start_i, end_i):
        s, e, m, lp = table[i]
        if m == month and lp == bool(is_leap):
            length = (e - s).days
            if day > length:
                raise ValueError(f"음력 {year}년 {'윤' if is_leap else ''}{month}월은 {length}일까지 있습니다.")
            return s + timedelta(days=day - 1)
    raise ValueError(f"음력 {year}년에는 {'윤' if is_leap else ''}{month}월이 없습니다. 날짜(윤달 여부)를 확인해 주세요.")


def solar_to_lunar(d):
    """양력 date → (음력년, 월, 일, 윤달여부)."""
    table = lunar_table_for_year(d.year)
    cur = None
    for i, (s, e, m, lp) in enumerate(table):
        if s <= d < e:
            cur = i
            break
    if cur is None:
        raise ValueError("음력 변환 범위 오류")
    ly = None
    for i in range(cur, -1, -1):
        s, e, m, lp = table[i]
        if m == 1 and not lp:
            ly = s.year
            break
    s, e, m, lp = table[cur]
    return (ly if ly is not None else d.year - 1), m, (d - s).days + 1, lp


# =====================================================================
#  한국 표준시 이력 (시간대 데이터베이스 기준) / 출생지 / 진태양시
# =====================================================================
_TZ_RAW = [('1899-12-31 00:00:00', 30472), ('1908-03-31 15:32:08', 30600), ('1911-12-31 15:30:00', 32400), ('1948-05-31 15:00:00', 36000), ('1948-09-12 14:00:00', 32400), ('1949-04-02 15:00:00', 36000), ('1949-09-10 14:00:00', 32400), ('1950-03-31 15:00:00', 36000), ('1950-09-09 14:00:00', 32400), ('1951-05-05 15:00:00', 36000), ('1951-09-08 14:00:00', 32400), ('1954-03-20 15:00:00', 30600), ('1955-05-04 15:30:00', 34200), ('1955-09-08 14:30:00', 30600), ('1956-05-19 15:30:00', 34200), ('1956-09-29 14:30:00', 30600), ('1957-05-04 15:30:00', 34200), ('1957-09-21 14:30:00', 30600), ('1958-05-03 15:30:00', 34200), ('1958-09-20 14:30:00', 30600), ('1959-05-02 15:30:00', 34200), ('1959-09-19 14:30:00', 30600), ('1960-04-30 15:30:00', 34200), ('1960-09-17 14:30:00', 30600), ('1961-08-09 15:30:00', 32400), ('1987-05-09 17:00:00', 36000), ('1987-10-10 17:00:00', 32400), ('1988-05-07 17:00:00', 36000), ('1988-10-08 17:00:00', 32400)]
TZ_TABLE = [(datetime.strptime(s, "%Y-%m-%d %H:%M:%S"), off) for s, off in _TZ_RAW]


def korea_offset_seconds(dt_local):
    """시계에 찍힌 한국 시각(dt_local)에 해당하는 당시 UTC 오프셋(초)."""
    best = TZ_TABLE[0][1]
    for start_utc, off in TZ_TABLE:
        if dt_local - timedelta(seconds=off) >= start_utc:
            best = off
    return best


def utc_from_korea_clock(dt_local, use_history=True):
    if not use_history:
        return dt_local - K9
    return dt_local - timedelta(seconds=korea_offset_seconds(dt_local))


def history_note(dt_local):
    """표준시 이력 때문에 시각을 환산했다면 설명 문구, 아니면 None."""
    off = korea_offset_seconds(dt_local)
    if off == 9 * 3600:
        return None
    diff_min = int(round((9 * 3600 - off) / 60.0))
    sign = "+" if diff_min > 0 else "−"
    if off == int(8.5 * 3600):
        why = "당시 한국 표준시가 UTC+8:30이던 시기"
    elif off == int(9.5 * 3600):
        why = "UTC+8:30 표준시에 서머타임이 겹친 시기"
    elif off == 10 * 3600:
        why = "서머타임(일광절약시간) 시행 시기"
    else:
        why = "당시 지방 표준시 적용 시기"
    return f"{why}라서 시계 시각을 현재 한국 표준시(UTC+9) 기준으로 {sign}{abs(diff_min)}분 환산해서 계산했어요."


CITIES = [
    ("서울", 126.98), ("부산", 129.08), ("대구", 128.60), ("인천", 126.70), ("광주", 126.85),
    ("대전", 127.38), ("울산", 129.31), ("세종", 127.29), ("수원", 127.03), ("창원", 128.68),
    ("청주", 127.49), ("전주", 127.15), ("천안", 127.15), ("포항", 129.37), ("제주", 126.53),
    ("춘천", 127.73), ("강릉", 128.90), ("원주", 127.95), ("여수", 127.66), ("목포", 126.39),
    ("안동", 128.73), ("군산", 126.71), ("평양", 125.75), ("기타(경도 보정 안 함)", 135.00),
]
CITY_LON = dict(CITIES)
SOLAR_MODES = ["표준시 그대로 (기본)", "진태양시 (출생지 경도 보정)", "진태양시 (경도 + 균시차)"]


def equation_of_time_minutes(d):
    n = d.timetuple().tm_yday
    b = 2 * math.pi * (n - 81) / 365.0
    return 9.87 * math.sin(2 * b) - 7.53 * math.cos(b) - 1.5 * math.sin(b)


# =====================================================================
#  사주 구조 계산
# =====================================================================
POS_KEYS = ["year", "month", "day", "hour"]
POS_LABEL = {"year": "연주", "month": "월주", "day": "일주", "hour": "시주"}
POS_SHORT = {"year": "연", "month": "월", "day": "일", "hour": "시"}
POS_PALACE = {
    "year": "조상·초년기·사회적 배경",
    "month": "부모·직업·청년기(사회궁)",
    "day": "나 자신·배우자(배우자궁)",
    "hour": "자녀·말년·결과물",
}


def _first_month_stem(year_stem):
    return ((year_stem % 5) * 2 + 2) % 10


def _first_hour_stem(day_stem):
    return ((day_stem % 5) * 2) % 10


def _wolgeon_terms(year):
    out = []
    for yy in (year - 1, year, year + 1):
        for name in WOLGEON_JIEQI:
            out.append((name, term_kst(name, yy)))
    out.sort(key=lambda x: x[1])
    return out


def _pillars_at(calc_dt, time_known):
    terms = _wolgeon_terms(calc_dt.year)
    ipchun = term_kst("입춘", calc_dt.year)
    saju_year = calc_dt.year if calc_dt >= ipchun else calc_dt.year - 1
    ys, yb = (saju_year - 4) % 10, (saju_year - 4) % 12
    cur = 0
    for i, (name, dt) in enumerate(terms):
        if dt <= calc_dt:
            cur = i
        else:
            break
    month_name = terms[cur][0]
    order = WOLGEON_JIEQI.index(month_name)
    mb = (2 + order) % 12
    ms = (_first_month_stem(ys) + order) % 10
    sd = (calc_dt + timedelta(hours=1)).date() if calc_dt.hour >= 23 else calc_dt.date()
    didx = (jdn_of_date(sd) + 49) % 60
    ds, db = didx % 10, didx % 12
    hour = None
    if time_known:
        hb = ((calc_dt.hour + 1) % 24) // 2
        hour = ((_first_hour_stem(ds) + hb) % 10, hb)
    prev_t = terms[cur]
    next_t = terms[cur + 1] if cur + 1 < len(terms) else None
    return {
        "pillars": {"year": (ys, yb), "month": (ms, mb), "day": (ds, db), "hour": hour},
        "saju_year": saju_year, "month_term": month_name,
        "prev_term": prev_t, "next_term": next_t, "terms": terms, "day_idx": didx,
    }


def compute_chart(name="", gender="남", calendar="양력", y=2000, m=1, d=1, hh=12, mm=0,
                  time_known=True, leap=False, place="서울", solar_mode=0, use_history=True):
    """입력값으로 사주 원국(chart)을 계산."""
    if not (1900 <= y <= 2100):
        raise ValueError("1900년~2100년 사이만 계산할 수 있어요.")
    if calendar == "음력":
        sol = lunar_to_solar(y, m, d, leap)
        lunar = (y, m, d, bool(leap))
    else:
        try:
            sol = date(y, m, d)
        except ValueError:
            raise ValueError(f"{y}년 {m}월 {d}일은 존재하지 않는 날짜예요.")
        lunar = solar_to_lunar(sol)
    notes = []
    if time_known:
        dt_local = datetime(sol.year, sol.month, sol.day, hh, mm)
        utc = utc_from_korea_clock(dt_local, use_history)
        kst_norm = utc + K9
        if use_history:
            hn = history_note(dt_local)
            if hn:
                notes.append(hn)
        shift = 0.0
        lon = CITY_LON.get(place, 135.0)
        if solar_mode >= 1:
            shift += (lon - 135.0) * 4.0
        if solar_mode >= 2:
            shift += equation_of_time_minutes(kst_norm)
        calc_dt = kst_norm + timedelta(minutes=shift)
        if solar_mode >= 1:
            notes.append(f"진태양시 보정: 출생지 '{place}' 기준 {shift:+.0f}분 적용 "
                         f"(보정 후 {calc_dt:%H:%M}).")
    else:
        dt_local = datetime(sol.year, sol.month, sol.day, 12, 0)
        calc_dt = dt_local
        notes.append("태어난 시간을 몰라서 시주는 빼고 풀이했어요.")
    base = _pillars_at(calc_dt, time_known)
    if not time_known:
        lo = _pillars_at(datetime(sol.year, sol.month, sol.day, 0, 5), False)["pillars"]
        hi = _pillars_at(datetime(sol.year, sol.month, sol.day, 23, 0), False)["pillars"]
        if lo["year"] != hi["year"] or lo["month"] != hi["month"]:
            notes.append("이날은 절기가 바뀌는 날이라, 태어난 시간에 따라 연주·월주가 달라질 수 있어요. "
                         "시간을 알면 입력하는 것이 정확합니다.")
    elif base["next_term"] is not None:
        for nm, dtt in (base["prev_term"], base["next_term"]):
            gap = abs((calc_dt - dtt).total_seconds()) / 60.0
            if gap <= 30:
                notes.append(f"출생 시각이 절기 '{nm}'({dtt:%m/%d %H:%M}) 전후 {int(gap)}분 이내라서, "
                             f"만세력 앱과 한 번 대조해 보시길 권해요(절기 시각은 분 단위로 계산됩니다).")
                break
    return {
        "name": name, "gender": gender, "calendar": calendar, "solar_date": sol, "lunar": lunar,
        "dt_local": dt_local, "calc_dt": calc_dt, "time_known": time_known, "place": place,
        "solar_mode": solar_mode, "pillars": base["pillars"], "saju_year": base["saju_year"],
        "month_term": base["month_term"], "prev_term": base["prev_term"], "next_term": base["next_term"],
        "terms": base["terms"], "day_idx": base["day_idx"], "notes": notes,
    }


# =====================================================================
#  십성 / 12운성 / 합충형파해 / 신살
# =====================================================================
def ten_god(day_stem, other_stem):
    """일간 기준 다른 천간의 십성. (이름, 그룹)"""
    ho, oo = OHANG_GAN[day_stem], OHANG_GAN[other_stem]
    same = (day_stem % 2 == other_stem % 2)
    if oo == ho:
        return ("비견" if same else "겁재"), "비겁"
    if SAENG[ho] == oo:
        return ("식신" if same else "상관"), "식상"
    if GEUK[ho] == oo:
        return ("편재" if same else "정재"), "재성"
    if GEUK[oo] == ho:
        return ("편관" if same else "정관"), "관성"
    return ("편인" if same else "정인"), "인성"


def ten_god_branch(day_stem, branch):
    """지지의 십성(정기 기준)."""
    return ten_god(day_stem, main_stem(branch))


GROUPS = ["비겁", "식상", "재성", "관성", "인성"]
STAGES = ["장생", "목욕", "관대", "건록", "제왕", "쇠", "병", "사", "묘", "절", "태", "양"]
_JANGSAENG = {0: 11, 1: 6, 2: 2, 3: 9, 4: 2, 5: 9, 6: 5, 7: 0, 8: 8, 9: 3}


def twelve_stage(stem, branch):
    s = _JANGSAENG[stem]
    k = (branch - s) % 12 if stem % 2 == 0 else (s - branch) % 12
    return STAGES[k]


def group_to_oheng(day_stem, group):
    ho = OHANG_GAN[day_stem]
    if group == "비겁":
        return ho
    if group == "식상":
        return SAENG[ho]
    if group == "재성":
        return GEUK[ho]
    if group == "관성":
        return next(k for k, v in GEUK.items() if v == ho)
    return next(k for k, v in SAENG.items() if v == ho)  # 인성


# --- 천간 합/충
_GAN_HAP = {frozenset({0, 5}): "토", frozenset({1, 6}): "금", frozenset({2, 7}): "수",
            frozenset({3, 8}): "목", frozenset({4, 9}): "화"}
_GAN_CHUNG = [frozenset({0, 6}), frozenset({1, 7}), frozenset({2, 8}), frozenset({3, 9})]

# --- 지지 관계
_SAMHAP = [({8, 0, 4}, "수국(水局)", 0), ({11, 3, 7}, "목국(木局)", 3),
           ({2, 6, 10}, "화국(火局)", 6), ({5, 9, 1}, "금국(金局)", 9)]
_BANGHAP = [({2, 3, 4}, "동방 목(木)"), ({5, 6, 7}, "남방 화(火)"),
            ({8, 9, 10}, "서방 금(金)"), ({11, 0, 1}, "북방 수(水)")]
_YUKHAP = {frozenset({0, 1}): "토", frozenset({2, 11}): "목", frozenset({3, 10}): "화",
           frozenset({4, 9}): "금", frozenset({5, 8}): "수", frozenset({6, 7}): "화/토"}
_CHUNG = [frozenset(p) for p in ((0, 6), (1, 7), (2, 8), (3, 9), (4, 10), (5, 11))]
_HYUNG_PAIRS = {frozenset({2, 5}): "무은지형(인사)", frozenset({5, 8}): "무은지형(사신)",
                frozenset({2, 8}): "무은지형(인신)", frozenset({1, 10}): "지세지형(축술)",
                frozenset({10, 7}): "지세지형(술미)", frozenset({1, 7}): "지세지형(축미)",
                frozenset({0, 3}): "무례지형(자묘)"}
_JAHYUNG = {4, 6, 9, 11}
_HAE = [frozenset(p) for p in ((0, 7), (1, 6), (2, 5), (3, 4), (8, 11), (9, 10))]
_PA = [frozenset(p) for p in ((0, 9), (1, 4), (2, 11), (3, 6), (5, 8), (7, 10))]
_WONJIN = [frozenset(p) for p in ((0, 7), (1, 6), (2, 9), (3, 8), (4, 11), (5, 10))]

REL_DESC = {
    "육합": "서로 끌려서 손을 잡는 사이 — 인연·협력·화합",
    "삼합": "세 글자가 한마음으로 뭉치는 힘 — 팀워크·좋은 결실",
    "반합": "세 글자가 모여야 완성되는 팀에서 두 글자만 모인 상태 — 뭉치려는 마음은 있지만 빠진 한 글자가 들어와야 힘이 완성돼요",
    "방합": "같은 계절의 기운이 모이는 힘 — 그 오행이 더 강해져요",
    "충": "정면으로 부딪히는 사이 — 변화·이동·전환이 생기고 관계에 긴장이 있어요",
    "형": "서로 불편하고 압박을 주는 사이 — 갈등·구설·스트레스가 생기기 쉬워요",
    "해": "은근히 서로를 서운하게 하는 사이 — 오해와 서운함이 쌓이기 쉬워요",
    "파": "계획이나 약속이 틀어지기 쉬운 사이 — 일정·약속이 바뀔 수 있어요",
    "원진": "이유 없이 밉다가도 끌리는 애증의 사이",
    "천간합": "하늘 글자 둘이 서로 끌려 하나가 되는 사이 — 인연·결합",
    "천간충": "하늘 글자 둘이 서로 맞붙는 사이 — 의견 충돌·변화",
}
REL_GOOD = {"육합": True, "삼합": True, "반합": True, "방합": True, "천간합": True,
            "충": False, "형": False, "해": False, "파": False, "원진": False, "천간충": False}


def branch_relations(a, b):
    """두 지지 사이의 관계 목록: [(종류, 설명문구), ...]"""
    out = []
    pair = frozenset({a, b})
    if a == b:
        if a in _JAHYUNG:
            out.append(("형", f"자형({JI[a]}{JI[a]})"))
        return out
    if pair in _YUKHAP:
        out.append(("육합", f"{JI[a]}{JI[b]}합({_YUKHAP[pair]})"))
    for grp, label, wang in _SAMHAP:
        if a in grp and b in grp:
            miss = (grp - {a, b}).pop()
            out.append(("반합", f"{label} 반합 (빠진 글자: {JI[miss]}({JI_H[miss]}))"))
    for grp, label in _BANGHAP:
        if a in grp and b in grp:
            miss = (grp - {a, b}).pop()
            out.append(("방합", f"{label} 방합 구성 (빠진 글자: {JI[miss]}({JI_H[miss]}))"))
    if pair in _CHUNG:
        out.append(("충", f"{JI[a]}{JI[b]}충"))
    if pair in _HYUNG_PAIRS:
        out.append(("형", _HYUNG_PAIRS[pair]))
    if pair in _HAE:
        out.append(("해", f"{JI[a]}{JI[b]}해"))
    if pair in _PA:
        out.append(("파", f"{JI[a]}{JI[b]}파"))
    if pair in _WONJIN:
        out.append(("원진", f"{JI[a]}{JI[b]}원진"))
    return out


def stem_relations(a, b):
    out = []
    pair = frozenset({a, b})
    if pair in _GAN_HAP:
        out.append(("천간합", f"{GAN[a]}{GAN[b]}합({_GAN_HAP[pair]})"))
    if pair in _GAN_CHUNG:
        out.append(("천간충", f"{GAN[a]}{GAN[b]}충"))
    return out


def chart_relations(pillars):
    """원국 안의 합·충·형·파·해 목록."""
    keys = [k for k in POS_KEYS if pillars.get(k)]
    res = []
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            ka, kb = keys[i], keys[j]
            for kind, label in stem_relations(pillars[ka][0], pillars[kb][0]):
                res.append({"where": f"{POS_SHORT[ka]}간 {GAN[pillars[ka][0]]} ↔ {POS_SHORT[kb]}간 {GAN[pillars[kb][0]]}",
                            "kind": kind, "label": label, "good": REL_GOOD[kind], "desc": REL_DESC[kind]})
            for kind, label in branch_relations(pillars[ka][1], pillars[kb][1]):
                res.append({"where": f"{POS_SHORT[ka]}지 {JI[pillars[ka][1]]} ↔ {POS_SHORT[kb]}지 {JI[pillars[kb][1]]}",
                            "kind": kind, "label": label, "good": REL_GOOD[kind], "desc": REL_DESC[kind]})
    br = {pillars[k][1] for k in keys}
    for grp, label, wang in _SAMHAP:
        if grp <= br:
            res.append({"where": "원국 전체", "kind": "삼합", "label": f"{label} 완성", "good": True,
                        "desc": REL_DESC["삼합"]})
    for grp, label in _BANGHAP:
        if grp <= br:
            res.append({"where": "원국 전체", "kind": "방합", "label": f"{label} 완성", "good": True,
                        "desc": REL_DESC["방합"]})
    return res


_DOHWA_ETC = [({2, 6, 10}, 3, 8, 10), ({8, 0, 4}, 9, 2, 4),
              ({5, 9, 1}, 6, 11, 1), ({11, 3, 7}, 0, 5, 7)]  # (삼합, 도화, 역마, 화개)
_CHEONEUL = {0: (1, 7), 4: (1, 7), 6: (1, 7), 1: (0, 8), 5: (0, 8), 2: (11, 9), 3: (11, 9),
             8: (5, 3), 9: (5, 3), 7: (2, 6)}


def calc_shinsal(pillars, day_idx):
    """간단 신살: 도화·역마·화개·천을귀인·공망."""
    keys = [k for k in POS_KEYS if pillars.get(k)]
    branches = {k: pillars[k][1] for k in keys}
    found = []

    def where_of(target, exclude=None):
        return [POS_SHORT[k] + "지" for k in keys if branches[k] == target and k != exclude]

    for idx, name in ((1, "도화살"), (2, "역마살"), (3, "화개살")):
        seen = set()
        for base_key, base_label in (("year", "연지"), ("day", "일지")):
            base_b = branches[base_key]
            for grp in _DOHWA_ETC:
                if base_b in grp[0]:
                    target = grp[idx]
                    w = where_of(target, exclude=base_key if target != base_b else None)
                    if target == base_b:
                        w = [POS_SHORT[base_key] + "지"]
                    for x in w:
                        key = (name, x)
                        if key not in seen:
                            seen.add(key)
                            found.append({"name": name, "where": f"{x} {JI[target]}", "basis": base_label + " 기준"})
    seen = set()
    for base_key, base_label in (("day", "일간"), ("year", "연간")):
        if base_key not in pillars or not pillars[base_key]:
            continue
        for tb in _CHEONEUL[pillars[base_key][0]]:
            for x in where_of(tb):
                if ("천을귀인", x) not in seen:
                    seen.add(("천을귀인", x))
                    found.append({"name": "천을귀인", "where": f"{x} {JI[tb]}", "basis": base_label + " 기준"})
    xun = day_idx // 10
    gm = ((10 - 2 * xun) % 12, (11 - 2 * xun) % 12)
    for k in keys:
        if k != "day" and branches[k] in gm:
            found.append({"name": "공망", "where": f"{POS_SHORT[k]}지 {JI[branches[k]]}", "basis": f"일주 기준 공망({JI[gm[0]]}{JI[gm[1]]})"})
    return found, gm


# =====================================================================
#  분석 (십성·강약·용신·대운·세운)
# =====================================================================
def _group_weights(pillars, ds):
    ss_w = {g: 0.0 for g in GROUPS}
    oh_w = {o: 0.0 for o in OHANG_LIST}
    ohn = {o: 0 for o in OHANG_LIST}
    basic = {g: 0 for g in GROUPS}
    for k in POS_KEYS:
        p = pillars.get(k)
        if not p:
            continue
        s, b = p
        ohn[OHANG_GAN[s]] += 1
        ohn[OHANG_JI[b]] += 1
        oh_w[OHANG_GAN[s]] += 1.0
        if k != "day":
            _, g = ten_god(ds, s)
            ss_w[g] += 1.0
            basic[g] += 1
        _, gb = ten_god_branch(ds, b)
        basic[gb] += 1
        factor = 2.0 if k == "month" else 1.0
        for hs, w in JIJANGGAN[b]:
            oh_w[OHANG_GAN[hs]] += w
            _, g2 = ten_god(ds, hs)
            ss_w[g2] += w * factor
    return ss_w, oh_w, ohn, basic


def strength_grade(ratio):
    if ratio >= 0.70:
        return "극신강"
    if ratio >= 0.55:
        return "신강"
    if ratio >= 0.45:
        return "중화"
    if ratio >= 0.30:
        return "신약"
    return "극신약"


def analyze(chart, now=None):
    now = now or datetime.now()
    pil = chart["pillars"]
    ds = pil["day"][0]
    dso = OHANG_GAN[ds]
    keys = [k for k in POS_KEYS if pil.get(k)]
    an = {"ds": ds, "dso": dso, "keys": keys}
    # 각 글자 십성
    gods = {}
    for k in keys:
        s, b = pil[k]
        entry = {}
        entry["stem"] = ("일간(나)", "-") if k == "day" else ten_god(ds, s)
        entry["branch"] = ten_god_branch(ds, b)
        entry["hidden"] = [(GAN[hs], ten_god(ds, hs)[0], w) for hs, w in JIJANGGAN[b]]
        entry["stage"] = twelve_stage(ds, b)
        gods[k] = entry
    an["gods"] = gods
    ss_w, oh_w, ohn, basic = _group_weights(pil, ds)
    an["ss_w"], an["oh_w"], an["oh_n"], an["ss_basic"] = ss_w, oh_w, ohn, basic
    total = 1.0 + sum(ss_w.values())
    support = 1.0 + ss_w["비겁"] + ss_w["인성"]
    ratio = support / total if total else 0.5
    an["ratio"] = ratio
    an["grade"] = strength_grade(ratio)
    mg = ten_god_branch(ds, pil["month"][1])[1]
    an["deukryeong"] = mg in ("비겁", "인성")
    an["month_group"] = mg
    # 용신(억부) 후보
    cands = ["식상", "재성", "관성"] if ratio >= 0.5 else ["인성", "비겁"]
    order = {g: i for i, g in enumerate(cands)}
    ranked = sorted(cands, key=lambda g: (ss_w[g], order[g]))
    an["yong"] = [(g, group_to_oheng(ds, g)) for g in ranked]
    an["avoid"] = [(g, group_to_oheng(ds, g)) for g in GROUPS if g not in cands]
    mb = pil["month"][1]
    if mb in (11, 0, 1):
        an["johu"] = ("화", "한겨울에 태어나 차가운 기운이 강해서, 따뜻한 화(火) 기운이 도움이 됩니다.")
    elif mb in (5, 6, 7):
        an["johu"] = ("수", "한여름에 태어나 뜨거운 기운이 강해서, 식혀주는 수(水) 기운이 도움이 됩니다.")
    elif mb in (2, 3, 4):
        an["johu"] = (None, "만물이 자라는 봄에 태어나 한난(寒暖)의 치우침이 크지 않은 편입니다.")
    else:
        an["johu"] = (None, "수확의 가을에 태어나 한난(寒暖)의 치우침이 크지 않지만 다소 건조한 기운이 있습니다.")
    an["relations"] = chart_relations(pil)
    an["shinsal"], an["gongmang"] = calc_shinsal(pil, chart["day_idx"])
    an["daeun"] = calc_daeun(chart, an, now)
    an["sewoon"] = calc_sewoon(chart, an, now)
    an["now"] = now
    return an


def rate_groups(an, g1, g2):
    good = {"식상", "재성", "관성"} if an["ratio"] >= 0.5 else {"비겁", "인성"}
    sc = (1 if g1 in good else -1) + (1 if g2 in good else -1)
    return sc, ("순풍(좋은 흐름)" if sc == 2 else "보통" if sc == 0 else "주의(조절 필요)")


def calc_daeun(chart, an, now):
    pil = chart["pillars"]
    ys = pil["year"][0]
    gender = chart["gender"]
    forward = (ys % 2 == 0 and gender == "남") or (ys % 2 == 1 and gender == "여")
    calc = chart["calc_dt"]
    terms = chart["terms"]
    if forward:
        target = next((dt for nm, dt in terms if dt > calc), None)
    else:
        target = next((dt for nm, dt in reversed(terms) if dt <= calc), None)
    diff_days = abs((target - calc).total_seconds()) / 86400.0 if target else 15.0
    age_years = diff_days / 3.0
    yrs = int(age_years)
    mons = int(round((age_years - yrs) * 12))
    if mons == 12:
        yrs, mons = yrs + 1, 0
    su = max(1, int(age_years + 0.5))
    mi = gz_index(*pil["month"])
    ds = an["ds"]
    birth_year = chart["solar_date"].year
    age_now = (now - chart["dt_local"]).days / 365.2425
    cycles = []
    cur_k = None
    for k in range(1, 10):
        idx = (mi + k) % 60 if forward else (mi - k) % 60
        st, br = idx % 10, idx % 12
        g1 = ten_god(ds, st)
        g2 = ten_god_branch(ds, br)
        sc, label = rate_groups(an, g1[1], g2[1])
        a0 = su + 10 * (k - 1)
        cyc = {"k": k, "age_from": a0, "age_to": a0 + 9, "year_from": birth_year + a0,
               "gz": GAN[st] + JI[br], "gz_h": GAN_H[st] + JI_H[br], "stem": st, "branch": br,
               "g1": g1, "g2": g2, "stage": twelve_stage(ds, br), "score": sc, "rating": label}
        cycles.append(cyc)
        if age_now >= (age_years + 10 * (k - 1)) and age_now < (age_years + 10 * k):
            cur_k = k
    return {"forward": forward, "years": yrs, "months": mons, "su": su, "age_years": age_years,
            "cycles": cycles, "current": cur_k, "age_now": age_now,
            "before_first": age_now < age_years}


def calc_sewoon(chart, an, now):
    pil = chart["pillars"]
    ds = an["ds"]
    day_b = pil["day"][1]
    month_b = pil["month"][1]
    rows = []
    for yr in range(now.year - 1, now.year + 5):
        idx = (yr - 4) % 60
        st, br = idx % 10, idx % 12
        g1 = ten_god(ds, st)
        g2 = ten_god_branch(ds, br)
        sc, label = rate_groups(an, g1[1], g2[1])
        events = []
        for kind, lab in branch_relations(br, day_b):
            events.append(("일지", kind, lab))
        for kind, lab in branch_relations(br, month_b):
            events.append(("월지", kind, lab))
        for kind, lab in stem_relations(st, ds):
            events.append(("일간", kind, lab))
        rows.append({"year": yr, "gz": GAN[st] + JI[br], "gz_h": GAN_H[st] + JI_H[br], "stem": st,
                     "branch": br, "g1": g1, "g2": g2, "stage": twelve_stage(ds, br),
                     "score": sc, "rating": label, "events": events, "is_now": yr == now.year})
    return rows


# =====================================================================
#  풀이 문장 라이브러리
# =====================================================================
def _has_batchim(word):
    for ch in reversed(word):
        if "가" <= ch <= "힣":
            return (ord(ch) - 0xAC00) % 28 != 0
        if ch.isdigit():
            return ch in "013678"
        if ch.isalpha():
            return False
    return False


def josa(word, with_b, without_b):
    """받침 여부에 따라 조사를 붙인다. 예) josa('민수','이','가') → '민수가'"""
    return word + (with_b if _has_batchim(word) else without_b)


OH_COLOR = {"목": "#2f9e62", "화": "#d9453b", "토": "#c99a2e", "금": "#8b96a3", "수": "#2f6fb5"}
OH_HANJA = {"목": "木", "화": "火", "토": "土", "금": "金", "수": "水"}
GROUP_COLOR = {"비겁": "#6c8ebf", "식상": "#e08a3c", "재성": "#c9a227", "관성": "#8e5aa8", "인성": "#3f9e8a"}

GRADE_PLAIN = {
    "극신강": "극신강 (내 힘이 아주 센 편)", "신강": "신강 (내 힘이 센 편)", "중화": "중화 (내 힘이 알맞은 편)",
    "신약": "신약 (내 힘이 조금 약한 편)", "극신약": "극신약 (내 힘이 많이 약한 편)",
}
GROUP_TAG = {"비겁": "비겁(내 편)", "식상": "식상(재능)", "재성": "재성(돈)", "관성": "관성(직장)", "인성": "인성(공부)"}
GROUP_FIELD = {"비겁": "사람·경쟁", "식상": "재능·표현", "재성": "돈·현실", "관성": "직장·책임", "인성": "공부·도움"}
GROUP_PLAIN = {
    "비겁": "나와 같은 편 기운(비겁)", "식상": "재능·표현 기운(식상)", "재성": "돈·현실 기운(재성)",
    "관성": "직장·규칙 기운(관성)", "인성": "공부·도움 기운(인성)",
}
ILGAN_BLURB = {
    "갑": "큰 나무처럼 곧고 당당한 성격이에요. 주관이 뚜렷하고 앞장서는 걸 좋아하지만, 한번 마음먹으면 잘 굽히지 않는 고집도 있어요.",
    "을": "풀이나 덩굴처럼 부드럽고 적응력이 좋은 성격이에요. 사람들과 잘 어울리고 끈기가 있지만, 가끔 남에게 기대고 싶은 마음이 커질 수 있어요.",
    "병": "태양처럼 밝고 뜨거운 성격이에요. 솔직하고 추진력이 좋지만, 성격이 급하고 눈에 띄고 싶은 마음이 앞설 때가 있어요.",
    "정": "촛불처럼 은은하고 따뜻한 성격이에요. 섬세하고 정이 많으며 집중력이 좋지만, 예민하고 마음이 여려 걱정을 많이 할 수 있어요.",
    "무": "큰 산처럼 묵직하고 믿음직한 성격이에요. 마음이 넓고 듬직하지만, 변화를 싫어하고 융통성이 부족하다는 말을 들을 수 있어요.",
    "기": "기름진 밭처럼 성실하고 알뜰한 성격이에요. 현실적이고 꼼꼼하지만, 걱정이 많아서 나서기를 망설일 때가 있어요.",
    "경": "단단한 쇠처럼 의리 있고 결단력 있는 성격이에요. 맺고 끊음이 분명하지만, 말이 직설적이고 융통성이 부족할 수 있어요.",
    "신": "보석처럼 섬세하고 감각이 뛰어난 성격이에요. 미적 감각과 완벽주의가 있지만, 예민하고 자존심이 세서 까다롭게 보일 수 있어요.",
    "임": "큰 강이나 바다처럼 마음이 넓고 지혜로운 성격이에요. 생각이 깊고 자유로운 걸 좋아하지만, 마음이 자주 바뀌고 한곳에 머물기 어려울 수 있어요.",
    "계": "맑은 샘물처럼 순수하고 감이 좋은 성격이에요. 눈치가 빠르고 참을성이 있지만, 마음이 여리고 결정을 미루는 편일 수 있어요.",
}
ILGAN_KEYWORD = {
    "갑": "리더십·정직·고집", "을": "적응력·사교성·끈기", "병": "열정·솔직·추진력", "정": "섬세함·헌신·집중력",
    "무": "신뢰·포용·묵직함", "기": "성실·실속·겸손", "경": "의리·결단·강직", "신": "예민한 감각·완벽주의·자존심",
    "임": "지혜·포용·자유로움", "계": "직관·순수·인내",
}
STRENGTH_TEXT = {
    ("목", True): "나무 기운(내 기운)이 튼튼해서 의지와 추진력이 강해요. 내 주장이 뚜렷한 만큼, 남의 이야기도 한 번 들어보고 속도를 조절하면 더 크게 성장해요.",
    ("목", False): "나무의 뿌리가 약한 편이라 뜻은 큰데 힘이 달릴 때가 있어요. 좋은 스승·동료·환경(물과 흙)의 도움을 받으면 크게 자라요.",
    ("화", True): "불꽃이 활활 타오르는 편이라 열정과 존재감이 커요. 감정과 말이 앞서기 쉬우니, 한 박자 쉬고 말하는 습관이 도움이 돼요.",
    ("화", False): "불씨가 약한 편이라 시작할 때 힘이 부족하다고 느낄 수 있어요. 응원해 주는 사람, 규칙적인 생활, 따뜻한 환경이 힘이 돼요.",
    ("토", True): "대지처럼 든든하고 중심이 단단해요. 다만 한번 정하면 바꾸지 않는 고집이 생길 수 있으니, 변화에도 마음을 열어 보세요.",
    ("토", False): "중심을 잡는 힘이 조금 약해서 주변 영향에 흔들릴 수 있어요. 믿을 만한 사람과 안정적인 생활 습관을 곁에 두면 좋아져요.",
    ("금", True): "칼날처럼 단단하고 원칙이 분명해요. 날카로운 말이 상대에게 상처가 되지 않도록 표현을 부드럽게 다듬으면 신뢰가 더 커져요.",
    ("금", False): "예리한 감각은 있지만 밀어붙이는 힘이 부족할 수 있어요. 전문성과 자격을 쌓아서 스스로를 단단하게 만들면 강점이 살아나요.",
    ("수", True): "물이 풍부해서 생각이 깊고 적응력이 좋아요. 생각이 너무 많아져 결정을 미루지 않도록, 실행 기준을 미리 정해 두세요.",
    ("수", False): "물이 마르기 쉬운 편이라 감정과 체력 관리가 중요해요. 충분한 휴식과 배움, 지지해 주는 사람이 큰 힘이 돼요.",
}
WOLJI_TEXT = {
    0: "한겨울(자월)에 태어나서, 겉은 조용해도 속에 에너지를 차곡차곡 모으는 사람이에요. 차분해 보이지만 계획이 깊어요.",
    1: "늦겨울(축월)에 태어나서 참을성과 저장하는 힘이 있어요. 꾸준함으로 결과를 만들어 내요.",
    2: "초봄(인월)에 태어나서 시작과 도전의 기운이 있어요. 새로운 일을 여는 데 강해요.",
    3: "봄 한가운데(묘월)에 태어나서 성장과 사교의 기운이 있어요. 감각이 좋고 사람 사이를 잘 조율해요.",
    4: "늦봄(진월)에 태어나서 변화와 전환의 기운이 있어요. 다재다능하고 환경에 빨리 적응해요.",
    5: "초여름(사월)에 태어나서 열정과 영리함의 기운이 있어요. 머리 회전이 빠르고 활동적이에요.",
    6: "한여름(오월)에 태어나서 가장 뜨거운 기운이 있어요. 표현력과 존재감이 크고 열정이 넘쳐요.",
    7: "늦여름(미월)에 태어나서 결실을 준비하는 기운이 있어요. 속정이 깊고 끈기 있게 가꾸는 힘이 있어요.",
    8: "초가을(신월)에 태어나서 결단과 정리의 기운이 있어요. 판단이 빠르고 실리에 밝아요.",
    9: "가을 한가운데(유월)에 태어나서 섬세하고 깔끔한 기운이 있어요. 완성도와 원칙을 중요하게 생각해요.",
    10: "늦가을(술월)에 태어나서 신념과 의리의 기운이 있어요. 한번 정한 일은 끝까지 지키려고 해요.",
    11: "초겨울(해월)에 태어나서 지혜와 이동의 기운이 있어요. 생각이 깊고 새로운 곳에 대한 호기심이 커요.",
}
_SEASON_OF = {2: 0, 3: 0, 4: 0, 5: 1, 6: 1, 7: 1, 8: 2, 9: 2, 10: 2, 11: 3, 0: 3, 1: 3}
SEASON_NAME = ["봄", "여름", "가을", "겨울"]
SEASON_ILGAN = {
    ("목", 0): "봄에 태어난 나무라 제철을 만났어요. 쑥쑥 자라는 힘과 생명력이 좋아요.",
    ("목", 1): "여름에 태어난 나무라 뜨거운 열기에 잎이 마르기 쉬워요. 물(수) 기운, 즉 충분한 휴식·공부·감정 관리가 보약이에요.",
    ("목", 2): "가을에 태어난 나무라 가지치기를 당하는 시기예요. 시련을 겪으며 더 단단해지고 열매를 맺는 구조예요.",
    ("목", 3): "겨울에 태어난 나무라 따뜻한 햇볕(화 기운)이 필요해요. 긍정적인 사람과 따뜻한 환경이 성장의 열쇠예요.",
    ("화", 0): "봄에 태어난 불이라 땔감(나무)이 풍부해요. 열정이 오래가고 주변의 도움도 받기 쉬워요.",
    ("화", 1): "여름에 태어난 불이라 기세가 최고예요. 열정은 크지만 지치지 않도록 식히는 시간이 필요해요.",
    ("화", 2): "가을에 태어난 불이라 힘이 조금 줄어드는 시기예요. 배움과 응원(땔감)을 채우면 은은하게 오래가요.",
    ("화", 3): "겨울에 태어난 불이라 작은 불씨가 소중해요. 따뜻한 환경과 응원해 주는 사람이 성공의 열쇠예요.",
    ("토", 0): "봄에 태어난 흙이라 나무에 눌리기 쉬워서 중심 잡기가 과제예요. 믿을 만한 기반을 먼저 다지세요.",
    ("토", 1): "여름에 태어난 흙이라 메마르기 쉬워요. 마음의 여유와 물(수) 기운이 균형을 잡아줘요.",
    ("토", 2): "가을에 태어난 흙이라 수확을 마치고 쉬는 땅이에요. 안정적이고 실속 있게 쌓아가는 구조예요.",
    ("토", 3): "겨울에 태어난 흙이라 꽁꽁 얼기 쉬워요. 온기(화 기운)를 주는 사람과 활동이 도움이 돼요.",
    ("금", 0): "봄에 태어난 쇠라 힘이 약한 시기예요. 흙(안정적인 기반)의 도움을 받아 실력을 쌓으면 빛나요.",
    ("금", 1): "여름에 태어난 쇠라 불에 달궈지는 시기예요. 단련되어 쓸모가 커지지만 번아웃은 조심하세요.",
    ("금", 2): "가을에 태어난 쇠라 제철을 만났어요. 결단력과 완성도가 좋고 날이 잘 서 있어요.",
    ("금", 3): "겨울에 태어난 쇠라 차갑게 식어 있어요. 불(열정·인정)로 단련될 때 가치가 커져요.",
    ("수", 0): "봄에 태어난 물이라 나무를 키우는 데 기운을 많이 써요. 재능을 남에게 베푸는 쪽에서 쓰임이 커요.",
    ("수", 1): "여름에 태어난 물이라 증발하기 쉬워요. 체력과 감정 소모를 줄이고 충전 시간을 꼭 확보하세요.",
    ("수", 2): "가을에 태어난 물이라 맑은 물줄기(금)가 받쳐줘요. 생각이 깊고 총명하며 안정감이 있어요.",
    ("수", 3): "겨울에 태어난 물이라 제철을 만났어요. 지혜와 직감이 깊고 마음이 넓어요.",
}
GROUP_ONE_LINER = {
    "비겁": "독립심과 추진력이 강한 '마이웨이' 타입",
    "식상": "표현력과 아이디어가 돋보이는 '끼 많은' 타입",
    "재성": "현실 감각과 수완이 좋은 '실속파' 타입",
    "관성": "책임감과 조직력이 강한 '리더' 타입",
    "인성": "배우고 배려하는 걸 좋아하는 '멘토형' 타입",
}
GROUP_MEANING = {
    "비겁": "나와 같은 편 기운 — 자립심·경쟁심·친구·형제",
    "식상": "내가 밖으로 꺼내는 기운 — 표현·재능·활동·(여자는) 자녀",
    "재성": "내가 다루는 기운 — 돈·현실·성과·(남자는) 아내·연애 상대",
    "관성": "나를 규칙 안에 두는 기운 — 직장·책임·명예·(여자는) 남편·연애 상대",
    "인성": "나를 도와주는 기운 — 공부·자격증·보호·어머니",
}
SIPSEONG_DESC = {
    "비견": "나와 같은 편 — 자립심, 동료애, 자기 주관",
    "겁재": "승부욕과 과감함 — 경쟁, 돈 나눔, 추진력",
    "식신": "여유와 꾸준한 표현 — 먹을 복, 안정적인 재능, 낙천적인 성격",
    "상관": "재치와 비판 정신 — 창의력, 반항 기질, 뛰어난 말솜씨",
    "편재": "큰 돈과 넓은 활동 — 사업 수완, 투자, 사교성",
    "정재": "꾸준한 수입과 성실 — 알뜰함, 안정, 신용",
    "편관": "압박과 추진력 — 강한 책임감, 승부욕, 카리스마",
    "정관": "명예와 규칙 — 직장, 책임감, 반듯함",
    "편인": "독특한 공부와 직감 — 특이한 관심사, 예민함, 영감",
    "정인": "공부와 보호 — 자격, 어머니의 도움, 배려와 지혜",
}
SPOUSE_BY_SS = {
    "비견": "배우자 자리에 '비견'이 있어서 친구처럼 대등한 관계를 좋아해요. 서로 독립적이지만, 주도권 다툼이 생기지 않도록 역할을 나누면 좋아요.",
    "겁재": "배우자 자리에 '겁재'가 있어서 열정적이지만 경쟁·질투·돈 문제가 끼기 쉬워요. 돈 문제는 투명하게 나누는 것이 관계를 지켜줘요.",
    "식신": "배우자 자리에 '식신'이 있어서 편안하고 여유로운 관계를 만들어요. 서로 챙겨주고 즐거움을 나누는 따뜻한 가정을 이루기 쉬워요.",
    "상관": "배우자 자리에 '상관'이 있어서 재치 있고 자극적인 관계가 되기 쉬워요. 날카로운 말이 상처가 되지 않게 표현을 다듬는 게 관건이에요.",
    "편재": "배우자 자리에 '편재'가 있어서 활동적이고 통 큰 관계를 만들어요. 사교적이고 씀씀이가 큰 배우자를 만나기 쉬우니 가계 계획이 중요해요.",
    "정재": "배우자 자리에 '정재'가 있어서 성실하고 알뜰하게 가정을 꾸리는 배우자 인연이에요. 안정적이고 현실적인 관계를 만들어 가요.",
    "편관": "배우자 자리에 '편관'이 있어서 카리스마 있고 책임감 강한 상대에게 끌려요. 서로 부담이 되지 않게 각자의 영역을 존중해야 해요.",
    "정관": "배우자 자리에 '정관'이 있어서 반듯하고 믿음직한 배우자 인연이에요. 서로 예의와 책임을 지키는 안정적인 관계가 돼요.",
    "편인": "배우자 자리에 '편인'이 있어서 개성 강하고 독특한 상대에게 끌려요. 마음의 거리가 생기지 않도록 대화를 자주 하세요.",
    "정인": "배우자 자리에 '정인'이 있어서 나를 보살피고 이해해 주는 배우자 인연이에요. 마음이 편하지만 너무 의지하지 않도록 균형을 잡으세요.",
}
CHILD_BY_SS = {
    "비견": "자녀 자리(시지)에 '비견'이 있어서 자녀와 친구처럼 지내는 편이에요. 서로 독립적이라 간섭을 줄일수록 사이가 좋아져요.",
    "겁재": "자녀 자리(시지)에 '겁재'가 있어서 자녀와 정이 뜨거운 만큼 고집이 부딪힐 수 있어요. 한 발 물러서서 먼저 들어주는 게 중요해요.",
    "식신": "자녀 자리(시지)에 '식신'이 있어서 자녀 복이 따뜻한 편이에요. 아이를 편안하게 키우고 함께 즐거운 시간을 보내기 좋아요.",
    "상관": "자녀 자리(시지)에 '상관'이 있어서 똑똑하고 개성이 강한 자녀와 인연이 있기 쉬워요. 말을 곧이곧대로 받아치기보다 감정을 먼저 받아주면 좋아요.",
    "편재": "자녀 자리(시지)에 '편재'가 있어서 자녀와 활발하게 어울리고 아낌없이 쓰는 편이에요. 교육비·양육비 계획을 미리 세워 두면 좋아요.",
    "정재": "자녀 자리(시지)에 '정재'가 있어서 자녀를 성실하고 꼼꼼하게 챙기는 편이에요. 안정적으로 키우지만 걱정이 너무 앞서지 않게 주의하세요.",
    "편관": "자녀 자리(시지)에 '편관'이 있어서 자녀를 엄하게 키우거나, 책임감 강한 자녀와 인연이 있기 쉬워요. 혼내기보다 믿고 맡기는 시간을 늘려 보세요.",
    "정관": "자녀 자리(시지)에 '정관'이 있어서 반듯하고 예의 바른 자녀와 인연이 있기 쉬워요. 자녀가 부담을 느끼지 않도록 기대치를 조절하세요.",
    "편인": "자녀 자리(시지)에 '편인'이 있어서 개성이 강하고 독특한 관심사를 가진 자녀와 인연이 있기 쉬워요. 속마음을 알기 어려우니 대화 시간을 따로 만들어 주세요.",
    "정인": "자녀 자리(시지)에 '정인'이 있어서 자녀를 보살피는 마음이 깊어요. 너무 감싸기만 하지 말고, 스스로 해볼 기회를 주세요.",
}
PARENT_STYLE = {
    "비겁": "친구처럼 대등하게 지내는 부모", "식상": "표현이 풍부하고 잘 놀아주는 부모",
    "재성": "현실적으로 꼼꼼히 챙기는 부모", "관성": "원칙과 규칙을 중요하게 여기는 부모",
    "인성": "보살피고 가르치기를 좋아하는 부모",
}
GROUP_CAREER = {
    "비겁": ("독립심과 주도권이 중요한 일", "자영업·프리랜서·전문직·영업 리더·스포츠"),
    "식상": ("재능·표현·기술이 돈이 되는 일", "기획·콘텐츠·교육·디자인·IT/엔지니어링·요리·서비스"),
    "재성": ("현실 감각으로 돈을 다루는 일", "금융·유통·무역·회계·영업·사업·부동산"),
    "관성": ("조직과 규칙, 책임이 있는 일", "공무원·대기업·법률·군경·관리직·행정"),
    "인성": ("배우고 가르치고 보호하는 일", "교육·연구·의료·문서·자격 기반 전문직·상담"),
}
CAREER_COMBO = {
    frozenset({"식상", "재성"}): "재능이 돈으로 이어지기 쉬운 구조예요(식상생재). 기술·창작·영업으로 수익을 내기 좋아요.",
    frozenset({"재성", "관성"}): "돈과 지위를 함께 얻기 좋은 구조예요(재관쌍미). 안정적인 조직에서 성장하거나 관리·경영에 유리해요.",
    frozenset({"관성", "인성"}): "학식과 신뢰로 조직에서 인정받기 쉬운 구조예요(관인상생). 공무원·교육·연구·전문직에 잘 맞아요.",
    frozenset({"인성", "비겁"}): "마음의 중심이 단단해서 한 분야를 깊게 파고드는 데 강해요.",
    frozenset({"식상", "관성"}): "자유롭게 표현하고 싶은 마음과 조직의 틀이 서로 당기는 구조예요. 조직 안에서 창의적인 일을 맡으면 균형이 맞아요.",
    frozenset({"비겁", "재성"}): "경쟁 속에서 실속을 챙기는 힘이 있어서 영업·사업에 강해요. 대신 동업·보증은 신중하게 하세요.",
    frozenset({"비겁", "식상"}): "내 힘을 기술과 표현으로 풀어내는 데 강해서 전문 기술직·프리랜서에 잘 맞아요.",
    frozenset({"인성", "식상"}): "배운 것을 가르치거나 콘텐츠로 풀어내는 일에 좋아요.",
    frozenset({"인성", "재성"}): "이상(공부)과 현실(돈)이 서로 부딪히는 구조예요. 전문성을 수입으로 연결하면 답이 보여요.",
    frozenset({"비겁", "관성"}): "내 주장과 조직의 규칙이 팽팽한 구조예요. 권한이 보장된 책임 있는 자리가 잘 맞아요.",
}
STAGE_DESC = {
    "장생": "새로 태어나는 기운 — 시작·성장·가능성",
    "목욕": "다듬어지는 기운 — 감수성·매력·변화(들뜨지 않게 주의)",
    "관대": "사회로 나서는 기운 — 자신감·패기·성장",
    "건록": "자립하는 기운 — 실력·독립·안정된 힘",
    "제왕": "정점에 오른 기운 — 에너지 최고조·자존심(욕심 주의)",
    "쇠": "차분히 내려오는 기운 — 노련함·안정·절제",
    "병": "힘이 빠지는 기운 — 예민함·섬세함·휴식 필요",
    "사": "정리하고 멈추는 기운 — 사색적·마무리",
    "묘": "저장하는 기운 — 모으기·보관·속으로 쌓기",
    "절": "끊어졌다 새로 이어지는 기운 — 전환점·새 출발",
    "태": "싹이 트기 전의 기운 — 구상·준비·잠재력",
    "양": "길러지는 기운 — 보살핌·성장 준비·배움",
}
_STAGE_VIGOR = {"장생": 3, "목욕": 2, "관대": 3, "건록": 4, "제왕": 5, "쇠": 2, "병": 1, "사": 1, "묘": 1, "절": 0, "태": 1, "양": 2}
SHINSAL_DESC = {
    "도화살": "사람을 끄는 매력(인기)이 있다는 뜻이에요. 사람을 만나는 일·서비스·예술·방송 쪽에서 강점이 돼요. 다만 이성 관계는 신중하게 정리하는 게 좋아요.",
    "역마살": "움직임이 많다는 뜻이에요. 이사·출장·여행·해외 일이 잦거나 한곳에 가만히 있기 힘든 활동적인 기운이에요.",
    "화개살": "혼자 깊이 파고드는 기운이에요. 예술·공부·종교·철학 같은 분야에 재능이 있고, 혼자만의 시간이 꼭 필요해요.",
    "천을귀인": "힘들 때 도와주는 사람(귀인)을 만나기 쉬운 기운이에요. 어려울 때 주변에 도움을 청하면 길이 열리는 편이에요.",
    "공망": "그 자리의 기운이 '비어 있다'고 보는 개념이에요. 그 자리와 관련된 일은 기대보다 덜 채워지는 느낌이 들 수 있지만, 오히려 집착을 내려놓으면 마음이 편해지는 경우도 많아요.",
}
GROUP_DAEUN_TEXT = {
    "비겁": "사람·경쟁과 관련된 일이 많아지는 시기예요. 독립이나 동업 이야기가 나올 수 있으니 돈 관계는 분명히 해 두세요.",
    "식상": "내 재능과 표현을 밖으로 꺼내는 시기예요. 결과물을 만들기 좋지만, 말과 행동이 앞서지 않게 조심하세요.",
    "재성": "돈과 현실적인 기회, 그리고 책임이 커지는 시기예요. 수입이 늘 수 있는 만큼 지출과 투자 관리를 꼼꼼히 하세요.",
    "관성": "직장·직책·평가와 규칙이 강조되는 시기예요. 승진·이직·책임 증가가 올 수 있고 스트레스 관리가 필요해요.",
    "인성": "공부·자격증·문서·도와주는 사람(귀인)의 기운이 열리는 시기예요. 배우고 준비하고 도움을 받기 좋아요.",
}
ORGAN = {"목": "간·담·눈·근육·신경", "화": "심장·소장·혈압·혈액순환", "토": "위·비장·소화기",
         "금": "폐·대장·호흡기·피부", "수": "신장·방광·비뇨·귀·체온 조절"}
DISCLAIMER = ("이 풀이는 전통 명리학(사주 이론)을 바탕으로 한 참고용 해석이에요. 의학·법률·재테크 판단을 대신하지 않아요. "
              "같은 사주도 해석하는 방법이 학파마다 다를 수 있으니, 재미와 자기 이해를 위한 참고 정도로만 봐 주세요. "
              "자녀·결혼·재물처럼 중요한 일은 사주가 아니라 본인과 가족의 선택과 노력으로 만들어 가는 거예요.")
LIFE_STAGE_LABEL = {"year": "어린 시절 · 가정환경", "month": "청년기 · 사회생활", "day": "중년기 · 나와 배우자", "hour": "말년 · 자녀"}
FAMILY_MOOD = {
    "목": "새로운 걸 배우고 키워 가는, 성장하는 분위기",
    "화": "밝고 활기차며 대화가 많은, 따뜻한 분위기",
    "토": "차분하고 든든한, 안정적인 분위기",
    "금": "정돈되고 원칙이 있는, 깔끔한 분위기",
    "수": "조용하고 생각이 깊은, 여유로운 분위기",
}


# =====================================================================
#  리포트 모델 만들기 (GUI / HTML / 텍스트가 같은 모델을 사용)
# =====================================================================
def hanja_pillar(p):
    return (GAN_H[p[0]] + JI_H[p[1]]) if p else ""


def kor_pillar(p):
    return (GAN[p[0]] + JI[p[1]]) if p else "시간 모름"


def _tier(v, table, default=""):
    for th, txt in table:
        if v >= th:
            return txt
    return default


def _pct(v, total):
    return int(round(v * 100.0 / total)) if total else 0


def birth_label(chart):
    sol = chart["solar_date"]
    ly, lm, ld, lp = chart["lunar"]
    t = f" {chart['dt_local']:%H:%M}" if chart["time_known"] else " (시간 모름)"
    lunar_txt = f"음력 {ly}년 {'윤' if lp else ''}{lm}월 {ld}일"
    return f"양력 {sol.year}년 {sol.month}월 {sol.day}일{t}  ·  {lunar_txt}"


def _pillars_block(chart, an):
    order = ["hour", "day", "month", "year"]
    pil = chart["pillars"]
    cols = []
    rows_ss, rows_branch, rows_hidden, rows_stage, rows_sin = [], [], [], [], []
    sin_by = {}
    for s in an["shinsal"]:
        for tag in ("연", "월", "일", "시"):
            if s["where"].startswith(tag + "지"):
                sin_by.setdefault({"연": "year", "월": "month", "일": "day", "시": "hour"}[tag], []).append(s["name"])
    for k in order:
        p = pil.get(k)
        if not p:
            cols.append({"label": POS_LABEL[k], "empty": True})
            rows_ss.append("—"); rows_branch.append("—"); rows_hidden.append("—"); rows_stage.append("—"); rows_sin.append("")
            continue
        g = an["gods"][k]
        cols.append({"label": POS_LABEL[k], "empty": False,
                     "gan": GAN[p[0]], "ji": JI[p[1]], "gan_h": GAN_H[p[0]], "ji_h": JI_H[p[1]],
                     "gan_oh": OHANG_GAN[p[0]], "ji_oh": OHANG_JI[p[1]],
                     "gan_ss": g["stem"][0], "ji_ss": g["branch"][0]})
        rows_ss.append(g["stem"][0])
        rows_branch.append(g["branch"][0])
        rows_hidden.append(" ".join(f"{h[0]}" for h in g["hidden"]))
        rows_stage.append(g["stage"])
        rows_sin.append(" · ".join(dict.fromkeys(sin_by.get(k, []))))
    return {"t": "pillars", "cols": cols,
            "rows": [("천간 십성", rows_ss), ("지지 십성", rows_branch), ("지장간", rows_hidden),
                     ("12운성", rows_stage), ("신살", rows_sin)]}


# ---------------------------------------------------------------------
#  풀이용 도우미 함수
# ---------------------------------------------------------------------
def _kw(ss):
    d = SIPSEONG_DESC.get(ss, "")
    return d.split(" — ")[-1] if d else ""


def _good_groups(an):
    return {"식상", "재성", "관성"} if an["ratio"] >= 0.5 else {"비겁", "인성"}


def _now_row(an):
    return next((r for r in an["sewoon"] if r["is_now"]), None)


def _spouse_group(chart):
    return "관성" if chart["gender"] == "여" else "재성"


def _child_group(chart):
    return "식상" if chart["gender"] == "여" else "관성"


def _stars(v, thr):
    n = 1 + sum(1 for t in thr if v >= t)
    return max(1, min(5, n))


def _star_text(n):
    return "★" * n + "☆" * (5 - n)


def _jae_counts(an):
    n_jeong = n_pyeon = 0
    for k in an["keys"]:
        for nm in (an["gods"][k]["stem"][0], an["gods"][k]["branch"][0]):
            if nm == "정재":
                n_jeong += 1
            elif nm == "편재":
                n_pyeon += 1
    return n_jeong, n_pyeon


def _money_style(an):
    """돈을 다루는 스타일을 (이름, 쉬운 설명)으로 돌려준다."""
    w = an["ss_w"]
    jae = w["재성"]
    n_jeong, n_pyeon = _jae_counts(an)
    if jae < 0.8:
        return "무관심형", "돈 자체보다 일·사람·보람에 마음이 더 가는 편이에요."
    if w["비겁"] >= max(2.5, jae * 1.3):
        return "나눔형", "돈이 들어와도 사람·모임·경쟁에 쓰게 되기 쉬워서, 모으려면 장치가 필요해요."
    if n_jeong > n_pyeon:
        return "저축형", "월급·고정 수입을 차곡차곡 모으는 방식이 잘 맞아요."
    if n_pyeon > n_jeong:
        return "굴리기형", "투자·사업·프로젝트처럼 크게 움직이는 방식에 소질이 있어요."
    return "균형형", "모으는 것과 굴리는 것을 상황에 맞게 섞어 쓸 수 있어요."


def _future_years(an, group):
    now_y = an["now"].year
    return [r["year"] for r in an["sewoon"] if r["year"] >= now_y and group in (r["g1"][1], r["g2"][1])]


def _years_text(years):
    return ", ".join(f"{y}년" for y in years)


# ---------------------------------------------------------------------
#  각 풀이 섹션
# ---------------------------------------------------------------------
def _stars_block(chart, an):
    w = an["ss_w"]
    sp = _spouse_group(chart)
    ch = _child_group(chart)
    thr = [0.8, 1.8, 3.0, 4.5]
    items = [
        ("재물", "재성", w["재성"]),
        ("직업·명예", "관성", w["관성"]),
        ("연애·결혼", sp, w[sp]),
        ("자녀", ch, w[ch]),
        ("공부·자격", "인성", w["인성"]),
        ("사람·친구", "비겁", w["비겁"]),
        ("재능·표현", "식상", w["식상"]),
    ]
    bars = []
    for lab, g, v in items:
        n = _stars(v, thr)
        bars.append((lab, n, GROUP_COLOR[g], _star_text(n)))
    return {"t": "bars", "title": "분야별 한눈에 보기 (별이 많을수록 그 분야에 쓸 수 있는 기운이 많아요)", "items": bars, "max": 5}


def _character_section(chart, an):
    ds = an["ds"]
    g = GAN[ds]
    oh = an["dso"]
    strong = an["ratio"] >= 0.5
    mb = chart["pillars"]["month"][1]
    season = _SEASON_OF[mb]
    deuk = "태어난 달의 기운이 내 편이라 힘을 받는 편이고, " if an["deukryeong"] else "태어난 달의 기운은 내 편이 아니지만, "
    whole = "사주 전체로는 내 편 기운이 많은 편이에요." if strong else "사주 전체로는 내 편 기운이 적은 편이에요."
    blocks = [
        {"t": "kv", "items": [("타고난 기질", f"일간 '{g}'({GAN_H[ds]}) · {oh}({OH_HANJA[oh]}) 기운 — 키워드: {ILGAN_KEYWORD[g]}")]},
        {"t": "p", "text": ILGAN_BLURB[g]},
        {"t": "p", "text": f"내 힘의 세기: {GRADE_PLAIN[an['grade']]}. {deuk}{whole} " + STRENGTH_TEXT[(oh, strong)]},
        {"t": "p", "text": f"태어난 달의 기운: {WOLJI_TEXT[mb]}"},
        {"t": "p", "text": f"{SEASON_NAME[season]}에 태어난 {oh} 기운: {SEASON_ILGAN[(oh, season)]}"},
    ]
    top = sorted(an["ss_w"].items(), key=lambda x: -x[1])
    if top[0][1] > 0:
        blocks.append({"t": "p", "text": f"가장 두드러지는 성향: {GROUP_ONE_LINER[top[0][0]]}이에요. ({GROUP_MEANING[top[0][0]]})"})
    return blocks


def _love_section(chart, an):
    ds = an["ds"]
    gender = chart["gender"]
    key_group = _spouse_group(chart)
    w = an["ss_w"][key_group]
    label = "아내·연애 상대 기운(재성)" if gender != "여" else "남편·연애 상대 기운(관성)"
    day_ss = an["gods"]["day"]["branch"][0]
    day_stage = an["gods"]["day"]["stage"]
    blocks = [{"t": "p", "text": "태어난 날의 아래 글자(일지)는 '배우자 자리'예요. " + SPOUSE_BY_SS[day_ss]},
              {"t": "p", "text": f"배우자 자리의 에너지 상태는 '{day_stage}' — {STAGE_DESC[day_stage]}."}]
    blocks.append({"t": "p", "text": _tier(w, [
        (3.0, f"{label}이 풍부해서 인연의 기회가 많고 연애에 적극적이에요. 다만 마음이 여러 곳으로 흩어지기 쉬우니, 한 사람에게 집중하는 연습이 필요해요."),
        (1.8, f"{label}이 알맞게 있어서 인연이 자연스럽게 이어지는 편이에요. 마음이 맞는 사람을 만나면 관계가 안정적으로 발전해요."),
        (0.8, f"{label}이 은은해서 연애가 천천히, 신중하게 찾아와요. 한 사람에게 깊게 집중하는 스타일이에요."),
    ], f"{label}이 약한 편이라, 연애보다 일과 자기 성장에 에너지를 쓰는 시기가 길 수 있어요. 소개·모임 같은 만남의 기회를 일부러 만들어 보면 좋아요.")})
    star_names = ("정재", "편재") if gender != "여" else ("정관", "편관")
    cnt = {n: 0 for n in star_names}
    for k in an["keys"]:
        for nm in (an["gods"][k]["stem"][0], an["gods"][k]["branch"][0]):
            if nm in cnt:
                cnt[nm] += 1
    if cnt[star_names[0]] and not cnt[star_names[1]]:
        blocks.append({"t": "p", "text": f"'{star_names[0]}'만 있어서, 한 사람과 진지하고 안정적으로 만나는 스타일이에요."})
    elif cnt[star_names[1]] and not cnt[star_names[0]]:
        blocks.append({"t": "p", "text": f"'{star_names[1]}'만 있어서, 열정적이고 변화가 있는 연애를 하는 편이에요."})
    elif cnt[star_names[0]] and cnt[star_names[1]]:
        blocks.append({"t": "p", "text": f"'{star_names[0]}'과 '{star_names[1]}'이 함께 있어서 인연의 폭이 넓어요. 대신 마음이 갈릴 수 있으니 나만의 기준을 분명히 해 두세요."})
    if any(s["name"] == "도화살" for s in an["shinsal"]):
        blocks.append({"t": "p", "text": "도화살(사람을 끄는 매력)이 있어서 호감을 얻기 쉽고, 주변에서 먼저 관심을 보이는 경우가 많아요."})
    bad = [r for r in an["relations"] if "일지" in r["where"] and r["good"] is False]
    if bad:
        blocks.append({"t": "p", "text": f"배우자 자리(일지)가 '{bad[0]['where']}' 사이에서 {bad[0]['label']}({bad[0]['kind']})으로 부딪히고 있어서, 관계에서 변화나 마찰이 생기기 쉬운 부분이 있어요. 대화로 풀어가면 오히려 더 깊어지는 계기가 돼요."})
    yrs = _future_years(an, key_group)
    if yrs:
        blocks.append({"t": "p", "text": f"앞으로 인연·연애·결혼 이야기가 움직이기 쉬운 해: {_years_text(yrs)}. (이 해에 {label}이 들어와요)"})
    return blocks


def _career_section(chart, an):
    ranked = sorted(an["ss_w"].items(), key=lambda x: -x[1])
    a, b = ranked[0][0], ranked[1][0]
    blocks = []
    blocks.append({"t": "p", "text": f"가장 강한 기운은 {GROUP_PLAIN[a]}이에요. 그래서 '{GROUP_CAREER[a][0]}'이 잘 맞아요. 어울리는 분야: {GROUP_CAREER[a][1]}."})
    if ranked[1][1] >= 1.0:
        combo = CAREER_COMBO.get(frozenset({a, b}))
        blocks.append({"t": "p", "text": f"그다음 기운은 {GROUP_PLAIN[b]}이에요. " + (combo if combo else f"'{GROUP_CAREER[b][0]}'도 보조 적성으로 살릴 수 있어요.")})
    mg = an["month_group"]
    blocks.append({"t": "p", "text": f"사회생활 자리(월주)의 기운은 {GROUP_PLAIN[mg]}이에요. 그래서 직장이나 사회에서는 '{GROUP_CAREER[mg][0]}' 쪽 모습이 드러나요."})
    if an["ss_w"]["관성"] >= 2.5 and an["ratio"] < 0.5:
        blocks.append({"t": "p", "text": "책임과 압박이 커서 부담이 될 수 있어요. 역할을 나누고, 체력과 실력(공부·내 편 기운)을 키우는 게 중요해요."})
    nr = _now_row(an)
    if nr and "관성" in (nr["g1"][1], nr["g2"][1]):
        blocks.append({"t": "p", "text": f"올해({nr['year']}년)는 직장·직책 기운이 들어오는 해라서, 평가·승진·이직·업무 변화가 생기기 쉬워요."})
    return blocks


def _money_section(chart, an):
    w = an["ss_w"]
    jae = w["재성"]
    style, style_txt = _money_style(an)
    blocks = [{"t": "kv", "items": [("돈 쓰는 스타일", f"{style} — {style_txt}")]}]
    blocks.append({"t": "p", "text": _tier(jae, [
        (3.0, "돈이 들어오고 나가는 흐름이 활발해요. 규모가 커서 사업·투자 기회도 많지만, 그만큼 지출 관리와 위험 분산이 중요해요."),
        (1.8, "재물운이 안정적인 편이에요. 버는 만큼 관리하면 꾸준히 모을 수 있어요."),
        (0.8, "큰 욕심 없이 차분하게 모으는 방식이 잘 맞아요. 무리한 투자보다 저축과 분산 투자가 유리해요."),
    ], "돈 자체보다 다른 가치(일·사람·명예)에 마음이 더 가는 편이에요. 재물운을 키우려면 일부러 돈 관리에 관심을 갖는 것이 도움이 돼요.")})
    n_jeong, n_pyeon = _jae_counts(an)
    if n_jeong > n_pyeon:
        blocks.append({"t": "p", "text": "정재(꾸준한 돈) 성향이 우세해서, 월급·고정 수입·적금처럼 안정적으로 쌓이는 재물이 잘 맞아요."})
    elif n_pyeon > n_jeong:
        blocks.append({"t": "p", "text": "편재(큰 돈) 성향이 우세해서, 사업·투자·프로젝트처럼 오르내림은 있지만 규모가 큰 재물 방식에 소질이 있어요."})
    if w["식상"] >= 1.5 and jae >= 1.0:
        blocks.append({"t": "p", "text": "재능이 돈으로 이어지는 구조예요(식상생재). 기술·콘텐츠·서비스처럼 내 재주로 돈을 버는 방식이 좋아요."})
    if w["비겁"] >= max(2.5, jae * 1.3):
        blocks.append({"t": "p", "text": "'나와 같은 편 기운(비겁)'이 강해서 돈을 두고 경쟁하거나 나눠 쓰는 일이 생기기 쉬워요. 동업·보증·돈 빌려주기는 특히 신중하게 하세요."})
    if jae >= 2.5 and an["ratio"] < 0.45:
        blocks.append({"t": "p", "text": "돈 기회는 많은데 그걸 감당할 힘이 모자란 구조예요(재다신약). 욕심을 키우기보다 체력과 실력을 먼저 키우는 게 순서예요."})
    if an["ratio"] >= 0.55 and jae >= 1.8:
        blocks.append({"t": "p", "text": "내 힘이 충분해서 돈의 흐름을 감당할 수 있어요. 도전적인 투자도 소화할 수 있지만, 한곳에 몰아넣지 않고 나눠서 하는 게 안전해요."})
    elif an["ratio"] < 0.45:
        blocks.append({"t": "p", "text": "내 힘이 조금 약한 편이라 원금을 지키는 안전한 방식(적금·분산)이 마음 편하고 유리해요."})
    d = an["daeun"]
    rich = [c for c in d["cycles"] if "재성" in (c["g1"][1], c["g2"][1])]
    if rich:
        parts = []
        for c in rich:
            cur = " (지금)" if d["current"] == c["k"] else ""
            parts.append(f"{c['age_from']}~{c['age_to']}세({c['year_from']}년~){cur}")
        blocks.append({"t": "p", "text": "인생에서 돈의 기운이 들어오는 10년 구간(대운): " + " / ".join(parts) + ". 이 시기에는 수입 기회가 늘지만 씀씀이도 함께 커지기 쉬워요."})
    else:
        blocks.append({"t": "p", "text": "인생의 큰 흐름(대운)에서 돈의 기운이 크게 두드러지는 구간은 보이지 않아요. 큰 한 방보다 꾸준히 쌓는 방식이 맞아요."})
    nr = _now_row(an)
    if nr:
        gs = (nr["g1"][1], nr["g2"][1])
        if "재성" in gs:
            blocks.append({"t": "p", "text": f"올해({nr['year']}년)는 돈의 기운이 들어오는 해예요. 수입·거래 기회가 생길 수 있으니 놓치지 말되, 지출도 같이 늘지 않게 예산을 세우세요."})
        elif "비겁" in gs:
            blocks.append({"t": "p", "text": f"올해({nr['year']}년)는 '나와 같은 편 기운'이 들어와서 지출·경쟁·돈 부탁이 늘기 쉬운 해예요. 큰 투자나 보증은 신중하게 하세요."})
        else:
            blocks.append({"t": "p", "text": f"올해({nr['year']}년)는 돈의 흐름에 큰 변화가 없는 해예요. 평소대로 꾸준히 관리하면 돼요."})
    yrs = _future_years(an, "재성")
    if yrs:
        blocks.append({"t": "p", "text": f"앞으로 돈 기회가 움직이기 쉬운 해: {_years_text(yrs)}."})
    y = an["yong"][0][1]
    blocks.append({"t": "bullets", "items": [
        "월급날 바로 저축·투자 금액을 자동이체로 빼 두면 새는 돈이 줄어요.",
        f"나에게 필요한 기운인 {y}({OH_HANJA[y]}) 기운을 가까이하면 마음이 안정되어 돈 판단도 차분해져요. ({_OH_LIFESTYLE[y]})",
        "큰 지출(집·차·투자)은 감정이 들뜬 날 말고, 하루 이틀 지나서 다시 생각한 뒤에 정하세요.",
    ]})
    return blocks


def _child_section(chart, an):
    cg = _child_group(chart)
    w = an["ss_w"][cg]
    gender = chart["gender"]
    label = "자녀 기운(식상)" if gender == "여" else "자녀 기운(관성)"
    blocks = [{"t": "kv", "items": [("자녀 기운의 양", f"{_star_text(_stars(w, [0.8, 1.8, 3.0, 4.5]))}  ({label})")]}]
    blocks.append({"t": "p", "text": _tier(w, [
        (3.0, f"{label}이 풍부해서 자녀와의 인연이 깊고, 자녀에게 쏟는 정성이 큰 편이에요. 다만 마음이 자녀에게 너무 쏠려 걱정이 늘 수 있으니, 내 시간도 꼭 챙기세요."),
        (1.8, f"{label}이 알맞게 있어서, 자녀와의 인연이 자연스럽고 안정적인 편이에요."),
        (0.8, f"{label}이 은은해서, 자녀 문제는 서두르기보다 때를 기다리는 편이 마음이 편해요. 늦게 오는 인연이 더 깊은 경우도 많아요."),
    ], f"{label}이 적은 편이에요. 자녀를 갖는 시기나 키우는 방식이 남들과 다를 수 있고, 아이를 '스스로 크는 아이'로 키우기 쉬워요. 이 기운은 일·작품·후배나 제자를 키우는 쪽으로도 쓰여요.")})
    if "hour" in an["keys"]:
        hss = an["gods"]["hour"]["branch"][0]
        hst = an["gods"]["hour"]["stage"]
        blocks.append({"t": "p", "text": CHILD_BY_SS[hss]})
        blocks.append({"t": "p", "text": f"자녀 자리(시주)의 에너지 상태는 '{hst}' — {STAGE_DESC[hst]}. 말년에도 이 분위기가 이어져요."})
        rel = [r for r in an["relations"] if "시지" in r["where"]]
        good_rel = [r for r in rel if r["good"]]
        bad_rel = [r for r in rel if not r["good"]]
        if good_rel:
            r = good_rel[0]
            blocks.append({"t": "p", "text": f"자녀 자리(시지)가 '{r['where']}' 사이에서 서로 끌리는 관계({r['label']})예요. 자녀와 말년운에 도움이 되는 흐름이에요."})
        if bad_rel:
            r = bad_rel[0]
            blocks.append({"t": "p", "text": f"자녀 자리(시지)가 '{r['where']}' 사이에서 부딪히는 관계({r['label']})예요. {r['desc']}. 자녀와 마음을 맞추려면 대화를 자주 하는 것이 좋아요."})
        for s in an["shinsal"]:
            if s["name"] == "공망" and s["where"].startswith("시지"):
                blocks.append({"t": "p", "text": "자녀 자리가 '공망'(비어 있는 자리)이라서, 자녀에 대한 기대와 현실이 다를 수 있어요. 기대를 조금 내려놓고 아이의 속도를 믿어 주면 오히려 관계가 편안해져요."})
            if s["name"] == "도화살" and s["where"].startswith("시지"):
                blocks.append({"t": "p", "text": "자녀 자리에 도화살이 있어서, 자녀가 매력 있고 인기가 많거나 예술·표현 쪽 재능이 있을 수 있어요."})
    else:
        blocks.append({"t": "callout", "kind": "warn", "text": "태어난 시간을 몰라서 자녀 자리(시주)는 볼 수 없어요. 위 내용은 사주 전체의 자녀 기운만 참고한 거예요. 시간을 알면 더 정확해져요."})
    top = max(an["ss_w"], key=an["ss_w"].get)
    blocks.append({"t": "p", "text": f"내가 아이를 키우면 '{PARENT_STYLE[top]}'가 되기 쉬워요."})
    yrs = _future_years(an, cg)
    if yrs:
        blocks.append({"t": "p", "text": f"앞으로 자녀와 관련된 일(출산·입시·진로·독립 등)이 움직이기 쉬운 해: {_years_text(yrs)}. ({label}이 들어오는 해)"})
    blocks.append({"t": "callout", "kind": "info", "text": "자녀 인연은 사주만으로 정해지지 않아요. 이 내용은 '나는 어떤 부모가 되기 쉬운가'를 가볍게 참고하는 용도로만 봐 주세요."})
    return blocks


def _family_section(chart, an):
    w = an["ss_w"]
    blocks = []
    blocks.append({"t": "p", "text": _tier(w["인성"], [
        (3.0, "어머니나 윗사람의 보살핌과 가르침을 많이 받는 구조예요. 다만 지나친 보호 속에서 스스로 결정할 기회가 줄어들지 않게 하세요."),
        (1.8, "어머니나 윗사람의 도움을 알맞게 받는 구조예요."),
        (0.8, "도움은 받지만 크게 기대지는 않고, 스스로 크는 편이에요."),
    ], "도움을 받기보다 스스로 길을 개척하는 구조예요. 어른에게 먼저 조언을 구하는 습관을 들이면 큰 힘이 돼요.")})
    blocks.append({"t": "p", "text": _tier(w["재성"], [
        (3.0, "아버지나 집안의 경제적 기반, 현실적인 자원과 인연이 깊은 편이에요."),
        (1.8, "아버지나 집안의 경제적 도움과 인연이 알맞게 있는 편이에요."),
        (0.8, "집안의 도움에 크게 기대기보다 내 힘으로 기반을 만드는 편이에요."),
    ], "집안의 경제적 도움을 기대하기보다 스스로 기반을 쌓는 구조예요. 일찍 독립심이 자라기 쉬워요.")})
    blocks.append({"t": "p", "text": _tier(w["비겁"], [
        (3.0, "형제·친구·동료 기운이 강해서 주변에 사람이 많아요. 도움도 받지만, 경쟁하거나 돈 문제가 얽힐 수 있으니 선을 분명히 하세요."),
        (1.8, "형제·친구와 서로 도우며 지내는 알맞은 구조예요."),
        (0.8, "형제·친구와는 가깝지만 각자의 삶을 존중하는 편이에요."),
    ], "혼자 서는 힘이 강해서 형제·친구에게 크게 의지하지 않아요. 필요할 때 먼저 도움을 청하는 연습을 해 보세요.")})
    pil = chart["pillars"]
    ys = an["gods"]["year"]["branch"][0]
    ms = an["gods"]["month"]["branch"][0]
    blocks.append({"t": "p", "text": f"어린 시절·가정환경 자리(연주)의 중심 기운은 '{ys}' — {_kw(ys)}이에요."})
    blocks.append({"t": "p", "text": f"부모·사회 자리(월주)의 중심 기운은 '{ms}' — {_kw(ms)}이에요."})
    rel = [r for r in an["relations"] if ("연지" in r["where"] and "월지" in r["where"]) or ("연간" in r["where"] and "월간" in r["where"])]
    for r in rel:
        if r["good"]:
            blocks.append({"t": "p", "text": f"어린 시절 자리와 부모·사회 자리가 서로 끌리는 관계({r['label']})라서, 가정환경이 비교적 안정적이고 서로 도움이 되는 편이에요."})
        else:
            blocks.append({"t": "p", "text": f"어린 시절 자리와 부모·사회 자리가 부딪히는 관계({r['label']})라서, 어린 시절에 이사·전학·환경 변화가 있었거나 어른과 의견 차이가 있었을 수 있어요."})
    return blocks


def _study_section(chart, an):
    w = an["ss_w"]
    blocks = []
    if w["인성"] >= 2.5:
        blocks.append({"t": "p", "text": "공부하는 힘이 좋은 구조예요. 배우는 것 자체를 즐기고, 자격증·학위가 인생에 도움이 돼요."})
    elif w["인성"] >= 1.2:
        blocks.append({"t": "p", "text": "공부 기운이 알맞게 있어요. 목표가 분명하면 집중해서 결과를 낼 수 있어요."})
    else:
        blocks.append({"t": "p", "text": "책상 공부보다 경험하고 부딪히면서 배우는 방식이 잘 맞아요. 이론보다 실습·현장 중심으로 공부해 보세요."})
    if w["식상"] >= 2.0:
        blocks.append({"t": "p", "text": "이해한 것을 말·글·작품으로 풀어낼 때 실력이 올라가요. 발표·글쓰기·실습형 공부가 잘 맞아요."})
    if w["관성"] >= 2.0 and w["인성"] >= 1.5:
        blocks.append({"t": "p", "text": "시험·자격·공공 분야에 강한 구조예요(합격운이 있는 구조). 계획을 세워 꾸준히 하면 결과가 따라와요."})
    if w["비겁"] >= 3.0 and w["인성"] < 1.2:
        blocks.append({"t": "p", "text": "친구·사람이 많아 집중이 흩어질 수 있어요. 공부할 때는 혼자 있는 시간을 일부러 확보하세요."})
    nr = _now_row(an)
    if nr and "인성" in (nr["g1"][1], nr["g2"][1]):
        blocks.append({"t": "p", "text": f"올해({nr['year']}년)는 공부·자격증·계약 서류 운이 열리는 해예요. 미뤄 둔 시험이나 자격 준비를 시작하기 좋아요."})
    yrs = _future_years(an, "인성")
    if yrs:
        blocks.append({"t": "p", "text": f"앞으로 공부·자격·문서 운이 열리기 쉬운 해: {_years_text(yrs)}."})
    return blocks


def _people_section(chart, an):
    w = an["ss_w"]
    bi = w["비겁"]
    blocks = [{"t": "p", "text": _tier(bi, [
        (3.0, "발이 넓고 사람을 끌어모으는 편이에요. 관계에 에너지를 많이 쓰다 보면 정작 나를 챙길 시간이 부족해지니, 혼자만의 시간을 지키세요."),
        (1.8, "친한 사람과는 깊게, 나머지는 적당히 거리를 두는 균형 잡힌 관계를 맺어요."),
        (0.8, "넓게 사귀기보다 소수와 깊고 오래가는 관계를 좋아해요."),
    ], "사람에게 기대기보다 스스로 판단하고 움직이는 독립적인 편이에요. 도움이 필요할 때 먼저 부탁하는 연습이 관계를 풍성하게 해요.")}]
    if w["식상"] >= 2.0:
        blocks.append({"t": "p", "text": "표현력이 좋아서 말과 분위기로 사람을 끌어요. 다만 직설적인 말이 상처가 될 수 있으니 한 번 걸러서 말하면 좋아요."})
    if w["인성"] >= 2.5:
        blocks.append({"t": "p", "text": "생각이 깊고 배려하는 편이라 신뢰를 얻어요. 다만 속마음을 혼자 삭이지 말고 표현해 주세요."})
    if w["관성"] >= 2.5:
        blocks.append({"t": "p", "text": "예의와 책임을 중요하게 여겨서 윗사람과의 관계가 안정적이에요. 스스로에게 너무 엄격하지 않도록 조심하세요."})
    return blocks


def _health_section(chart, an):
    ow = an["oh_w"]
    total = sum(ow.values())
    blocks = []
    excess = [o for o in OHANG_LIST if ow[o] / total >= 0.36]
    lack = [o for o in OHANG_LIST if ow[o] / total < 0.08]
    for o in excess:
        blocks.append({"t": "p", "text": f"{o}({OH_HANJA[o]}) 기운이 너무 많은 편이에요. 관련된 부위({ORGAN[o]})를 무리하지 않도록 평소에 관리해 주세요."})
    for o in lack:
        blocks.append({"t": "p", "text": f"{o}({OH_HANJA[o]}) 기운이 부족한 편이에요. 관련된 부위({ORGAN[o]})의 컨디션 관리와 규칙적인 생활이 도움이 돼요."})
    if not blocks:
        blocks.append({"t": "p", "text": "오행이 비교적 고르게 퍼져 있어서 어느 한쪽으로 크게 치우치지 않아요."})
    blocks.append({"t": "callout", "kind": "info", "text": "오행과 신체 부위의 연결은 전통 이론에 따른 참고 정보일 뿐, 의학적 진단이 아니에요. 건강 문제는 꼭 전문가와 상의하세요."})
    return blocks


def _life_section(chart, an):
    rows = []
    vig = {}
    for k in ["year", "month", "day", "hour"]:
        if k not in an["keys"]:
            rows.append([LIFE_STAGE_LABEL[k], POS_LABEL[k], "—", "태어난 시간을 몰라서 볼 수 없어요"])
            continue
        p = chart["pillars"][k]
        g = an["gods"][k]
        ss = g["branch"][0]
        vig[k] = _STAGE_VIGOR[g["stage"]]
        rows.append([LIFE_STAGE_LABEL[k], f"{POS_LABEL[k]} {GAN[p[0]]}{JI[p[1]]}", f"{ss} ({_kw(ss)})", f"{g['stage']}: {STAGE_DESC[g['stage']]}"])
    blocks = [{"t": "p", "text": "사주의 네 기둥은 인생의 네 시기를 뜻해요. 연주는 어린 시절, 월주는 청년기, 일주는 중년기, 시주는 말년을 나타내요."},
              {"t": "table", "headers": ["인생 시기", "기둥", "이 시기의 중심 기운", "에너지 상태"], "rows": rows, "widths": [3, 2, 4, 5]}]
    if len(vig) >= 2:
        names = {"year": "어린 시절", "month": "청년기", "day": "중년기", "hour": "말년"}
        hi = max(vig, key=lambda k: vig[k])
        lo = min(vig, key=lambda k: vig[k])
        if vig[hi] != vig[lo]:
            blocks.append({"t": "p", "text": f"에너지가 가장 힘차게 쓰이는 시기는 '{names[hi]}', 힘을 아끼고 차분히 준비해야 하는 시기는 '{names[lo]}'이에요."})
    return blocks


def _yong_section(chart, an):
    y = an["yong"]
    blocks = []
    strong = an["ratio"] >= 0.5
    blocks.append({"t": "p", "text": f"사주의 균형으로 보면 '{GRADE_PLAIN[an['grade']]}'이라서, "
                                      f"{'넘치는 힘을 풀어주고 조절해 주는' if strong else '부족한 힘을 채워 주는'} 기운이 필요해요. "
                                      "아래 '필요한 기운'은 나에게 도움이 되는 방향, '조심할 기운'은 이미 충분해서 더하면 과해지기 쉬운 방향이에요."})
    blocks.append({"t": "kv", "items": [
        ("가장 필요한 기운", f"{y[0][1]}({OH_HANJA[y[0][1]]}) — {GROUP_PLAIN[y[0][0]]}"),
        ("그다음 도움 되는 기운", ", ".join(f"{o}({GROUP_FIELD[g]})" for g, o in y[1:]) or "—"),
        ("과해지기 쉬운 기운", ", ".join(f"{o}({GROUP_FIELD[g]})" for g, o in an["avoid"])),
    ]})
    blocks.append({"t": "p", "text": f"{y[0][1]}({OH_HANJA[y[0][1]]}) 기운을 가까이하는 방법: {_OH_LIFESTYLE[y[0][1]]}"})
    jo = an["johu"]
    if jo[0] and jo[0] == y[0][1]:
        extra_jo = " 계절 면에서도 같은 방향이라 이 기운의 도움이 특히 커요."
    elif jo[0]:
        extra_jo = f" 보조로 {jo[0]}({OH_HANJA[jo[0]]}) 기운도 함께 챙기면 좋아요."
    else:
        extra_jo = ""
    blocks.append({"t": "p", "text": f"태어난 계절 이야기(조후): {jo[1]}{extra_jo}"})
    blocks.append({"t": "callout", "kind": "info", "text": "필요한 기운(용신)은 학파마다 보는 방법이 달라요. 여기서는 가장 기본적인 방법(내 힘의 세기와 태어난 계절)으로 간단히 정한 거라 참고용으로만 봐 주세요."})
    return blocks


_OH_LIFESTYLE = {
    "목": "초록 식물·숲 산책, 새로운 배움과 시작, 푸른 계열 색상, 스트레칭과 성장하는 활동.",
    "화": "햇볕 쬐기·활동적인 운동, 따뜻한 색상, 사람들과의 교류, 열정을 쏟을 취미.",
    "토": "규칙적인 생활과 식사, 땅을 밟는 산책·등산, 안정적인 루틴, 황토·베이지 계열 색상.",
    "금": "정리정돈, 결단을 내리는 습관, 호흡·유산소 운동, 흰색·은색 계열, 금속 소품.",
    "수": "충분한 수분 섭취와 수면, 물가 산책·수영, 독서와 사색, 검정·남색 계열.",
}


def _relations_section(an):
    intro = {"t": "p", "text": "글자와 글자 사이에는 '서로 끌리는 관계(합)'와 '부딪히는 관계(충·형·해·파)'가 있어요. "
                               "연=어린 시절·가정, 월=사회생활·부모, 일=나·배우자, 시=자녀·말년 자리를 뜻해요. 부딪힘이 꼭 나쁜 것만은 아니고 변화가 생기는 자리라는 뜻이에요."}
    rel = an["relations"]
    if not rel:
        return [intro, {"t": "p", "text": "사주 안에서 두드러지게 끌리거나 부딪히는 관계는 보이지 않아요. 비교적 평온한 구조예요."}]
    rows = [[r["where"], r["label"], "좋은 작용(끌림)" if r["good"] else "긴장 작용(부딪힘)", r["desc"]] for r in rel]
    return [intro, {"t": "table", "headers": ["위치", "관계", "성격", "쉬운 뜻"], "rows": rows, "widths": [2, 2, 2, 5]}]


def _shinsal_section(an):
    intro = {"t": "p", "text": "신살은 사주에 있는 '특별한 표시' 같은 거예요. 있다고 크게 좋거나 나쁜 게 아니라, 어떤 성향이 두드러지는지 알려주는 참고 정보예요."}
    if not an["shinsal"]:
        return [intro, {"t": "p", "text": "기본 신살(도화·역마·화개·천을귀인·공망)에 해당하는 항목이 보이지 않아요."}]
    blocks = [intro]
    seen = {}
    for s in an["shinsal"]:
        seen.setdefault(s["name"], []).append(f"{s['where']} ({s['basis']})")
    for name, locs in seen.items():
        blocks.append({"t": "kv", "items": [(name, " · ".join(locs))]})
        blocks.append({"t": "p", "text": SHINSAL_DESC[name]})
    return blocks


def _field_cell(an, row, group):
    if group in (row["g1"][1], row["g2"][1]):
        return "◎ 기회" if group in _good_groups(an) else "△ 조절"
    return "-"


def _daeun_section(chart, an):
    d = an["daeun"]
    blocks = []
    blocks.append({"t": "p", "text": f"대운은 10년마다 바뀌는 '인생의 큰 흐름'이에요. 나는 {'순행' if d['forward'] else '역행'} 대운이고, "
                                      f"대운수는 {d['su']}이에요 (대략 만 {d['years']}세 {d['months']}개월부터 첫 대운이 시작돼요)."})
    rows, hl = [], None
    for c in d["cycles"]:
        mark = ""
        if d["current"] == c["k"]:
            hl = len(rows)
            mark = " ◀ 지금"
        rows.append([f"{c['age_from']}~{c['age_to']}세{mark}", f"{c['year_from']}년~", f"{c['gz']} ({c['gz_h']})",
                     f"{GROUP_FIELD[c['g1'][1]]} / {GROUP_FIELD[c['g2'][1]]}", c["stage"], c["rating"]])
    blocks.append({"t": "table", "headers": ["나이", "시작 연도", "대운 글자", "들어오는 기운 (겉 / 속)", "에너지", "흐름"],
                   "rows": rows, "highlight": hl, "widths": [2, 2, 2, 4, 1, 3]})
    if d["current"]:
        c = d["cycles"][d["current"] - 1]
        blocks.append({"t": "p", "text": f"지금은 {c['gz']} 대운({c['age_from']}~{c['age_to']}세)이에요. {GROUP_DAEUN_TEXT[c['g1'][1]]}"
                                          f" 속으로는 {GROUP_PLAIN[c['g2'][1]]}이 받쳐줘요. 이 시기의 흐름은 '{c['rating']}'으로 봐요."})
    elif d["before_first"]:
        blocks.append({"t": "p", "text": "아직 첫 대운이 시작되기 전이에요. 이 시기에는 태어난 달(월주)의 기운이 어린 시절을 이끌어요."})
    good_cycles = [c for c in d["cycles"] if c["score"] == 2]
    if good_cycles:
        blocks.append({"t": "p", "text": "특히 흐름이 좋은 구간(순풍): " + ", ".join(f"{c['age_from']}~{c['age_to']}세" for c in good_cycles) + "."})
    blocks.append({"t": "callout", "kind": "info", "text": "'흐름'은 나에게 도움이 되는 기운이 들어오는지로 간단히 매긴 참고 점수예요. '주의'라고 해서 나쁜 시기가 아니라, 조심하고 조절하면 좋은 시기라는 뜻이에요."})
    return blocks


def _sewoon_section(chart, an):
    rows, hl = [], None
    for r in an["sewoon"]:
        ev = " · ".join(f"{w} {lab}" for w, k, lab in r["events"]) or "—"
        if r["is_now"]:
            hl = len(rows)
        rows.append([f"{r['year']}년{' ◀ 올해' if r['is_now'] else ''}", f"{r['gz']} ({r['gz_h']})",
                     f"{GROUP_FIELD[r['g1'][1]]} / {GROUP_FIELD[r['g2'][1]]}", r["rating"], ev])
    blocks = [{"t": "p", "text": "세운은 '그해의 운'이에요. 해마다 들어오는 기운이 달라서, 같은 사람이라도 해에 따라 분위기가 달라져요."},
              {"t": "table", "headers": ["해", "그해의 글자", "들어오는 기운 (겉 / 속)", "흐름", "사주와의 관계"],
               "rows": rows, "highlight": hl, "widths": [2, 2, 4, 3, 4]}]
    frows = []
    for r in an["sewoon"]:
        frows.append([f"{r['year']}년{' ◀' if r['is_now'] else ''}", _field_cell(an, r, "재성"), _field_cell(an, r, "관성"),
                      _field_cell(an, r, "인성"), _field_cell(an, r, "식상"), _field_cell(an, r, "비겁")])
    blocks.append({"t": "p", "text": "분야별로 보면 이래요. ◎는 그 분야의 기운이 들어오면서 나에게 도움이 되는 해, △는 기운은 들어오지만 조절이 필요한 해, -는 특별한 변화가 없는 해예요."})
    blocks.append({"t": "table", "headers": ["해", "재물(돈)", "직장·명예", "공부·자격", "재능·표현", "경쟁·지출"],
                   "rows": frows, "widths": [2, 2, 2, 2, 2, 2]})
    now_row = _now_row(an)
    if now_row:
        g1, g2 = now_row["g1"][1], now_row["g2"][1]
        txt = (f"올해({now_row['year']}년 {now_row['gz']}년)는 겉으로는 {GROUP_PLAIN[g1]}, 속으로는 {GROUP_PLAIN[g2]}이 들어와요. "
               f"{GROUP_DAEUN_TEXT[g1]}")
        if g2 != g1:
            txt += f" 속으로는 {GROUP_FIELD[g2]} 쪽 일도 함께 움직여요."
        blocks.append({"t": "p", "text": txt})
        for w, k, lab in now_row["events"]:
            blocks.append({"t": "bullets", "items": [f"{josa(w, '과', '와')} {lab}({k}): {REL_DESC[k]}"]})
        blocks.append({"t": "p", "text": f"종합하면 올해의 흐름은 '{now_row['rating']}'이에요. 해는 1월 1일이 아니라 입춘(2월 초)에 바뀌는 것으로 보기 때문에, 입춘 전후로 분위기가 달라질 수 있어요."})
    return blocks



def build_personal_report(chart, an):
    name = chart["name"] or "이 사람"
    sections = []
    # 1) 원국
    pb = [{"t": "p", "text": "사주는 태어난 해·달·날·시간을 각각 두 글자(위 글자=하늘, 아래 글자=땅)로 바꾼 여덟 글자예요. "
                              "표의 '십성'은 나(일간)를 기준으로 각 글자가 나와 어떤 관계인지 알려주는 이름이고, '12운성'은 그 자리의 에너지 상태예요. 아래 '용어 쉽게 보기'에서 더 자세히 풀어 놓았어요."},
          {"t": "kv", "items": [("이름 / 성별", f"{name} / {chart['gender']}성" if chart["gender"] in ("남", "여") else name),
                                ("생년월일시", birth_label(chart)),
                                ("출생지 / 시각 기준", f"{chart['place']} / {SOLAR_MODES[chart['solar_mode']]}")]},
          _pillars_block(chart, an)]
    for n in chart["notes"]:
        pb.append({"t": "callout", "kind": "warn", "text": n})
    sections.append({"id": "chart", "title": "사주 원국 (四柱八字) — 태어난 순간의 여덟 글자", "open": True, "blocks": pb})
    # 2) 한눈에
    top = max(an["ss_w"], key=an["ss_w"].get)
    y = an["yong"][0]
    summary = (f"{GAN[an['ds']]}({GAN_H[an['ds']]}) 일간 · {GRADE_PLAIN[an['grade']]} — {GROUP_ONE_LINER[top]}. "
               f"나에게 필요한 기운: {y[1]}({OH_HANJA[y[1]]}).")
    sections.append({"id": "summary", "title": "한눈에 보기", "open": True, "blocks": [
        {"t": "callout", "kind": "info", "text": summary},
        {"t": "kv", "items": [("일간(나)", f"{GAN[an['ds']]} · {an['dso']}"), ("내 힘의 세기", f"{GRADE_PLAIN[an['grade']]} (내 편 기운 비율 {an['ratio']:.0%})"),
                              ("태어난 달의 힘", "내 편이에요 (득령)" if an["deukryeong"] else "내 편은 아니에요 (실령)"),
                              ("가장 강한 성향", f"{top} — {GROUP_MEANING[top]}")]},
        _stars_block(chart, an)]})
    # 3) 분포
    tot_n = sum(an["oh_n"].values())
    bars_n = [(f"{o}({OH_HANJA[o]})", an["oh_n"][o], OH_COLOR[o], f"{an['oh_n'][o]}글자") for o in OHANG_LIST]
    tot_w = sum(an["oh_w"].values())
    bars_w = [(f"{o}({OH_HANJA[o]})", an["oh_w"][o], OH_COLOR[o], f"{an['oh_w'][o]:.1f} ({_pct(an['oh_w'][o], tot_w)}%)") for o in OHANG_LIST]
    bars_g = [(GROUP_TAG[g], an["ss_w"][g], GROUP_COLOR[g], f"{an['ss_w'][g]:.1f}") for g in GROUPS]
    dist = [{"t": "p", "text": "오행은 세상을 이루는 다섯 가지 기운(나무·불·흙·쇠·물)이에요. 어떤 기운이 많고 적은지 보면 성격과 균형을 알 수 있어요."},
            {"t": "bars", "title": f"오행 분포 — 겉으로 보이는 {tot_n}글자 기준", "items": bars_n},
            {"t": "bars", "title": "오행 세기 — 글자 속에 숨은 기운까지 합친 값", "items": bars_w},
            {"t": "bars", "title": "다섯 가지 성향의 세기 — 태어난 달에 가중치를 더한 값", "items": bars_g}]
    miss = [o for o in OHANG_LIST if an["oh_n"][o] == 0]
    if miss:
        dist.append({"t": "p", "text": f"겉으로 보이는 글자에 없는 오행: {', '.join(miss)} — 글자 속에 숨어 있을 수 있어서 위의 '오행 세기'도 같이 봐 주세요."})
    mx = max(OHANG_LIST, key=lambda o: an["oh_w"][o])
    dist.append({"t": "p", "text": f"가장 강한 오행은 {mx}({OH_HANJA[mx]})이에요. 다섯 가지 성향의 뜻은 이래요."})
    dist.append({"t": "bullets", "items": [f"{g}: {GROUP_MEANING[g]}" for g in GROUPS]})
    sections.append({"id": "dist", "title": "오행·성향 분포", "open": True, "blocks": dist})
    sections.append({"id": "char", "title": "타고난 성격", "open": True, "blocks": _character_section(chart, an)})
    sections.append({"id": "love", "title": "연애·결혼운", "open": True, "blocks": _love_section(chart, an)})
    sections.append({"id": "career", "title": "직업운", "open": True, "blocks": _career_section(chart, an)})
    sections.append({"id": "money", "title": "재물운 (돈 버는 힘·모으는 힘)", "open": True, "blocks": _money_section(chart, an)})
    sections.append({"id": "child", "title": "자식운 (자녀 인연·말년)", "open": True, "blocks": _child_section(chart, an)})
    sections.append({"id": "family", "title": "부모·형제·가정운", "open": True, "blocks": _family_section(chart, an)})
    sections.append({"id": "study", "title": "학업·시험·자격운", "open": False, "blocks": _study_section(chart, an)})
    sections.append({"id": "people", "title": "대인관계운", "open": False, "blocks": _people_section(chart, an)})
    sections.append({"id": "health", "title": "건강 참고", "open": False, "blocks": _health_section(chart, an)})
    sections.append({"id": "life", "title": "인생 시기별 흐름 (초년·청년·중년·말년)", "open": True, "blocks": _life_section(chart, an)})
    sections.append({"id": "yong", "title": "나에게 필요한 기운 (용신·계절)", "open": True, "blocks": _yong_section(chart, an)})
    sections.append({"id": "daeun", "title": "대운 (10년 단위 큰 흐름)", "open": True, "blocks": _daeun_section(chart, an)})
    sections.append({"id": "sewoon", "title": "세운 (올해와 앞으로의 해)", "open": True, "blocks": _sewoon_section(chart, an)})
    sections.append({"id": "rel", "title": "사주 속 글자들의 관계 (합·충·형·파·해)", "open": False, "blocks": _relations_section(an)})
    sections.append({"id": "sinsal", "title": "신살 (특별한 표시)", "open": False, "blocks": _shinsal_section(an)})
    stage_rows = [[POS_LABEL[k], JI[chart["pillars"][k][1]], an["gods"][k]["stage"], STAGE_DESC[an["gods"][k]["stage"]]] for k in an["keys"]]
    god_rows = [[nm, desc] for nm, desc in SIPSEONG_DESC.items()]
    sections.append({"id": "ref", "title": "참고: 12운성·십성 뜻풀이", "open": False, "blocks": [
        {"t": "table", "headers": ["자리", "아래 글자", "12운성", "의미"], "rows": stage_rows, "widths": [1, 1, 1, 5]},
        {"t": "table", "headers": ["십성", "의미"], "rows": god_rows, "widths": [1, 6]}]})
    sections.append({"id": "glossary", "title": "용어 쉽게 보기", "open": False, "blocks": [{"t": "bullets", "items": [
        "일간: 태어난 날의 위 글자예요. 사주에서 '나 자신'을 뜻해요.",
        "오행(목·화·토·금·수): 세상을 이루는 다섯 가지 기운. 나무·불·흙·쇠·물에 비유해요.",
        "십성: 일간(나)을 기준으로 다른 글자가 나와 어떤 관계인지 알려주는 10가지 이름이에요. 비겁(내 편·경쟁), 식상(재능·표현), 재성(돈·현실), 관성(직장·책임), 인성(공부·도움) 다섯 묶음으로 봐요.",
        "신강·신약: 내 편 기운(나와 같은 편 + 나를 도와주는 기운)이 많으면 신강, 적으면 신약이에요. 좋고 나쁨이 아니라 '힘의 세기'를 말해요.",
        "용신: 사주의 균형을 맞춰 주는 '나에게 필요한 기운'이에요.",
        "대운·세운: 대운은 10년 단위, 세운은 1년 단위의 운의 흐름이에요.",
        "합·충: 합은 두 글자가 서로 끌려서 손잡는 관계, 충은 정면으로 부딪히는 관계예요.",
        "12운성: 한 기운이 태어나서 자라고 힘이 빠지는 12단계로, 그 자리의 에너지 상태를 말해요.",
        "신살: 사주에 있는 특별한 표시(매력·이동·귀인 등)예요.",
        "지장간: 아래 글자 속에 숨어 있는 위 글자예요. 겉으로 안 보이는 속마음이나 숨은 재능으로 봐요.",
    ]}]})
    sections.append({"id": "note", "title": "유의사항", "open": False, "blocks": [{"t": "p", "text": DISCLAIMER}]})
    return {"title": f"{name} 님의 사주풀이", "kind": "personal", "sections": sections}


# =====================================================================
#  궁합
# =====================================================================
_REL_WEIGHT = {"육합": 30, "삼합": 20, "반합": 16, "방합": 8, "충": -26, "형": -16, "해": -10, "파": -8, "원진": -12}
LOVER_TEXT = {
    "정재": "정재 — 성실하고 알뜰해서 안정적인 배우자감의 정석 같은 인연이에요",
    "편재": "편재 — 활기차고 매력적이며 변화가 있는 인연이에요",
    "정관": "정관 — 반듯하고 믿음직한 배우자감의 정석 같은 인연이에요",
    "편관": "편관 — 카리스마 있고 강하게 이끄는 열정적인 인연이에요",
    "비견": "비견 — 친구처럼 대등하고 편안한 관계예요",
    "겁재": "겁재 — 경쟁심과 밀고 당김이 생기기 쉬운 관계예요",
    "식신": "식신 — 내가 편안하게 챙겨주고 베푸는 관계예요",
    "상관": "상관 — 내가 자극을 주고 표현을 이끌어 내는 관계예요",
    "정인": "정인 — 상대가 나를 보살피고 이해해 주는 관계예요",
    "편인": "편인 — 상대가 독특한 시각으로 나를 자극하는 관계예요",
}
_LOVER_BONUS = {"정재": 14, "편재": 10, "정관": 14, "편관": 8, "정인": 8, "편인": 3, "식신": 5, "상관": 1, "비견": 4, "겁재": -2}


def _lover_bonus(gender, god_name):
    """gender가 남이면 재성이, 여이면 관성이 배우자별. 반대 성격이면 보너스를 줄임."""
    b = _LOVER_BONUS[god_name]
    if gender == "남" and god_name in ("정관", "편관"):
        return {"정관": 4, "편관": -2}[god_name]
    if gender == "여" and god_name in ("정재", "편재"):
        return {"정재": 6, "편재": 4}[god_name]
    return b


def _rel_delta(a, b, scale=1.0):
    """두 지지 관계 점수와 설명 목록 [(kind, label, delta)]"""
    items = []
    rels = branch_relations(a, b)
    for kind, label in rels:
        items.append((kind, label, int(round(_REL_WEIGHT[kind] * scale))))
    if a == b and not rels:
        items.append(("같은 지지", f"같은 글자({JI[a]})", int(round(4 * scale))))
    total = sum(x[2] for x in items)
    total = max(-int(40 * scale), min(int(45 * scale), total))
    return total, items


def _clamp(v, lo=8, hi=98):
    return max(lo, min(hi, int(round(v))))


def _share(an):
    tot = sum(an["oh_w"].values())
    return {o: an["oh_w"][o] / tot for o in OHANG_LIST}


def score_label(v):
    if v >= 82:
        return "천생연분급 — 서로를 크게 채워주는 조합"
    if v >= 70:
        return "좋은 궁합 — 함께할수록 시너지가 나는 조합"
    if v >= 55:
        return "무난한 궁합 — 서로 이해하면 안정적인 조합"
    if v >= 42:
        return "노력이 필요한 궁합 — 다름을 조율할수록 깊어지는 조합"
    return "부딪힘이 잦은 궁합 — 거리 조절과 배려가 꼭 필요한 조합"


def analyze_pair(c1, a1, c2, a2):
    n1, n2 = c1["name"] or "사람1", c2["name"] or "사람2"
    p1, p2 = c1["pillars"], c2["pillars"]
    good, bad, detail = [], [], {}
    cats = {}

    # 1) 일간 케미
    ds1, ds2 = a1["ds"], a2["ds"]
    base = 55
    notes = []
    pair = frozenset({ds1, ds2})
    if pair in _GAN_HAP:
        base += 30
        t = f"두 사람의 일간 {GAN[ds1]}·{GAN[ds2]}이(가) 서로 끌려서 하나로 합쳐지는 사이(천간합, {_GAN_HAP[pair]}) — 처음 만났을 때부터 이유 없이 끌리고, 서로 맞춰 주려는 마음이 자연스럽게 생기는 '운명의 짝꿍' 같은 인연이에요. 편하다고 고마움 표현을 줄이지만 않으면 오래 가요"
        notes.append(t); good.append(f"두 사람의 일간 {GAN[ds1]}·{GAN[ds2]}이(가) 서로 끌려서 하나가 되는 사이(천간합) — 처음부터 이유 없이 끌리는 '운명의 짝꿍' 같은 인연이에요")
    elif pair in _GAN_CHUNG:
        base -= 18
        t = f"일간 {GAN[ds1]}·{GAN[ds2]}이(가) 정면으로 맞붙는 사이(천간충) — 생각과 행동 방식이 정반대라 말투·결정 방식에서 부딪히기 쉬워요. 대신 서로 없는 면을 배울 수 있는 관계라서, '누가 맞나'보다 '왜 그렇게 생각했나'를 먼저 물어보는 게 중요해요"
        notes.append(t); bad.append(f"일간 {GAN[ds1]}·{GAN[ds2]}이(가) 정면으로 맞붙는 사이(천간충) — 생각과 행동 방식이 정반대라 말투·결정 방식에서 부딪히기 쉬워요")
    else:
        o1, o2 = a1["dso"], a2["dso"]
        if o1 == o2:
            base += 6
            t = f"일간 오행이 같은 {o1} — 성향과 가치관이 닮아서 말이 잘 통하고 편안해요. 다만 단점도 닮아서 같이 고집을 부리거나 같이 지치기 쉬워서, 새로운 자극을 일부러 만들어 주면 좋아요"
            notes.append(t); good.append(f"일간 오행이 같은 {o1} — 성향이 닮아서 말이 잘 통하고 편안해요")
        elif SAENG[o1] == o2 or SAENG[o2] == o1:
            base += 14
            giver, taker = (n1, n2) if SAENG[o1] == o2 else (n2, n1)
            t = f"일간 오행이 서로 살려 주는 사이(상생) — {giver}님의 기운이 {taker}님을 북돋워 주는 사이예요. {taker}님은 곁에 있으면 힘이 나고, {giver}님은 계속 주다 지치지 않게 고마움을 돌려받는 게 중요해요"
            notes.append(t); good.append(f"일간 오행이 서로 살려 주는 사이(상생) — {giver}님의 기운이 {taker}님을 북돋워 줘요")
        else:
            base -= 10
            t = f"일간 오행이 서로 누르는 사이(상극, {o1}↔{o2}) — 한쪽이 무심코 한 말이 다른 쪽에게는 압박으로 느껴지기 쉬워요. 적당한 긴장감은 서로를 성장시키지만, 말투를 부드럽게 하고 서운한 건 바로 말하는 배려가 필요해요"
            notes.append(t); bad.append(f"일간 오행이 서로 누르는 사이(상극, {o1}↔{o2}) — 한쪽의 무심한 말이 다른 쪽에게 압박으로 느껴지기 쉬워요")
    g12 = ten_god(ds1, ds2)
    g21 = ten_god(ds2, ds1)
    b1, b2 = _lover_bonus(c1["gender"], g12[0]), _lover_bonus(c2["gender"], g21[0])
    base += b1 + b2
    notes.append(f"{n1} 입장에서 {josa(n2, '은', '는')} {LOVER_TEXT[g12[0]]}")
    notes.append(f"{n2} 입장에서 {josa(n1, '은', '는')} {LOVER_TEXT[g21[0]]}")
    if b1 + b2 >= 20:
        good.append(f"서로가 서로에게 '이상적인 배우자감'으로 보이는 관계예요 ({n1}→{n2}: {g12[0]}, {n2}→{n1}: {g21[0]})")
    elif b1 + b2 <= 2:
        bad.append(f"서로를 보는 기운이 '배우자감'과는 거리가 있어서, 연인보다 친구·동료 같은 느낌이 강할 수 있어요 ({g12[0]}/{g21[0]})")
    cats["일간 케미 (성향·끌림)"] = _clamp(base)
    detail["일간 케미 (성향·끌림)"] = notes

    # 2) 배우자궁(일지)
    d, items = _rel_delta(p1["day"][1], p2["day"][1], 1.0)
    notes = []
    for kind, label, dv in items:
        t = _pair_rel_text("day", p1["day"][1], p2["day"][1], kind, label) + (" " + _missing_note(c1, c2, "day", p1["day"][1], p2["day"][1]) if kind == "반합" else "")
        notes.append(f"{t} ({dv:+d})")
        (good if dv > 0 else bad if dv < 0 else good).append(_pair_rel_short("day", p1["day"][1], p2["day"][1], kind, label))
    if not items:
        notes.append("일지 사이에 특별히 끌리거나 부딪히는 관계는 없어서 평온한 편이에요 (±0)")
    cats["배우자궁 (일지·생활 궁합)"] = _clamp(55 + d)
    detail["배우자궁 (일지·생활 궁합)"] = notes

    # 3) 월지
    d, items = _rel_delta(p1["month"][1], p2["month"][1], 0.7)
    notes = []
    for kind, label, dv in items:
        t = _pair_rel_text("month", p1["month"][1], p2["month"][1], kind, label) + (" " + _missing_note(c1, c2, "month", p1["month"][1], p2["month"][1]) if kind == "반합" else "")
        notes.append(f"{t} ({dv:+d})")
        (good if dv > 0 else bad if dv < 0 else good).append(_pair_rel_short("month", p1["month"][1], p2["month"][1], kind, label))
    if not items:
        notes.append("월지 사이에 특별히 끌리거나 부딪히는 관계는 없어요 (±0)")
    if frozenset({p1["month"][0], p2["month"][0]}) in _GAN_HAP:
        d += 6
        notes.append("월간끼리 천간합 — 일·사회적 관심사가 잘 통해요 (+6)")
        good.append("월간 글자끼리 서로 끌리는 사이(천간합)라서 일·사회적 가치관이 잘 통해요")
    cats["월지 (가치관·사회적 궁합)"] = _clamp(55 + d)
    detail["월지 (가치관·사회적 궁합)"] = notes

    # 4) 오행 보완 / 용신
    s1, s2 = _share(a1), _share(a2)
    sc = 50
    notes = []
    for o in OHANG_LIST:
        if s1[o] < 0.10 and s2[o] >= 0.22:
            sc += 9
            t = f"{n1}님에게 부족한 {o}({OH_HANJA[o]}) 기운을 {n2}님이 채워 줘요"
            notes.append(t + " (+9)"); good.append(t)
        if s2[o] < 0.10 and s1[o] >= 0.22:
            sc += 9
            t = f"{n2}님에게 부족한 {o}({OH_HANJA[o]}) 기운을 {n1}님이 채워 줘요"
            notes.append(t + " (+9)"); good.append(t)
        if s1[o] >= 0.34 and s2[o] >= 0.34:
            sc -= 7
            t = f"두 사람 모두 {o}({OH_HANJA[o]}) 기운이 과해서 같은 부분이 더 강해지거나 같은 약점이 겹칠 수 있어요"
            notes.append(t + " (−7)"); bad.append(t)
    y1, y2 = a1["yong"][0][1], a2["yong"][0][1]
    for who, other, y, sh in ((n1, n2, y1, s2), (n2, n1, y2, s1)):
        if sh[y] >= 0.25:
            sc += 12
            t = f"{who}님에게 필요한 {y}({OH_HANJA[y]}) 기운이 {other}님에게 풍부해서 곁에 있으면 힘이 돼요"
            notes.append(t + " (+12)"); good.append(t)
        elif sh[y] >= 0.18:
            sc += 6
            t = f"{who}님에게 필요한 {y}({OH_HANJA[y]}) 기운을 {other}님이 어느 정도 가지고 있어요"
            notes.append(t + " (+6)"); good.append(t)
        elif sh[y] < 0.06:
            sc -= 3
            notes.append(f"{who}님에게 필요한 {y}({OH_HANJA[y]}) 기운은 {other}님에게 거의 없어 함께 채우는 활동이 필요해요 (−3)")
    if not notes:
        notes.append("오행의 보완·과다 관계가 뚜렷하지 않아요 (±0)")
    cats["오행 보완 (서로 채워주는 정도)"] = _clamp(sc)
    detail["오행 보완 (서로 채워주는 정도)"] = notes

    # 5) 띠
    d, items = _rel_delta(p1["year"][1], p2["year"][1], 0.6)
    notes = []
    for kind, label, dv in items:
        t = _pair_rel_text("year", p1["year"][1], p2["year"][1], kind, label) + (" " + _missing_note(c1, c2, "year", p1["year"][1], p2["year"][1]) if kind == "반합" else "")
        notes.append(f"{t} ({dv:+d})")
        (good if dv > 0 else bad if dv < 0 else good).append(_pair_rel_short("year", p1["year"][1], p2["year"][1], kind, label))
    if not items:
        notes.append("띠 사이에 특별히 끌리거나 부딪히는 관계는 없어요 (±0)")
    cats["띠 궁합 (연지)"] = _clamp(55 + d)
    detail["띠 궁합 (연지)"] = notes

    weights = {"일간 케미 (성향·끌림)": 0.25, "배우자궁 (일지·생활 궁합)": 0.25, "월지 (가치관·사회적 궁합)": 0.15,
               "오행 보완 (서로 채워주는 정도)": 0.20, "띠 궁합 (연지)": 0.15}
    total = _clamp(sum(cats[k] * weights[k] for k in weights), 10, 97)

    # 시지(자녀·말년) 참고
    extra = []
    if p1.get("hour") and p2.get("hour"):
        for kind, label in branch_relations(p1["hour"][1], p2["hour"][1]):
            extra.append(_pair_rel_text("hour", p1["hour"][1], p2["hour"][1], kind, label) + (" " + _missing_note(c1, c2, "hour", p1["hour"][1], p2["hour"][1]) if kind == "반합" else "") + " (점수에는 반영하지 않는 참고 항목이에요.)")
    # 힘의 균형
    order = ["극신약", "신약", "중화", "신강", "극신강"]
    gap = order.index(a1["grade"]) - order.index(a2["grade"])
    if abs(gap) >= 2:
        strong, weak = (n1, n2) if gap > 0 else (n2, n1)
        balance = f"{strong}의 기운이 더 강해 관계를 주도하기 쉽고, {josa(weak, '은', '는')} 맞춰주는 쪽이 되기 쉬워요. 의사결정에서 {weak}의 의견도 충분히 반영해야 균형이 맞습니다."
    elif abs(gap) == 1:
        balance = "두 사람의 기운 세기가 비슷한 편이라 큰 쏠림 없이 균형을 잡기 좋아요."
    else:
        balance = "두 사람의 기운 세기가 비슷해 대등한 관계가 되기 쉽습니다. 다만 둘 다 양보가 필요한 순간에는 누군가 먼저 한 걸음 물러서는 연습이 필요해요."
    return {"names": (n1, n2), "total": total, "label": score_label(total), "cats": cats, "detail": detail,
            "good": good, "bad": bad, "extra": extra, "balance": balance, "s1": s1, "s2": s2, "y": (y1, y2)}


# ---------------------------------------------------------------------
#  궁합 - 재물·자녀·가정 추가 풀이
# ---------------------------------------------------------------------
_PAIR_MONEY = {
    frozenset({"저축형"}): "둘 다 차곡차곡 모으는 스타일이라 살림이 안정적이에요. 다만 너무 아끼기만 하면 즐거움이 줄 수 있으니 '같이 쓰는 날'을 정해 보세요.",
    frozenset({"저축형", "굴리기형"}): "한 사람은 모으고 한 사람은 굴리는 조합이라 서로 보완이 돼요. 투자 금액의 한도를 미리 정해 두면 다툼이 줄어요.",
    frozenset({"저축형", "나눔형"}): "한 사람은 모으고 한 사람은 베푸는 편이라 씀씀이 문제로 서운할 수 있어요. 생활비 통장과 각자 용돈 통장을 나누면 좋아요.",
    frozenset({"저축형", "무관심형"}): "한 사람이 살림을 챙기고 다른 사람은 맡기는 구조라 편해요. 다만 한쪽에만 짐이 쏠리지 않게 가계 현황을 함께 공유하세요.",
    frozenset({"굴리기형"}): "둘 다 크게 움직이는 스타일이라 기회는 많지만 손실도 커질 수 있어요. 생활비·비상금은 따로 묶어 두고 투자하세요.",
    frozenset({"굴리기형", "나눔형"}): "돈이 크게 움직이고 새기도 쉬운 조합이에요. 큰 지출은 꼭 둘이 상의하고, 정기적으로 자산을 점검하세요.",
    frozenset({"굴리기형", "무관심형"}): "한 사람이 돈을 굴리고 다른 사람은 맡기는 구조예요. 맡기는 쪽도 현황은 알고 있어야 믿음이 오래가요.",
    frozenset({"나눔형"}): "둘 다 사람과 모임에 쓰는 일이 많은 조합이라 모이는 돈이 적을 수 있어요. 먼저 저축할 금액을 떼어 놓고 쓰는 습관이 필요해요.",
    frozenset({"나눔형", "무관심형"}): "돈이 모이기보다 쓰이기 쉬운 조합이에요. 자동이체 저축 같은 장치를 꼭 만들어 두세요.",
    frozenset({"무관심형"}): "둘 다 돈에 큰 관심이 없어서 갈등은 적지만 모이는 속도도 느려요. 목표 금액을 정하고 함께 점검하는 날을 만들어 보세요.",
}
_PAIR_MONEY_DIR = {
    "재성": "재물 기운을 가져다주는 상대라, 함께하면 돈의 흐름이 좋아지기 쉬워요",
    "비겁": "돈을 두고 비교하거나 나눠 쓰기 쉬운 상대라, 돈 문제는 투명하게 공유하는 게 좋아요",
    "식상": "내가 아낌없이 베풀게 되는 상대라, 퍼주기만 하지 않도록 선을 정해 두면 좋아요",
    "인성": "뒤에서 든든하게 받쳐 주는 상대라, 경제적으로 의지가 되기 쉬워요",
    "관성": "책임감과 긴장을 주는 상대라, 돈 관리에서 서로 규칙을 정하면 좋아요",
}


# ---------------------------------------------------------------------
#  궁합 상세 풀이 (v2.2) : 쉬운 말 + 자세한 설명
# ---------------------------------------------------------------------
K_GAN = "일간 케미 (성향·끌림)"
K_DAY = "배우자궁 (일지·생활 궁합)"
K_MON = "월지 (가치관·사회적 궁합)"
K_OH = "오행 보완 (서로 채워주는 정도)"
K_YEAR = "띠 궁합 (연지)"

JI_ANIMAL = ["쥐", "소", "호랑이", "토끼", "용", "뱀", "말", "양", "원숭이", "닭", "개", "돼지"]
POS_LONG = {"year": "연", "month": "월", "day": "일", "hour": "시"}
POS_AREA = {"year": "집안 분위기·바깥에서 보이는 이미지", "month": "일·돈·사회생활", "day": "배우자·내 속마음", "hour": "자녀·말년"}

PAIR_POS_INFO = {
    "day": ("일지(배우자 자리)", "함께 생활할 때의 편안함, 애정 표현, 생활 습관"),
    "month": ("월지(사회생활·가치관 자리)", "일·돈·미래 계획을 바라보는 생각"),
    "year": ("연지(띠·집안 자리)", "양가 집안 분위기와 가족·어른과의 관계"),
    "hour": ("시지(자녀·말년 자리)", "아이를 대하는 방식과 노후 계획"),
}
PAIR_KIND_PLAIN = {
    "육합": "두 글자가 짝꿍처럼 딱 붙는 사이(육합)예요. 자석처럼 자연스럽게 끌리고, 함께 있으면 편안함과 정을 느끼기 쉬워요.",
    "반합": "세 글자가 모여야 완성되는 한 팀에서 두 글자가 먼저 만난 상태(반합)예요. 서로 뭉치고 돕고 싶은 마음은 있지만, 마지막 한 글자가 없어서 '거의 다 맞는데 뭔가 하나 아쉬운' 느낌이 들 수 있어요. 빠진 글자가 들어오는 해나 시기, 또는 둘이 함께 만드는 공동 목표가 그 빈자리를 채워 줘요.",
    "방합": "같은 계절의 글자끼리 만난 사이(방합)예요. 성향과 분위기가 닮아서 편하고 말이 통해요. 다만 한쪽 기운이 지나치게 커져서 생각이 한쪽으로 쏠릴 수 있어요.",
    "충": "마주 보고 정면으로 부딪히는 사이(충)예요. 처음엔 강하게 끌리기도 하지만 생각과 생활 방식이 정반대라 의견이 자주 갈리고, 한번 부딪히면 크게 터지기 쉬워요. 거꾸로 말하면 서로에게 없는 면을 배울 수 있는 관계이기도 해요.",
    "형": "서로 모르는 사이에 압박과 불편함을 주고받는 사이(형)예요. 큰 싸움보다는 말투나 태도 때문에 자꾸 마음이 상하는 식으로 나타나요.",
    "해": "겉으로는 괜찮아 보여도 마음속에 서운함이 조금씩 쌓이는 사이(해)예요. 오해가 생기기 쉬워서 서운한 건 그때그때 말하는 게 중요해요.",
    "파": "잘 가다가도 계획이나 약속이 자꾸 어긋나는 사이(파)예요. 큰 문제는 아니지만 일정이 틀어지거나 마음이 변덕스러워질 수 있어요.",
    "원진": "이유 없이 얄미운데 또 신경이 쓰이는 '애증' 사이(원진)예요. 사소한 일에 마음이 상하다가도 막상 떨어지면 허전해지는 관계예요.",
    "같은 지지": "같은 글자라서 서로를 거울처럼 보는 사이예요. 편하고 말이 잘 통하지만 단점도 똑같이 닮아서 같이 빠지기 쉬워요.",
}
PAIR_POS_GOOD = {
    "day": "그래서 같이 살거나 자주 만날수록 마음이 편하고, 말하지 않아도 통하는 순간이 많아요.",
    "month": "그래서 일·돈·미래 계획 같은 현실적인 이야기를 나눌 때 의견이 잘 맞는 편이에요.",
    "year": "그래서 양가 가족이나 어른들과의 관계, 집안 분위기에서 서로를 이해하기 쉬워요.",
    "hour": "그래서 아이 이야기나 노후 계획을 나눌 때 마음이 잘 맞는 편이에요.",
}
PAIR_POS_BAD = {
    "day": "그래서 함께 생활할 때 정리, 시간 약속, 말투 같은 사소한 습관에서 마찰이 생기기 쉬워요.",
    "month": "그래서 돈 쓰는 방식, 일에 대한 태도, 미래 계획에서 의견이 갈리기 쉬워요.",
    "year": "그래서 양가 가족이나 지인 관계, 집안 분위기 차이에서 불편함이 생기기 쉬워요.",
    "hour": "그래서 아이 교육 방식이나 노후 계획에서 의견 차이가 생기기 쉬워요.",
}
PAIR_TIP = {
    "육합": "이 끌림은 큰 자산이에요. 편하다고 당연하게 여기지 말고 고마움을 자주 표현해서 더 단단하게 만드세요.",
    "반합": "함께하는 시간을 늘리고 둘만의 공동 목표(여행, 저축, 취미 등)를 하나 만들면 부족한 한 글자 역할을 해 줘요.",
    "방합": "닮은 점이 많은 만큼, 일부러 다른 시각을 들어 보는 시간을 만들면 좋아요.",
    "충": "화가 났을 때 바로 반응하지 말고 하루쯤 시간을 둔 뒤 이야기하세요. '내가 맞다'보다 '너는 그렇게 느꼈구나'를 먼저 말해 주면 크게 도움이 돼요.",
    "형": "말투를 부드럽게 다듬는 것이 핵심이에요. 지적할 때는 칭찬을 먼저 하고, 명령 대신 부탁하는 말투로 바꿔 보세요.",
    "해": "서운함을 참았다가 한꺼번에 터뜨리지 말고, 그날그날 '나 이게 조금 서운했어'라고 짧게 말하는 습관을 들이세요.",
    "파": "중요한 약속은 메모나 알림으로 같이 확인하고, 계획이 바뀌면 이유를 먼저 설명해 주세요.",
    "원진": "이유 없이 미울 때는 '지금 내 컨디션 때문인가?'를 먼저 생각해 보세요. 가끔 서로 거리를 두는 시간도 도움이 돼요.",
    "같은 지지": "비슷한 약점이 겹치는 부분(예: 늦잠, 지출 습관)은 서로 알림을 해 주는 규칙을 만들면 좋아요.",
}
KIND_SHORT = {
    "육합": "좋은 인연·협력이 생기기 쉬워요", "삼합": "뭉치는 힘이 커져요", "반합": "뭉치려는 힘은 있지만 완성되기엔 한 글자가 모자라요",
    "방합": "같은 기운이 더 커져요", "충": "변화·이동·다툼이 생기기 쉬워요", "형": "스트레스·구설에 주의하세요",
    "해": "서운함·오해에 주의하세요", "파": "계획이 틀어질 수 있어요", "원진": "이유 없이 신경 쓰이는 일에 주의하세요",
    "천간합": "새로운 인연이나 결합의 기운이에요", "천간충": "의견 충돌과 변화에 주의하세요",
}


PAIR_KIND_ONE = {
    "육합": "짝꿍처럼 딱 붙는 사이라 자연스럽게 끌리고 편안해요",
    "반합": "뭉치려는 마음은 있지만 빠진 한 글자가 있어서 완성되기 전 단계예요",
    "방합": "성향이 닮아서 편하지만 한쪽으로 쏠리기 쉬워요",
    "충": "정면으로 부딪히는 사이라 의견 충돌이 잦을 수 있어요",
    "형": "말투·태도 때문에 자꾸 마음이 상하기 쉬워요",
    "해": "서운함이 조금씩 쌓이기 쉬워요",
    "파": "계획이나 약속이 어긋나기 쉬워요",
    "원진": "이유 없이 얄미우면서도 신경 쓰이는 애증의 사이예요",
    "같은 지지": "같은 글자라 편하지만 단점도 닮았어요",
}


def _pair_rel_short(pos, a, b, kind, label):
    title, area = PAIR_POS_INFO[pos]
    return f"{title} {JI[a]}·{JI[b]}: {label} — {PAIR_KIND_ONE.get(kind, '')} (자세한 풀이는 아래 해당 항목에 있어요)"


def _pair_rel_text(pos, a, b, kind, label):
    title, area = PAIR_POS_INFO[pos]
    good = REL_GOOD.get(kind, True)
    plain = PAIR_KIND_PLAIN.get(kind, REL_DESC.get(kind, ""))
    mean = (PAIR_POS_GOOD if good else PAIR_POS_BAD)[pos]
    tip = PAIR_TIP.get(kind, "")
    return f"{title} {JI[a]}·{JI[b]}: {label}. {plain} ({area}) {mean} ▶ 이렇게 해 보세요: {tip}"


CAT_PLAIN = {
    K_GAN: ("나 자신을 뜻하는 글자(일간)끼리의 관계예요. 첫인상·끌림·성격이 맞는 정도를 봐요.",
            "성향이 잘 맞고 서로 끌리는 편이에요.", "크게 맞지도 어긋나지도 않는 무난한 사이예요.", "성향 차이가 큰 편이라 서로를 이해하는 시간이 필요해요."),
    K_DAY: ("배우자 자리(일지)끼리의 관계예요. 같이 살 때의 편안함과 생활 궁합을 봐요.",
            "함께 지내면 마음이 편하고 생활 리듬이 잘 맞아요.", "생활 방식은 무난하게 맞춰 갈 수 있어요.", "생활 습관이나 애정 표현 방식에서 어긋남이 있을 수 있어요."),
    K_MON: ("사회생활·가치관 자리(월지)끼리의 관계예요. 일, 돈, 미래 계획을 보는 눈이 맞는 정도를 봐요.",
            "일과 돈, 미래 계획에서 생각이 잘 통해요.", "가치관이 크게 부딪히지는 않아요.", "일·돈·미래 계획에 대한 생각이 달라서 미리 맞춰 두는 것이 좋아요."),
    K_OH: ("두 사람이 가진 기운(오행)이 서로의 빈 곳을 채워 주는 정도예요.",
           "서로에게 없는 기운을 채워 줘서 함께 있으면 힘이 나요.", "서로 크게 채워 주지도 겹치지도 않는 편이에요.", "같은 기운이 겹치거나 서로 채워 주는 부분이 적어서 의식적인 보완이 필요해요."),
    K_YEAR: ("태어난 해의 띠(연지)끼리의 관계예요. 양가 집안, 가족 분위기와의 조화를 가볍게 봐요.",
             "집안 분위기나 가족 관계가 자연스럽게 어울려요.", "띠로는 특별히 맞거나 어긋나지 않아요.", "가족·집안 문제에서 의견이 갈릴 수 있으니 서로 이해하려는 노력이 필요해요."),
}


def _cat_tier(k, v):
    t = CAT_PLAIN[k]
    return t[1] if v >= 70 else t[2] if v >= 50 else t[3]


def _top_group(a):
    return max(a["ss_w"], key=a["ss_w"].get)


def _ilgan_relation(a1, a2, n1, n2):
    ds1, ds2 = a1["ds"], a2["ds"]
    pair = frozenset({ds1, ds2})
    if pair in _GAN_HAP:
        return "합", None, None
    if pair in _GAN_CHUNG:
        return "충", None, None
    o1, o2 = a1["dso"], a2["dso"]
    if o1 == o2:
        return "같음", None, None
    if SAENG[o1] == o2:
        return "상생", n1, n2
    if SAENG[o2] == o1:
        return "상생", n2, n1
    if GEUK[o1] == o2:
        return "상극", n1, n2
    return "상극", n2, n1


def _ilgan_paras(kind, g, t, o1, n1, n2):
    if kind == "합":
        return ["두 사람의 일간(나 자신을 뜻하는 글자)이 '천간합'이라는, 서로 끌려서 하나가 되는 관계예요. 쉽게 말하면 '운명의 짝꿍' 같은 조합이라서, 처음 만났을 때부터 이유 없이 편하거나 끌리는 느낌을 받기 쉬워요.",
                "서로 성격이 달라도 상대에게 맞춰 주려는 마음이 자연스럽게 생겨요. 다만 '이 사람은 당연히 내 편'이라고 생각해서 고마움 표현이 줄어들면 금방 식을 수 있으니, 고맙다는 말은 계속 해 주세요."]
    if kind == "충":
        return ["두 사람의 일간이 '천간충'이에요. 서로 정반대 방향으로 힘을 쓰는 글자라서 생각하는 방식과 행동 속도가 다른 편이에요.",
                "처음엔 '나와 다른 매력'에 끌리기도 하지만, 가까워질수록 말투·결정 방식·속도 차이에서 부딪히기 쉬워요. 그래도 서로에게 없는 면을 배울 수 있는 관계예요. '누가 맞나'를 따지지 말고 '왜 그렇게 생각했는지'를 먼저 물어보세요."]
    if kind == "같음":
        return [f"두 사람의 일간이 같은 {o1} 기운이에요. 성향과 가치관이 닮아서 '나랑 비슷하다'는 공감이 크고 말이 잘 통해요.",
                "대신 장점뿐 아니라 단점도 닮아서, 같은 부분에서 같이 지치거나 같이 고집을 부리기 쉬워요. 서로 다른 취미나 친구 관계를 인정해 주며 새로운 자극을 만들어 주면 좋아요."]
    if kind == "상생":
        return [f"두 사람의 일간 오행이 '상생' 관계예요. {g}님의 기운이 {t}님을 키워 주는 방향이라, {t}님은 {g}님 곁에서 힘을 얻고 편안함을 느끼기 쉬워요.",
                f"반대로 {g}님은 계속 주다 보면 지칠 수 있어요. {g}님은 '내가 더 주고 있다'는 서운함을 쌓아 두지 말고 이야기하고, {t}님은 받은 만큼 고마움과 행동으로 돌려주세요."]
    return [f"두 사람의 일간 오행이 '상극' 관계예요. {g}님의 기운이 {t}님을 누르는 방향이라, {g}님이 별 뜻 없이 한 말이나 행동도 {t}님에게는 압박으로 느껴질 수 있어요.",
            f"그렇다고 나쁜 궁합은 아니에요. 적당한 긴장감이 서로를 성장시키기도 해요. {g}님은 말투를 부드럽게, {t}님은 서운한 점을 참지 말고 바로 이야기해 주세요."]


PAIR_GOD_VIEW = {
    "비견": ("나와 비슷한 친구 같은 사람이에요. 대등하고 편하지만 서로 양보하지 않으면 고집 싸움이 될 수 있어요.", "누가 이기는지 따지기보다 역할을 나눠 보세요."),
    "겁재": ("라이벌이자 동료 같은 사람이에요. 자극은 되지만 비교하거나 돈 문제로 신경전이 생기기 쉬워요.", "비교하는 말은 줄이고 돈 문제는 미리 규칙을 정하세요."),
    "식신": ("내가 기분 좋게 챙겨 주고 싶은 사람이에요. 함께 있으면 여유롭고 먹고 즐기는 시간이 많아져요.", "받는 쪽도 고맙다는 표현을 자주 해 주세요."),
    "상관": ("내 안의 재능과 말솜씨를 끌어내는 사람이에요. 대화가 재밌지만 나도 모르게 지적하거나 날카로운 말이 나올 수 있어요.", "농담이라도 약점을 건드리는 말은 조심하세요."),
    "편재": ("나를 설레게 하고 활동 범위를 넓혀 주는 사람이에요. 매력적이지만 마음을 붙잡아 두기엔 변수가 많아요.", "약속과 연락 같은 기본적인 신뢰를 먼저 쌓으세요."),
    "정재": ("꾸준하고 믿음직하게 마음이 가는 사람이에요. 안정적인 만남이 되기 쉬워요.", "당연하게 여기지 말고 작은 이벤트로 설렘을 더해 주세요."),
    "편관": ("카리스마가 있어 강하게 끌리지만 부담과 압박도 주는 사람이에요. 내가 긴장하며 노력하게 돼요.", "너무 맞추기만 하지 말고 내 의견도 분명히 말하세요."),
    "정관": ("반듯하고 믿음이 가는 사람이에요. 예의 바르고 책임감 있게 대하게 돼요.", "너무 격식을 차리면 답답해지니 편한 모습도 보여 주세요."),
    "편인": ("독특하고 속을 알기 어려운 매력으로 나를 자극하는 사람이에요. 영감을 주지만 마음의 거리가 생기기 쉬워요.", "속마음을 추측하지 말고 직접 물어보세요."),
    "정인": ("나를 이해하고 보살펴 주는 따뜻한 사람이에요. 마음 놓고 기댈 수 있어요.", "기대기만 하지 말고 나도 챙겨 주는 모습을 보여 주세요."),
}
LOVE_STYLE = {
    "비겁": "주도권을 쉽게 내주지 않고 대등한 파트너를 원하는 연애 스타일이에요. 의지하기보다 함께 걸어가는 느낌을 좋아해요.",
    "식상": "말과 표현이 풍부한 연애 스타일이에요. 장난·애교·칭찬으로 마음을 표현하지만 기분 기복이 있거나 날카로운 한마디가 나올 때가 있어요.",
    "재성": "행동으로 챙기는 현실적인 연애 스타일이에요. 데이트 계획·선물·생활 챙기기를 잘하지만 가끔 계산적으로 보일 수 있어요.",
    "관성": "진중하고 책임감 있는 연애 스타일이에요. 마음을 천천히 열지만 한번 주면 오래가요. 체면 때문에 표현이 서툴 수 있어요.",
    "인성": "상대를 이해하고 보살피는 연애 스타일이에요. 마음이 깊고 헌신적이지만 걱정이 많고 속마음을 혼자 삭이는 편이에요.",
}
LOVE_LANG = {
    "비겁": "나를 존중하고 대등하게 대해 줄 때", "식상": "칭찬과 애정 표현을 말로 해 줄 때",
    "재성": "실질적으로 챙겨 주고 시간과 정성을 들여 줄 때", "관성": "약속을 지키고 믿음직하게 곁을 지켜 줄 때",
    "인성": "내 마음을 이해해 주고 편안하게 기댈 수 있게 해 줄 때",
}
TALK_STYLE = {
    "비겁": "자기 생각을 분명히 말하는 직설형이에요. 돌려 말하기보다 결론부터 말해요.",
    "식상": "말솜씨가 좋고 표현이 풍부한 수다형이에요. 생각나는 대로 말하다 보니 가끔 말이 앞서요.",
    "재성": "현실적이고 구체적으로 말하는 실용형이에요. 감정보다 '그래서 뭘 할 건데?'를 먼저 물어봐요.",
    "관성": "조심스럽고 예의를 갖춰 말하는 신중형이에요. 하고 싶은 말을 삼키다가 쌓아 두기도 해요.",
    "인성": "상대 말을 잘 들어 주는 경청형이에요. 속으로 생각이 많아서 말로 꺼내기까지 시간이 걸려요.",
}
TALK_WANT = {
    "비겁": "'네 생각을 존중해' '네가 정해도 좋아'", "식상": "'재밌다' '말을 참 잘한다' 같은 칭찬과 반응",
    "재성": "'덕분에 도움이 됐어' '챙겨 줘서 고마워'", "관성": "'믿음직하다' '네가 있어서 든든해'",
    "인성": "'네 마음 이해해' '괜찮아, 천천히 해도 돼'",
}
TALK_AVOID = {
    "비겁": "'네가 틀렸어' '내 말대로 해' 같은 명령이나 비교하는 말", "식상": "'말이 너무 많아' '또 그 소리야' 같이 표현을 막는 말",
    "재성": "'또 돈 얘기야' '너무 계산적이야' 같이 현실을 무시하는 말", "관성": "'왜 그렇게 답답해' '뭐 어때' 같이 체면과 책임을 가볍게 보는 말",
    "인성": "'생각이 너무 많아' '왜 말을 안 해' 같이 재촉하는 말",
}
ANGER = {
    "비겁": "화나면 목소리가 커지고 자기 주장을 더 세게 내세워요", "식상": "화나면 날카로운 말이 쏟아지거나 감정을 한꺼번에 터뜨려요",
    "재성": "화나면 따지듯이 이유와 잘잘못을 하나하나 짚어요", "관성": "화나면 말수가 줄고 싸늘해지며 속으로 오래 담아 둬요",
    "인성": "화나면 조용히 마음의 문을 닫고 혼자 생각에 잠겨요",
}
MAKEUP = {
    "비겁": "먼저 한 발 물러서서 '내가 너무 세게 말했다'고 인정하는 것", "식상": "감정이 가라앉은 뒤 차분히 다시 설명하고 사과하는 것",
    "재성": "잘잘못 대신 앞으로 어떻게 할지 현실적인 약속을 정하는 것", "관성": "시간을 조금 준 뒤 먼저 말을 걸어 마음을 열어 주는 것",
    "인성": "재촉하지 않고 곁에서 기다리며 '말할 준비 되면 말해 줘'라고 해 주는 것",
}
PARENT_ROLE = {
    "비겁": "친구처럼 놀아 주고 자립심을 키워 주는 역할", "식상": "감정 표현과 놀이, 칭찬을 맡는 역할",
    "재성": "생활 관리·교육비·일정을 챙기는 역할", "관성": "규칙과 안전, 훈육을 맡는 역할", "인성": "공부와 정서 돌봄을 맡는 역할",
}
PARENT_WARN = {
    "비겁": "아이와 고집 싸움이 되지 않게 주의", "식상": "기분에 따라 훈육이 들쑥날쑥하지 않게 주의",
    "재성": "성적·결과로만 평가하지 않게 주의", "관성": "너무 엄하게 몰아붙이지 않게 주의", "인성": "지나치게 감싸서 스스로 할 기회를 뺏지 않게 주의",
}
WORK_STRENGTH = {"비겁": "추진력·독립심·끈기", "식상": "아이디어·기획·표현력", "재성": "실행력·영업·돈 관리", "관성": "책임감·조직 관리·원칙", "인성": "분석·공부·꼼꼼한 준비"}
WORK_ROLE = {
    "비겁": "현장에서 밀어붙이는 실행 담당", "식상": "아이디어와 홍보를 맡는 기획 담당", "재성": "수익과 거래를 챙기는 영업·재무 담당",
    "관성": "일정과 규칙을 관리하는 운영 담당", "인성": "자료 조사와 품질을 챙기는 연구·검토 담당",
}
WORK_WARN = {
    "비겁": "자기 방식만 고집하지 않게 주의", "식상": "시작만 하고 마무리가 약해지지 않게 주의", "재성": "눈앞의 이익에만 치우치지 않게 주의",
    "관성": "융통성 없이 규칙만 내세우지 않게 주의", "인성": "준비만 길어지고 결정이 늦어지지 않게 주의",
}
WORK_COMBO = {
    frozenset({"비겁"}): "같은 스타일이라 속도가 잘 맞지만 주도권 다툼이 생기기 쉬워요. 맡을 영역을 먼저 나누세요.",
    frozenset({"식상"}): "아이디어는 넘치지만 마무리가 약할 수 있어요. 일정 관리 담당을 따로 정하세요.",
    frozenset({"재성"}): "수익 감각이 좋아서 성과가 나기 쉬워요. 이익 분배 기준을 처음부터 글로 정해 두세요.",
    frozenset({"관성"}): "원칙과 책임감이 강해 안정적이지만 융통성이 부족할 수 있어요. 새로운 시도를 하는 날을 정해 보세요.",
    frozenset({"인성"}): "신중하고 준비가 철저하지만 결정이 느려질 수 있어요. 결정 기한을 정해 두세요.",
    frozenset({"비겁", "식상"}): "한 사람은 추진하고 한 사람은 아이디어를 내는 조합이에요. 기술·창작 일에 잘 맞아요.",
    frozenset({"비겁", "재성"}): "경쟁 속에서 실속을 챙기는 조합이에요. 영업·사업에 강하지만 돈 문제는 투명하게 하세요.",
    frozenset({"비겁", "관성"}): "추진력과 조직 관리가 맞물리지만 주장과 규율이 부딪힐 수 있어요. 권한 범위를 정해 두세요.",
    frozenset({"비겁", "인성"}): "한 사람이 밀고 나가고 다른 사람이 든든히 받쳐 주는 조합이에요. 한 분야를 깊게 파기 좋아요.",
    frozenset({"식상", "재성"}): "재능이 돈으로 이어지는 조합이에요(식상생재). 사업·콘텐츠·창업에 좋아요.",
    frozenset({"식상", "관성"}): "자유로운 발상과 조직의 틀이 맞서는 조합이에요. 서로 존중하면 창의적이면서 안정적인 결과가 나와요.",
    frozenset({"식상", "인성"}): "배운 것을 가르치거나 콘텐츠로 풀어내는 데 잘 맞는 조합이에요.",
    frozenset({"재성", "관성"}): "돈과 지위를 함께 얻기 좋은 조합이에요. 안정적인 조직 운영과 관리·경영에 유리해요.",
    frozenset({"재성", "인성"}): "현실과 이상이 부딪히는 조합이라 의견이 갈리기 쉬워요. 전문성을 수익으로 연결하면 해법이 돼요.",
    frozenset({"관성", "인성"}): "신뢰와 학식으로 조직에서 인정받기 좋은 조합이에요. 교육·연구·전문직 협업에 잘 맞아요.",
}
OH_RHYTHM = {
    "목": "활동적이고 새로운 걸 시도하는 성장형 리듬이에요. 아침에 움직이고 배우는 시간을 좋아해요.",
    "화": "열정적이고 사교적인 활기형 리듬이에요. 사람을 만나고 움직일 때 에너지가 올라가며 밤늦게까지 깨어 있기 쉬워요.",
    "토": "규칙적이고 안정된 루틴형 리듬이에요. 정해진 식사·수면 시간을 중요하게 여겨요.",
    "금": "깔끔하고 정돈된 절제형 리듬이에요. 계획표와 정리정돈을 좋아하고 군더더기를 싫어해요.",
    "수": "여유롭고 생각이 깊은 자유형 리듬이에요. 혼자만의 시간과 충분한 수면·휴식이 꼭 필요해요.",
}


def _fmt_ji(lst):
    return "·".join(f"{JI[x]}({JI_H[x]})" for x in sorted(lst))


def _missing_note(c1, c2, pos, a, b):
    # 반합일 때 빠진 글자와, 그 글자를 상대가 가지고 있는지 안내
    for grp, label, wang in _SAMHAP:
        if a in grp and b in grp and a != b:
            miss = (grp - {a, b}).pop()
            have = []
            for nm, c in ((c1["name"] or "사람1", c1), (c2["name"] or "사람2", c2)):
                for k in ("year", "month", "day", "hour"):
                    if c["pillars"].get(k) and c["pillars"][k][1] == miss:
                        have.append(f"{nm}님의 {POS_LONG[k]}지")
            if have:
                return f"빠진 글자인 {JI[miss]}({JI_H[miss]})는 {', '.join(have)}에 있어서, 두 사람의 사주를 합쳐 보면 이 팀이 완성돼요. 서로 모자란 부분을 채워 주는 인연이라는 뜻이에요."
            return f"빠진 글자인 {JI[miss]}({JI_H[miss]})는 두 사람의 사주 어디에도 없어요. 그래서 {JI[miss]}에 해당하는 해나 대운(10년 흐름)이 들어올 때 이 힘이 완성된다고 봐요."
    return ""


def _pair_summary_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    kind, g, t = _ilgan_relation(a1, a2, n1, n2)
    arche = {
        "합": "서로 끌려서 하나가 되는 '자석형' 궁합",
        "상생": f"{g}님이 {t}님을 키워 주는 '든든한 서포터형' 궁합",
        "같음": "서로를 닮은 '거울형' 궁합",
        "충": "정반대라서 서로 자극이 되는 '밀고 당기기형' 궁합",
        "상극": f"{g}님이 {t}님을 이끄는 '긴장감 있는 자극형' 궁합",
    }[kind]
    cats = r["cats"]
    best = max(cats, key=cats.get)
    worst = min(cats, key=cats.get)
    blocks = [
        {"t": "p", "text": f"{n1}님과 {n2}님의 궁합 점수는 {r['total']}점이고, '{r['label']}'에 해당해요. 두 사람의 관계를 한마디로 하면 {arche}이에요."},
        {"t": "p", "text": f"가장 잘 맞는 부분은 '{best}'({cats[best]}점)이에요. {_cat_tier(best, cats[best])}"},
        {"t": "p", "text": f"가장 신경 써야 할 부분은 '{worst}'({cats[worst]}점)이에요. {_cat_tier(worst, cats[worst])}"},
        {"t": "p", "text": f"잘 맞는 점이 {len(r['good'])}가지, 조심할 점이 {len(r['bad'])}가지 발견됐어요. 아래에서 연애·결혼, 대화·싸움, 돈, 자녀, 가족, 일, 시기별 흐름 순서로 자세히 풀어 드릴게요."},
        {"t": "callout", "kind": "info", "text": "점수가 낮다고 안 맞는 사이는 아니고, 높다고 노력이 필요 없는 것도 아니에요. 점수는 '어느 부분을 더 신경 쓰면 좋은지' 알려 주는 안내판이라고 생각해 주세요."},
    ]
    return {"id": "pair_summary", "title": "한눈에 보는 총평", "open": True, "blocks": blocks}


def _pair_score_table(r):
    rows = []
    for k, v in r["cats"].items():
        rows.append([k, f"{v}점", CAT_PLAIN[k][0], _cat_tier(k, v)])
    return {"t": "table", "headers": ["항목", "점수", "이게 뭘 보는 건가요?", "이 점수가 뜻하는 것"], "rows": rows, "widths": [2, 1, 4, 4]}


def _pair_personality_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    blocks = []
    for n, a in ((n1, a1), (n2, a2)):
        gch = GAN[a["ds"]]
        top = _top_group(a)
        blocks.append({"t": "kv", "items": [
            (f"{n}님의 기본 성격", f"{gch}({a['dso']}) — {ILGAN_KEYWORD[gch]}"),
            ("성격 풀이", ILGAN_BLURB[gch]),
            ("기운의 세기", GRADE_PLAIN[a["grade"]]),
            ("가장 강한 성향", f"{GROUP_TAG[top]} — {GROUP_ONE_LINER[top]}")]})
    kind, g, t = _ilgan_relation(a1, a2, n1, n2)
    blocks.append({"t": "p", "text": "▶ 두 사람의 성격은 이렇게 만나요"})
    for ptxt in _ilgan_paras(kind, g, t, a1["dso"], n1, n2):
        blocks.append({"t": "p", "text": ptxt})
    g12 = ten_god(a1["ds"], a2["ds"])[0]
    g21 = ten_god(a2["ds"], a1["ds"])[0]
    v12, v21 = PAIR_GOD_VIEW[g12], PAIR_GOD_VIEW[g21]
    blocks.append({"t": "p", "text": "▶ 서로가 상대를 이렇게 느끼기 쉬워요"})
    blocks.append({"t": "bullets", "items": [
        f"{n1}님에게 {n2}님은 '{g12}' 느낌이에요. {v12[0]} (팁: {v12[1]})",
        f"{n2}님에게 {n1}님은 '{g21}' 느낌이에요. {v21[0]} (팁: {v21[1]})"]})
    blocks.append({"t": "p", "text": "▶ 힘의 균형: " + r["balance"]})
    return {"id": "pair_person", "title": "두 사람의 성격 비교", "open": True, "blocks": blocks}


def _pair_love_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    p1, p2 = c1["pillars"], c2["pillars"]
    blocks = []
    cats = r["cats"]
    blocks.append({"t": "p", "text": "▶ 처음 느끼는 끌림 (일간 관계)"})
    kind, g, t = _ilgan_relation(a1, a2, n1, n2)
    for ptxt in _ilgan_paras(kind, g, t, a1["dso"], n1, n2):
        blocks.append({"t": "p", "text": ptxt})
    blocks.append({"t": "p", "text": "▶ 함께 있을 때의 편안함 (배우자 자리 = 일지)"})
    rels = branch_relations(p1["day"][1], p2["day"][1])
    if rels:
        for kd, lab in rels:
            txt = _pair_rel_text("day", p1["day"][1], p2["day"][1], kd, lab)
            note = _missing_note(c1, c2, "day", p1["day"][1], p2["day"][1]) if kd == "반합" else ""
            blocks.append({"t": "p", "text": txt + (" " + note if note else "")})
    elif p1["day"][1] == p2["day"][1]:
        blocks.append({"t": "p", "text": _pair_rel_text("day", p1["day"][1], p2["day"][1], "같은 지지", f"같은 글자({JI[p1['day'][1]]})")})
    else:
        blocks.append({"t": "p", "text": "두 사람의 배우자 자리 사이에는 특별히 끌리거나 부딪히는 관계가 없어요. 큰 기복 없이 평온하게 지낼 수 있는 편이고, 애정은 두 사람이 얼마나 표현하느냐에 따라 달라져요."})
    blocks.append({"t": "p", "text": "▶ 각자의 연애 스타일"})
    rows = []
    for n, a in ((n1, a1), (n2, a2)):
        top = _top_group(a)
        rows.append([f"{n}님", LOVE_STYLE[top], LOVE_LANG[top]])
    blocks.append({"t": "table", "headers": ["이름", "연애할 때 모습", "사랑을 느끼는 순간"], "rows": rows, "widths": [1, 5, 3]})
    top1, top2 = _top_group(a1), _top_group(a2)
    blocks.append({"t": "bullets", "items": [
        f"{n1}님이 {n2}님에게 해 주면 좋은 것: {n2}님은 '{LOVE_LANG[top2]}' 사랑받는다고 느껴요.",
        f"{n2}님이 {n1}님에게 해 주면 좋은 것: {n1}님은 '{LOVE_LANG[top1]}' 사랑받는다고 느껴요."]})
    blocks.append({"t": "p", "text": "▶ 인연의 기운"})
    items = []
    for c, a, n in ((c1, a1, n1), (c2, a2, n2)):
        sg = _spouse_group(c)
        w = a["ss_w"][sg]
        items.append((f"{n}님의 연애·결혼 인연 기운", _star_text(_stars(w, [0.8, 1.8, 3.0, 4.5])) + " — " + _tier(w, [
            (3.0, "인연의 기회가 풍부한 편이에요"), (1.8, "인연이 자연스럽게 이어지는 편이에요"), (0.8, "신중하고 천천히 인연이 오는 편이에요")], "연애보다 일과 자기 성장에 에너지를 쓰는 시기가 길 수 있어요")))
    blocks.append({"t": "kv", "items": items})
    blocks.append({"t": "p", "text": "▶ 결혼·동거를 한다면"})
    day_score = cats[K_DAY]
    mon_score = cats[K_MON]
    blocks.append({"t": "p", "text": _tier(day_score, [
        (70, "생활 궁합이 좋은 편이라 함께 살면 안정감이 커요. 사소한 습관 차이만 미리 이야기해 두면 오래 편안하게 지낼 수 있어요."),
        (50, "생활 궁합은 무난한 편이에요. 집안일 분담, 수면·식사 시간, 쉬는 방식을 미리 합의해 두면 마찰이 줄어요.")],
        "생활 궁합은 조율이 필요한 편이에요. 결혼이나 동거 전에 집안일 분담, 돈 관리, 가족 모임 횟수 같은 현실적인 약속을 구체적으로 정해 두면 큰 도움이 돼요.")})
    blocks.append({"t": "p", "text": _tier(mon_score, [
        (70, "가치관 궁합도 좋아서 직업·돈·미래 계획을 이야기할 때 방향이 잘 맞아요."),
        (50, "가치관은 크게 부딪히지 않지만, 큰 결정 앞에서는 서로의 속도를 확인하세요.")],
        "가치관(일·돈·미래 계획)이 다를 수 있어요. 결혼 전에 직업, 저축 목표, 자녀 계획, 거주 지역에 대해 솔직하게 이야기해 보세요.")})
    sp1, sp2 = _future_years(a1, _spouse_group(c1)), _future_years(a2, _spouse_group(c2))
    ytxt = []
    if sp1:
        ytxt.append(f"{n1}님은 {_years_text(sp1)}")
    if sp2:
        ytxt.append(f"{n2}님은 {_years_text(sp2)}")
    if ytxt:
        blocks.append({"t": "p", "text": "▶ 인연이 움직이기 쉬운 해: " + " / ".join(ytxt) + ". 이 해에 연애·결혼 이야기가 나오거나 관계가 한 단계 달라지기 쉬워요."})
    return {"id": "pair_love", "title": "연애·결혼 궁합", "open": True, "blocks": blocks}


def _pair_talk_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    t1, t2 = _top_group(a1), _top_group(a2)
    blocks = [{"t": "p", "text": "사람마다 말하는 방식, 듣고 싶은 말, 화났을 때의 모습이 달라요. 각자 가장 강한 성향을 기준으로 정리했어요."}]
    rows = []
    for n, tg in ((n1, t1), (n2, t2)):
        rows.append([f"{n}님", TALK_STYLE[tg], TALK_WANT[tg], TALK_AVOID[tg]])
    blocks.append({"t": "table", "headers": ["이름", "말하는 방식", "듣고 싶은 말", "피해야 할 말"], "rows": rows, "widths": [1, 4, 3, 3]})
    blocks.append({"t": "p", "text": "▶ 싸웠을 때는 이런 모습이 되기 쉬워요"})
    rows = [[f"{n}님", ANGER[tg], MAKEUP[tg]] for n, tg in ((n1, t1), (n2, t2))]
    blocks.append({"t": "table", "headers": ["이름", "화났을 때", "마음이 풀리는 방법"], "rows": rows, "widths": [1, 4, 4]})
    if t1 == t2:
        blocks.append({"t": "p", "text": "두 사람이 비슷한 방식으로 화를 내서 같이 폭발하거나 같이 입을 닫기 쉬워요. 한 명이라도 먼저 '잠깐 쉬었다가 얘기하자'고 말하는 규칙을 만들어 두세요."})
    else:
        blocks.append({"t": "p", "text": f"{n1}님은 '{ANGER[t1]}' 쪽이고, {n2}님은 '{ANGER[t2]}' 쪽이라서 서로의 반응을 오해하기 쉬워요. 상대가 화났을 때의 모습은 '나를 싫어해서'가 아니라 '원래 그런 방식'이라고 이해해 주면 싸움이 훨씬 짧아져요."})
    topics = []
    for k, label_ in ((K_DAY, "집안일·생활 습관·애정 표현"), (K_MON, "돈·일·미래 계획"), (K_YEAR, "양가 가족·집안 문제"), (K_GAN, "말투·결정 방식·성격 차이")):
        if r["cats"][k] < 50:
            topics.append(label_)
    if topics:
        blocks.append({"t": "p", "text": "▶ 두 사람이 자주 부딪히기 쉬운 주제: " + ", ".join(topics) + ". 이 주제는 감정이 올라온 상태에서 이야기하지 말고, 차분할 때 미리 규칙을 정해 두세요."})
    else:
        blocks.append({"t": "p", "text": "▶ 특별히 자주 부딪히는 주제는 보이지 않아요. 그래도 사소한 서운함이 쌓이지 않게 주 1회 짧은 대화 시간을 가져 보세요."})
    blocks.append({"t": "p", "text": "▶ 싸움을 줄이는 5가지 약속"})
    blocks.append({"t": "bullets", "items": [
        "화가 났을 땐 '지금 말하면 후회할 것 같아. 30분 뒤에 얘기하자'라고 먼저 말하기",
        "'항상', '맨날', '너는 원래' 같은 단정하는 말 쓰지 않기",
        "지적하기 전에 상대가 한 일 중 고마운 점 한 가지 먼저 말하기",
        "서운한 일은 3일을 넘기지 않고 그때그때 짧게 이야기하기",
        "싸운 날에도 '잘 자'나 '밥은 먹었어?' 같은 기본 인사는 이어가기"]})
    return {"id": "pair_talk", "title": "대화·갈등 궁합 (이렇게 말하고, 이렇게 싸워요)", "open": True, "blocks": blocks}


def _pair_money_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    s1, t1 = _money_style(a1)
    s2, t2 = _money_style(a2)
    key = frozenset({s1, s2})
    txt = _PAIR_MONEY.get(key, "한 사람이 균형형이라 상대의 방식에 잘 맞춰 줄 수 있어요. 큰 지출은 함께 상의한다는 규칙만 있으면 무난해요.")
    g12 = ten_god(a1["ds"], a2["ds"])[1]
    g21 = ten_god(a2["ds"], a1["ds"])[1]
    blocks = [{"t": "kv", "items": [(n1, f"{s1} — {t1}"), (n2, f"{s2} — {t2}")]},
              {"t": "p", "text": txt},
              {"t": "bullets", "items": [f"{n1}님에게 {n2}님은 {_PAIR_MONEY_DIR[g12]}.", f"{n2}님에게 {n1}님은 {_PAIR_MONEY_DIR[g21]}."]}]
    n_good = sum(1 for a in (a1, a2) if a["ss_w"]["재성"] >= 1.8)
    if n_good == 2:
        blocks.append({"t": "p", "text": "두 사람 모두 돈의 기운이 있어서, 합치면 재물 기회가 많은 조합이에요. 대신 지출도 커지기 쉬우니 공동 예산을 세우세요."})
    elif n_good == 1:
        blocks.append({"t": "p", "text": "한 사람이 돈의 기운을 더 많이 갖고 있어요. 그 사람이 돈 흐름을 이끌고, 다른 사람은 꼼꼼한 점검 역할을 맡으면 균형이 맞아요."})
    else:
        blocks.append({"t": "p", "text": "두 사람 모두 돈의 기운이 크지 않아요. 큰 한 방을 노리기보다 함께 목표를 세워 꾸준히 모으는 방식이 안전해요."})
    # 역할 분담
    def mscore(a, s):
        v = a["ss_w"]["재성"]
        if s in ("저축형", "균형형"):
            v += 1.0
        if s in ("무관심형", "나눔형"):
            v -= 1.0
        return v
    m1, m2 = mscore(a1, s1), mscore(a2, s2)
    mgr, oth = (n1, n2) if m1 >= m2 else (n2, n1)
    blocks.append({"t": "p", "text": "▶ 가계 역할 분담"})
    blocks.append({"t": "p", "text": f"가계 관리는 {mgr}님이 맡는 편이 더 잘 맞아요. {oth}님은 큰 지출이 있을 때 의견을 내고, 한 달에 한 번 함께 통장을 보며 점검하는 방식이 좋아요. 한 사람에게만 돈 관리를 맡기면 부담과 불신이 쌓이기 쉬워서 '맡기되 공유하기'가 핵심이에요."})
    mon = r["cats"][K_MON]
    if mon < 50:
        blocks.append({"t": "p", "text": "월지(경제관·사회적 가치관) 궁합이 낮은 편이라, 돈을 쓰는 기준이 서로 달라 다툴 수 있어요. '얼마부터는 상의하기'처럼 숫자로 기준을 정해 두면 감정 싸움이 줄어요."})
    elif mon >= 70:
        blocks.append({"t": "p", "text": "월지(경제관·사회적 가치관) 궁합이 좋은 편이라, 돈을 쓰고 모으는 기준이 비슷해서 큰 갈등 없이 계획을 세우기 좋아요."})
    j1, j2 = _future_years(a1, "재성"), _future_years(a2, "재성")
    both = sorted(set(j1) & set(j2))
    blocks.append({"t": "p", "text": "▶ 돈 기운이 들어오는 해"})
    if both:
        blocks.append({"t": "p", "text": f"두 사람 모두 돈의 기운이 들어오는 해: {_years_text(both)}. 이 해에는 함께 저축 목표를 세우거나 큰 계획을 추진하기 좋아요."})
    if j1:
        blocks.append({"t": "p", "text": f"{n1}님: {_years_text(j1)}"})
    if j2:
        blocks.append({"t": "p", "text": f"{n2}님: {_years_text(j2)}"})
    if not (j1 or j2):
        blocks.append({"t": "p", "text": "앞으로 몇 년 안에 두드러지는 돈의 기운은 보이지 않아요. 큰 투자보다 지출을 정리하고 꾸준히 모으는 시기로 보세요."})
    rules = ["공동 생활비 통장과 각자 용돈 통장을 따로 두기 (용돈은 서로 간섭하지 않기)",
             "10만 원(또는 두 사람이 정한 금액) 이상 쓸 때는 미리 상의하기",
             "한 달에 한 번, 10분만 가계 점검 시간 갖기",
             "생활비 3~6개월 치 비상금 목표를 같이 세우기",
             "보증, 동업, 큰 투자는 반드시 둘이 충분히 상의한 뒤 결정하기"]
    if "굴리기형" in (s1, s2):
        rules.append("투자는 '잃어도 생활에 지장 없는 금액'까지만, 전체의 일정 비율로 한도 정하기")
    if "나눔형" in (s1, s2):
        rules.append("경조사비·모임비·가족 용돈은 한 달 한도를 미리 정하기")
    blocks.append({"t": "p", "text": "▶ 돈 문제를 줄이는 실천 규칙"})
    blocks.append({"t": "bullets", "items": rules})
    return {"id": "pair_money", "title": "재물 궁합 (돈 쓰는 방식)", "open": True, "blocks": blocks}


def _pair_child_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    p1, p2 = c1["pillars"], c2["pillars"]
    items = []
    ws = []
    for c, a, n in ((c1, a1, n1), (c2, a2, n2)):
        cg = _child_group(c)
        w = a["ss_w"][cg]
        ws.append(w)
        items.append((n, f"자녀 기운 {_star_text(_stars(w, [0.8, 1.8, 3.0, 4.5]))}"))
    blocks = [{"t": "kv", "items": items}]
    if min(ws) >= 1.8:
        blocks.append({"t": "p", "text": "두 사람 모두 자녀 기운이 알맞게 있어서, 자녀 인연이 풍성하고 함께 키우는 즐거움이 큰 조합이에요."})
    elif max(ws) >= 1.8:
        blocks.append({"t": "p", "text": "한 사람의 자녀 기운이 더 강해요. 그 사람이 아이에게 정을 더 쏟고, 다른 사람은 균형을 잡아 주는 역할이 되기 쉬워요."})
    else:
        blocks.append({"t": "p", "text": "두 사람 모두 자녀 기운이 은은한 편이에요. 서두르지 말고 둘이 충분히 이야기하며 때를 맞추는 편이 마음이 편해요."})
    blocks.append({"t": "p", "text": "▶ 자녀 자리(시지)끼리의 관계"})
    if p1.get("hour") and p2.get("hour"):
        a, b = p1["hour"][1], p2["hour"][1]
        rels = branch_relations(a, b)
        if rels:
            for kind, label in rels:
                note = _missing_note(c1, c2, "hour", a, b) if kind == "반합" else ""
                blocks.append({"t": "p", "text": _pair_rel_text("hour", a, b, kind, label) + (" " + note if note else "")})
        elif a == b:
            blocks.append({"t": "p", "text": _pair_rel_text("hour", a, b, "같은 지지", f"같은 글자({JI[a]})")})
        else:
            blocks.append({"t": "p", "text": "두 사람의 자녀 자리 사이에는 특별히 끌리거나 부딪히는 관계가 없어서, 육아 방식이 큰 충돌 없이 맞춰지기 쉬워요."})
    else:
        blocks.append({"t": "callout", "kind": "warn", "text": "한 사람이라도 태어난 시간을 모르면 자녀 자리(시주) 궁합은 볼 수 없어요."})
    t1, t2 = _top_group(a1), _top_group(a2)
    blocks.append({"t": "p", "text": "▶ 두 사람의 육아 스타일"})
    if t1 == t2:
        blocks.append({"t": "p", "text": f"두 사람 모두 '{PARENT_STYLE[t1]}'가 되기 쉬워서 일관된 교육이 가능해요. 대신 부족한 면을 채워 줄 사람(조부모, 선생님 등)이 있으면 좋아요."})
    else:
        blocks.append({"t": "p", "text": f"{n1}님은 '{PARENT_STYLE[t1]}', {n2}님은 '{PARENT_STYLE[t2]}'가 되기 쉬워요. 서로 다른 모습이 아이에게 균형이 되도록 역할을 나누세요. (한 사람이 엄하면 다른 사람은 안아 주기)"})
    blocks.append({"t": "table", "headers": ["이름", "맡으면 좋은 역할", "주의할 점"], "rows": [
        [f"{n1}님", PARENT_ROLE[t1], PARENT_WARN[t1]], [f"{n2}님", PARENT_ROLE[t2], PARENT_WARN[t2]]], "widths": [1, 4, 4]})
    y1, y2 = _future_years(a1, _child_group(c1)), _future_years(a2, _child_group(c2))
    both = sorted(set(y1) & set(y2))
    if both:
        blocks.append({"t": "p", "text": f"▶ 두 사람 모두 자녀 기운이 들어오는 해: {_years_text(both)}. 아이 계획을 이야기하기 좋은 시기로 참고해 보세요."})
    elif y1 or y2:
        parts = []
        if y1:
            parts.append(f"{n1}님은 {_years_text(y1)}")
        if y2:
            parts.append(f"{n2}님은 {_years_text(y2)}")
        blocks.append({"t": "p", "text": "▶ 자녀 기운이 들어오는 해: " + " / ".join(parts)})
    blocks.append({"t": "p", "text": "▶ 아이를 키울 때 함께 지키면 좋은 약속"})
    blocks.append({"t": "bullets", "items": [
        "아이 앞에서 서로의 훈육 방식을 비난하지 않기 (의견이 다르면 아이가 없을 때 이야기하기)",
        "엄한 사람과 부드러운 사람의 역할을 정해 두되, 가끔 서로 바꿔 보기",
        "교육비·학원 같은 큰 비용은 미리 한도를 정하고 함께 결정하기",
        "아이가 아니라 '행동'을 지적하고, 잘한 점은 구체적으로 칭찬하기"]})
    blocks.append({"t": "callout", "kind": "info", "text": "자녀 인연은 사주만으로 정해지지 않아요. 두 사람이 어떤 부모가 되기 쉬운지 가볍게 참고하는 용도로만 봐 주세요."})
    return {"id": "pair_child", "title": "자녀 궁합 (함께 아이를 키운다면)", "open": True, "blocks": blocks}


def _pair_family_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    p1, p2 = c1["pillars"], c2["pillars"]
    y1, y2 = p1["year"][1], p2["year"][1]
    blocks = [{"t": "kv", "items": [(f"{n1}님의 띠", f"{JI_ANIMAL[y1]}띠 ({JI[y1]})"), (f"{n2}님의 띠", f"{JI_ANIMAL[y2]}띠 ({JI[y2]})")]}]
    blocks.append({"t": "p", "text": "▶ 띠(연지) 관계 — 양가 집안과 가족 분위기"})
    rels = branch_relations(y1, y2)
    if rels:
        for kind, label in rels:
            note = _missing_note(c1, c2, "year", y1, y2) if kind == "반합" else ""
            blocks.append({"t": "p", "text": _pair_rel_text("year", y1, y2, kind, label) + (" " + note if note else "")})
    elif y1 == y2:
        blocks.append({"t": "p", "text": _pair_rel_text("year", y1, y2, "같은 지지", f"같은 띠({JI_ANIMAL[y1]}띠)")})
    else:
        blocks.append({"t": "p", "text": "두 사람의 띠 사이에는 특별히 끌리거나 부딪히는 관계가 없어요. 양가 관계는 두 사람이 어떻게 소통하느냐에 따라 달라져요."})
    blocks.append({"t": "p", "text": "▶ 월지 관계 — 부모님·형제와 일·돈에 대한 가치관"})
    m1, m2 = p1["month"][1], p2["month"][1]
    mr = branch_relations(m1, m2)
    if mr:
        for kind, label in mr:
            note = _missing_note(c1, c2, "month", m1, m2) if kind == "반합" else ""
            blocks.append({"t": "p", "text": _pair_rel_text("month", m1, m2, kind, label) + (" " + note if note else "")})
    elif m1 == m2:
        blocks.append({"t": "p", "text": _pair_rel_text("month", m1, m2, "같은 지지", f"같은 글자({JI[m1]})")})
    else:
        blocks.append({"t": "p", "text": "두 사람의 월지 사이에는 특별히 끌리거나 부딪히는 관계가 없어요. 가치관이 크게 어긋나지 않는 편이에요."})
    blocks.append({"t": "p", "text": "▶ 각자가 자란 가정 분위기"})
    its = []
    for n, a in ((n1, a1), (n2, a2)):
        ys = a["gods"]["year"]["branch"][0]
        ms = a["gods"]["month"]["branch"][0]
        its.append(f"{n}님: 어린 시절 자리의 중심 기운은 '{ys}'({_kw(ys)}), 부모·사회 자리는 '{ms}'({_kw(ms)})예요.")
    blocks.append({"t": "bullets", "items": its})
    blocks.append({"t": "p", "text": "▶ 가족 모임·명절 팁"})
    tips = ["명절·가족 행사 일정은 서로의 집안 분위기를 고려해 미리 번갈아 가며 정하기",
            "상대 가족에 대한 불만은 가족 앞이 아니라 둘이 있을 때 부드럽게 말하기",
            "내 가족이 하는 말에 대한 상대의 서운함이 있다면 '내가 중간에서 잘 전달할게'라고 먼저 말하기"]
    if r["cats"][K_YEAR] < 50 or r["cats"][K_MON] < 50:
        tips.append("집안 분위기나 가치관 차이가 있는 편이니, 처음부터 모든 걸 맞추려 하기보다 '이 부분은 서로 양보'라고 선을 정해 두기")
    blocks.append({"t": "bullets", "items": tips})
    return {"id": "pair_family", "title": "가족·집안 궁합 (양가 관계)", "open": False, "blocks": blocks}


def _pair_work_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    t1, t2 = _top_group(a1), _top_group(a2)
    blocks = [{"t": "p", "text": "연인이나 부부가 아니라 직장 동료, 동업 파트너, 함께 하는 프로젝트라면 이렇게 보세요."}]
    blocks.append({"t": "table", "headers": ["이름", "일에서의 강점", "맡기 좋은 역할", "주의할 점"], "rows": [
        [f"{n1}님", WORK_STRENGTH[t1], WORK_ROLE[t1], WORK_WARN[t1]], [f"{n2}님", WORK_STRENGTH[t2], WORK_ROLE[t2], WORK_WARN[t2]]], "widths": [1, 3, 4, 4]})
    blocks.append({"t": "p", "text": "▶ 두 사람의 조합: " + WORK_COMBO[frozenset({t1, t2})]})
    mon = r["cats"][K_MON]
    blocks.append({"t": "p", "text": "▶ 일과 가치관: " + _tier(mon, [
        (70, "일을 대하는 태도와 가치관이 잘 맞아서 함께 일하기 편해요."),
        (50, "일을 대하는 태도는 무난하게 맞춰 갈 수 있어요.")], "일을 대하는 태도와 가치관이 달라서, 역할과 책임 범위를 처음부터 분명히 해 두는 것이 좋아요.")})
    blocks.append({"t": "p", "text": "▶ 함께 일할 때 지키면 좋은 약속"})
    blocks.append({"t": "bullets", "items": [
        "역할과 책임 범위를 글로 적어 두기", "이익·비용 분배 기준을 시작할 때 정하기",
        "의견이 갈리면 '데이터와 사실' 먼저 확인하고, 개인 감정은 따로 이야기하기",
        "서로 잘한 점을 정기적으로 말해 주고, 불만은 쌓아 두지 않기"]})
    return {"id": "pair_work", "title": "함께 일한다면 (직장·동업 궁합)", "open": False, "blocks": blocks}


def _pair_home_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    comb = {o: r["s1"][o] + r["s2"][o] for o in OHANG_LIST}
    mx = max(OHANG_LIST, key=lambda o: comb[o])
    mn = min(OHANG_LIST, key=lambda o: comb[o])
    blocks = [{"t": "p", "text": f"두 사람이 함께 만드는 집안 분위기는 {mx}({OH_HANJA[mx]}) 기운이 가장 강해서 '{FAMILY_MOOD[mx]}'가 되기 쉬워요."},
              {"t": "p", "text": f"가장 부족한 기운은 {mn}({OH_HANJA[mn]})이에요. 집에서 이렇게 채워 보세요: {_OH_LIFESTYLE[mn]}"}]
    o1, o2 = a1["dso"], a2["dso"]
    blocks.append({"t": "p", "text": "▶ 생활 리듬"})
    blocks.append({"t": "bullets", "items": [f"{n1}님({o1}): {OH_RHYTHM[o1]}", f"{n2}님({o2}): {OH_RHYTHM[o2]}"]})
    if o1 == o2:
        blocks.append({"t": "p", "text": "생활 리듬이 닮아서 편하게 맞춰져요. 대신 같은 약점(예: 늦잠, 정리 안 하기)이 겹치기 쉬우니 서로 알려 주세요."})
    elif SAENG[o1] == o2 or SAENG[o2] == o1:
        blocks.append({"t": "p", "text": "생활 리듬이 서로 이어지는 편이라 한쪽이 이끌고 다른 쪽이 따라가는 형태로 자연스럽게 맞춰져요."})
    else:
        blocks.append({"t": "p", "text": "생활 리듬이 다른 편이라 처음엔 서로 맞추기 힘들 수 있어요. 식사·수면·청소 시간 같은 기본 규칙을 먼저 합의해 두면 훨씬 편해져요."})
    blocks.append({"t": "p", "text": "▶ 서로의 컨디션 챙기기"})
    its = []
    for n, s in ((n1, r["s1"]), (n2, r["s2"])):
        w = min(OHANG_LIST, key=lambda o: s[o])
        its.append(f"{n}님은 {w}({OH_HANJA[w]}) 기운이 약한 편이에요. 관련 부위({ORGAN[w]})를 무리하지 않도록 서로 챙겨 주세요. 함께 해 볼 활동: {_OH_LIFESTYLE[w]}")
    blocks.append({"t": "bullets", "items": its})
    blocks.append({"t": "callout", "kind": "info", "text": "오행과 신체 부위의 연결은 전통 이론에 따른 참고 정보이며 의학적 진단이 아니에요. 건강 문제는 반드시 전문가와 상담하세요."})
    return {"id": "pair_home", "title": "함께 살면 (생활 리듬·집안 분위기·건강)", "open": False, "blocks": blocks}


def _year_verdict(s1, s2, n1, n2):
    if s1 == 2 and s2 == 2:
        return "함께 도전하기 좋은 해", "결혼·이사·큰 계획을 함께 세우기 좋은 흐름이에요."
    if s1 == -2 and s2 == -2:
        return "둘 다 조심하는 해", "큰 결정은 미루고 서로 쉬어 가며 지켜 주세요."
    if s1 == 0 and s2 == 0:
        return "무난한 해", "큰 변화보다 지금의 생활을 안정적으로 이어가기 좋아요."
    if s1 == 2 and s2 == 0:
        return "한 사람이 힘을 받는 해", f"{n1}님이 앞에서 이끌고 {n2}님이 든든히 받쳐 주세요."
    if s1 == 0 and s2 == 2:
        return "한 사람이 힘을 받는 해", f"{n2}님이 앞에서 이끌고 {n1}님이 든든히 받쳐 주세요."
    if s1 == 2 and s2 == -2:
        return "엇갈리는 해", f"{n1}님은 잘 풀리고 {n2}님은 힘들 수 있어요. {n1}님이 {n2}님을 많이 챙겨 주세요."
    if s1 == -2 and s2 == 2:
        return "엇갈리는 해", f"{n2}님은 잘 풀리고 {n1}님은 힘들 수 있어요. {n2}님이 {n1}님을 많이 챙겨 주세요."
    who = n1 if s1 == -2 else n2
    return "한 사람이 조심하는 해", f"{who}님의 컨디션과 마음을 먼저 살피고, 무리한 결정은 미뤄 주세요."


def _pair_timing_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    rows = []
    good_years = []
    now_y = a1["now"].year
    for s1, s2 in zip(a1["sewoon"], a2["sewoon"]):
        v, adv = _year_verdict(s1["score"], s2["score"], n1, n2)
        tag = "(올해)" if s1["is_now"] else "(지난해)" if s1["year"] < now_y else ""
        rows.append([f"{s1['year']}년{tag}", s1["gz"], s1["rating"], s2["rating"], v, adv])
        if s1["year"] >= now_y and s1["score"] == 2 and s2["score"] == 2:
            good_years.append(s1["year"])
    blocks = [{"t": "p", "text": f"두 사람의 해마다 운(세운)을 나란히 놓고, 함께 보면 어떤 해인지 정리했어요. 순서는 {n1}님, {n2}님 순이에요."},
              {"t": "table", "headers": ["해", "간지", f"{n1}님", f"{n2}님", "함께 보면", "이렇게 보내세요"], "rows": rows, "widths": [1, 1, 2, 2, 2, 4]}]
    if good_years:
        blocks.append({"t": "p", "text": f"▶ 두 사람 모두 순풍인 해: {_years_text(good_years)}. 결혼, 이사, 이직, 아이 계획 같은 큰 결정을 함께 논의하기 좋은 시기로 참고해 보세요."})
    else:
        blocks.append({"t": "p", "text": "▶ 앞으로 몇 년 안에 두 사람이 동시에 순풍인 해는 뚜렷하지 않아요. 한 사람이 힘이 좋은 해에 그 사람이 이끌어 주는 식으로 시기를 나누면 좋아요."})
    ev = []
    for n, a in ((n1, a1), (n2, a2)):
        for s in a["sewoon"]:
            if s["year"] < now_y:
                continue
            for w, k, lab in s["events"]:
                ev.append(f"{s['year']}년 {n}님: 그해 들어오는 글자와 내 {w}의 관계는 {lab} — {KIND_SHORT.get(k, '')}")
    if ev:
        blocks.append({"t": "p", "text": "▶ 해마다 눈여겨볼 변화"})
        blocks.append({"t": "bullets", "items": ev})
    blocks.append({"t": "callout", "kind": "info", "text": "해가 바뀌는 기준은 1월 1일이 아니라 입춘(2월 초)이에요. 입춘 전후로 분위기가 달라질 수 있어요. 시기 풀이는 참고용이며, 중요한 결정은 현실적인 상황을 먼저 고려하세요."})
    return {"id": "pair_timing", "title": "시기별 흐름 (올해와 앞으로 몇 년)", "open": True, "blocks": blocks}


def _pair_link_section(c1, a1, c2, a2, r):
    n1, n2 = r["names"]
    p1, p2 = c1["pillars"], c2["pillars"]
    b1 = {v[1] for v in p1.values() if v}
    b2 = {v[1] for v in p2.values() if v}
    blocks = [{"t": "p", "text": "각자의 사주에 모자란 글자를 상대가 가지고 있으면, 둘이 만났을 때 '빈 곳이 채워지는' 인연이라고 봐요. 아래는 두 사람의 글자를 합쳐서 찾아낸 연결 고리예요."}]
    found = []
    for grp, label, wang in _SAMHAP:
        if grp <= (b1 | b2) and not grp <= b1 and not grp <= b2:
            m1, m2 = sorted(grp & b1), sorted(grp & b2)
            found.append(f"{label} 완성: {n1}님은 {_fmt_ji(m1) if m1 else '없음'}, {n2}님은 {_fmt_ji(m2) if m2 else '없음'}을(를) 가지고 있어요. 혼자서는 모자란 '세 글자 팀'이 둘이 만나면 완성돼서, 함께 있을 때 힘이 커지고 일이 잘 풀리기 쉬운 인연이에요.")
    for grp, label in _BANGHAP:
        if grp <= (b1 | b2) and not grp <= b1 and not grp <= b2:
            found.append(f"{label} 완성: 같은 계절 글자가 둘이 만나 모두 갖춰져요. 서로의 성향이 닮고 한쪽 기운이 강해지는 관계라서, 그 오행에 해당하는 활동을 같이 하면 에너지가 커져요.")
    if found:
        blocks.append({"t": "bullets", "items": found})
    else:
        blocks.append({"t": "p", "text": "두 사람의 글자를 합쳐서 완성되는 삼합·방합은 없어요. 특별한 연결 고리가 없다는 뜻이지 나쁘다는 뜻은 아니에요."})
    cross = []
    for ka in ("year", "month", "day", "hour"):
        for kb in ("year", "month", "day", "hour"):
            if ka == kb or "day" not in (ka, kb):
                continue
            if not p1.get(ka) or not p2.get(kb):
                continue
            for kind, label in branch_relations(p1[ka][1], p2[kb][1]):
                if kind == "육합":
                    cross.append(f"{n1}님의 {POS_LONG[ka]}지 {JI[p1[ka][1]]} ↔ {n2}님의 {POS_LONG[kb]}지 {JI[p2[kb][1]]}: {label} — 같은 자리는 아니지만 서로 짝이 되는 글자예요. 인연의 끈이 한 겹 더 있어서 ({POS_AREA[ka]} ↔ {POS_AREA[kb]}) 쪽에서 서로 끌리고 편안함을 느끼기 쉬워요.")
                elif kind == "충":
                    cross.append(f"{n1}님의 {POS_LONG[ka]}지 {JI[p1[ka][1]]} ↔ {n2}님의 {POS_LONG[kb]}지 {JI[p2[kb][1]]}: {label} — 서로 부딪히는 자리가 하나 더 있어요. ({POS_AREA[ka]} ↔ {POS_AREA[kb]}) 쪽에서 의견 충돌이나 변화가 생기기 쉬우니 이 부분은 미리 대화해 두세요.")
    for (x, nx, ax), (y, ny, ay) in (((p1, n1, c1), (p2, n2, c2)), ((p2, n2, c2), (p1, n1, c1))):
        for ky in ("year", "month", "hour"):
            if not y.get(ky):
                continue
            for kind, label in stem_relations(x["day"][0], y[ky][0]):
                if kind == "천간합":
                    cross.append(f"{nx}님의 일간(나 자신) {GAN[x['day'][0]]} ↔ {ny}님의 {POS_LONG[ky]}간 {GAN[y[ky][0]]}: {label} — {nx}님의 '나 자신'이 {ny}님의 {POS_AREA[ky]} 글자와 짝이 되어서, 그 분야에서 서로 통하는 느낌이 있어요.")
    if cross:
        blocks.append({"t": "p", "text": "▶ 배우자 자리·나 자신이 상대의 다른 자리와 만나는 관계"})
        blocks.append({"t": "bullets", "items": cross})
    return {"id": "pair_link", "title": "인연의 끈 (서로 채워 주는 글자)", "open": False, "blocks": blocks}


def _pair_reltype_section(c1, a1, c2, a2, r):
    cats = r["cats"]

    def avg(keys):
        return int(round(sum(cats[k] for k in keys) / len(keys)))
    types = [
        ("연인 (썸·연애)", [K_GAN, K_DAY], "설렘과 편안함이 함께 있는 좋은 연애 궁합이에요.", "무난하게 만날 수 있고 서로 노력하면 더 깊어져요.", "끌림이나 생활 방식에서 어긋남이 있어서 천천히 알아가는 게 좋아요."),
        ("부부 (결혼·동거)", [K_DAY, K_OH, K_MON], "오래 함께 살아도 편안한 구조예요. 서로의 빈 곳을 채워 줘요.", "큰 문제는 없지만 생활 규칙과 돈 관리 약속을 해 두면 더 안정돼요.", "생활 습관과 가치관을 미리 많이 맞춰 보고 결정하는 것이 좋아요."),
        ("직장 동료·동업", [K_MON, K_OH], "일과 가치관이 잘 맞아서 협업 효율이 좋아요.", "무난하게 협업할 수 있어요. 역할을 분명히 하면 더 좋아요.", "일하는 방식이 달라서 역할·책임·분배 기준을 문서로 정해 두세요."),
        ("친구", [K_GAN, K_YEAR], "말이 잘 통하고 오래 가는 친구가 되기 좋아요.", "편안하게 지낼 수 있는 친구 사이예요.", "성향이 달라서 서로의 방식을 존중해 주면 오히려 배울 점이 많아요."),
        ("가족 (부모·자녀·형제)", [K_YEAR, K_OH], "서로를 자연스럽게 이해하고 보듬어 주는 관계예요.", "무난한 관계이고 대화로 충분히 조율돼요.", "서로 기대하는 바가 달라서 말로 표현하고 확인하는 습관이 필요해요."),
    ]
    rows = []
    for name, keys, hi, mid, lo in types:
        v = avg(keys)
        rows.append([name, f"{v}점", hi if v >= 70 else mid if v >= 50 else lo])
    blocks = [{"t": "p", "text": "같은 두 사람이라도 어떤 관계냐에 따라 중요한 부분이 달라요. 항목 점수를 관계별로 다시 묶어서 봤어요."},
              {"t": "table", "headers": ["관계", "점수", "이 관계로 만난다면"], "rows": rows, "widths": [2, 1, 6]}]
    return {"id": "pair_reltype", "title": "관계별로 보면 (연인·부부·동료·친구·가족)", "open": False, "blocks": blocks}


def _pair_life_sections(c1, a1, c2, a2, r):
    return []


def build_pair_report(c1, a1, c2, a2):
    r = analyze_pair(c1, a1, c2, a2)
    n1, n2 = r["names"]
    sections = []
    sections.append(_pair_summary_section(c1, a1, c2, a2, r))

    cat_bars = [(k, v, "#4a7bd0" if v >= 70 else "#7a8aa0" if v >= 50 else "#d9694a", f"{v}점") for k, v in r["cats"].items()]
    sections.append({"id": "score", "title": "궁합 점수", "open": True, "blocks": [
        {"t": "score", "value": r["total"], "label": r["label"], "sub": f"{n1} ♥ {n2}"},
        {"t": "bars", "title": "항목별 점수 (100점 만점)", "items": cat_bars, "max": 100},
        _pair_score_table(r),
        {"t": "p", "text": "점수는 성향·끌림(일간) 25% · 배우자 자리(일지) 25% · 오행 보완 20% · 사회생활 자리(월지) 15% · 띠 15%를 합쳐서 낸 평균이에요. (일간=나 자신을 뜻하는 글자, 일지=배우자 자리, 월지=사회생활·가치관 자리)"}]})

    pb = [{"t": "kv", "items": [(n1, birth_label(c1)), (n2, birth_label(c2))]}]
    pb.append({"t": "p", "text": f"▶ {n1}"})
    pb.append(_pillars_block(c1, a1))
    pb.append({"t": "p", "text": f"▶ {n2}"})
    pb.append(_pillars_block(c2, a2))
    for who, c in ((n1, c1), (n2, c2)):
        for n in c["notes"]:
            pb.append({"t": "callout", "kind": "warn", "text": f"[{who}] {n}"})
    sections.append({"id": "charts", "title": "두 사람의 사주", "open": False, "blocks": pb})

    sections.append(_pair_personality_section(c1, a1, c2, a2, r))

    gd = [{"t": "bullets", "items": r["good"]}] if r["good"] else [{"t": "p", "text": "특별히 두드러지는 장점은 보이지 않지만, 무난하게 지낼 수 있는 조합이에요."}]
    sections.append({"id": "good", "title": "잘 맞는 점", "open": True, "blocks": gd})
    bd = [{"t": "bullets", "items": r["bad"]}] if r["bad"] else [{"t": "p", "text": "크게 충돌하는 요소는 보이지 않아요."}]
    sections.append({"id": "bad", "title": "조심할 점", "open": True, "blocks": bd})

    sections.append(_pair_love_section(c1, a1, c2, a2, r))
    sections.append(_pair_talk_section(c1, a1, c2, a2, r))
    sections.append(_pair_money_section(c1, a1, c2, a2, r))
    sections.append(_pair_child_section(c1, a1, c2, a2, r))
    sections.append(_pair_family_section(c1, a1, c2, a2, r))
    sections.append(_pair_work_section(c1, a1, c2, a2, r))
    sections.append(_pair_home_section(c1, a1, c2, a2, r))
    sections.append(_pair_timing_section(c1, a1, c2, a2, r))
    sections.append(_pair_link_section(c1, a1, c2, a2, r))
    sections.append(_pair_reltype_section(c1, a1, c2, a2, r))

    tips = [r["balance"]]
    worst = min(r["cats"], key=r["cats"].get)
    tip_by_cat = {
        K_GAN: "성향 차이가 큰 편이니, 서로의 방식을 '틀림'이 아니라 '다름'으로 받아들이는 대화 규칙을 만들어 보세요. 예를 들어 '결론부터 말하는 사람'과 '과정을 이야기하고 싶은 사람'이라면, 시작할 때 '지금은 해결책이 필요해, 공감이 필요해?'라고 먼저 물어보는 것도 좋아요.",
        K_DAY: "생활 리듬·집안일·돈 쓰는 방식을 미리 정해 두면 일상의 마찰을 크게 줄일 수 있어요. 집안일 분담표, 쉬는 날 보내는 방식, 각자의 혼자만의 시간을 정해 두세요.",
        K_MON: "일·사회적 가치관이 다를 수 있으니, 직업·경제관·미래 계획을 솔직하게 맞춰 보세요. 1년, 3년, 10년 뒤 모습을 서로 이야기하는 시간을 가져 보는 것이 좋아요.",
        K_OH: "서로에게 없는 기운을 활동으로 채워 보세요(함께 운동·산책·취미 만들기). 같은 기운이 과한 편이라면 서로 다른 취미를 존중해 주는 것도 방법이에요.",
        K_YEAR: "띠 궁합은 가볍게 참고하되, 어른·가족 관계에서 생기는 의견 차이를 서로 이해하려 해 보세요. 가족 이야기는 감정이 상하지 않도록 둘이 있을 때 부드럽게 하세요.",
    }
    tips.append(tip_by_cat[worst])
    y1, y2 = r["y"]
    tips.append(f"{n1}님에게는 {y1}({OH_HANJA[y1]}) 기운, {n2}님에게는 {y2}({OH_HANJA[y2]}) 기운이 도움이 돼요. {n1}님: {_OH_LIFESTYLE[y1]} / {n2}님: {_OH_LIFESTYLE[y2]}")
    top1, top2 = _top_group(a1), _top_group(a2)
    tips.append(f"오늘부터 해 볼 작은 실천 ① 하루 10분, 휴대폰 없이 대화하기 ② 하루에 한 번 칭찬하기 — {n1}님에게는 '{TALK_WANT[top1]}', {n2}님에게는 '{TALK_WANT[top2]}' 같은 말이 좋아요 ③ 주 1회 함께 하는 활동 만들기")
    tips.append("서운한 점은 쌓아 두지 말고 그날그날 짧게 이야기하는 것이 어떤 궁합이든 가장 확실한 해법이에요.")
    sections.append({"id": "tips", "title": "관계를 좋게 하는 팁", "open": True, "blocks": [{"t": "bullets", "items": tips}]})

    dt = [{"t": "p", "text": "각 항목이 어떻게 계산됐는지 보여 주는 근거예요. 괄호 안의 숫자(+16, −26 등)는 기본 점수에 더해지거나 빠진 점수예요."}]
    for k, lines in r["detail"].items():
        dt.append({"t": "kv", "items": [(k, f"{r['cats'][k]}점")]})
        dt.append({"t": "bullets", "items": lines})
    if r["extra"]:
        dt.append({"t": "bullets", "items": r["extra"]})
    sections.append({"id": "detail", "title": "항목별 상세 근거", "open": False, "blocks": dt})

    comb = {o: r["s1"][o] + r["s2"][o] for o in OHANG_LIST}
    tc = sum(comb.values())
    ob = [{"t": "bars", "title": f"{n1}의 오행", "items": [(f"{o}({OH_HANJA[o]})", r["s1"][o], OH_COLOR[o], f"{r['s1'][o]:.0%}") for o in OHANG_LIST], "max": 0.6},
          {"t": "bars", "title": f"{n2}의 오행", "items": [(f"{o}({OH_HANJA[o]})", r["s2"][o], OH_COLOR[o], f"{r['s2'][o]:.0%}") for o in OHANG_LIST], "max": 0.6},
          {"t": "bars", "title": "두 사람을 합친 오행 (부부·파트너로서의 균형)", "items": [(f"{o}({OH_HANJA[o]})", comb[o] / tc, OH_COLOR[o], f"{comb[o] / tc:.0%}") for o in OHANG_LIST], "max": 0.6}]
    weak = [o for o in OHANG_LIST if comb[o] / tc < 0.10]
    if weak:
        ob.append({"t": "p", "text": f"함께 있어도 {', '.join(weak)} 기운이 부족한 편이에요. 생활 속에서 이 기운을 보충해 주면 균형이 좋아집니다."})
    else:
        ob.append({"t": "p", "text": "두 사람을 합치면 오행이 비교적 고르게 채워져, 서로의 빈틈을 메워주는 구조입니다."})
    sections.append({"id": "oh", "title": "오행 비교·보완", "open": False, "blocks": ob})

    sm = []
    for c, a in ((c1, a1), (c2, a2)):
        top = max(a["ss_w"], key=a["ss_w"].get)
        sm.append([c["name"] or "사람", f"{GAN[a['ds']]}({a['dso']})", GRADE_PLAIN[a["grade"]], GROUP_TAG[top], f"{a['yong'][0][1]}"])
    sections.append({"id": "who", "title": "각자 요약", "open": False, "blocks": [
        {"t": "table", "headers": ["이름", "일간", "강약", "가장 강한 성향", "필요한 기운"], "rows": sm, "widths": [1, 1, 1, 2, 2]}]})
    sections.append({"id": "glossary", "title": "용어 쉽게 보기", "open": False, "blocks": [{"t": "bullets", "items": [
        "일간: 태어난 날의 위 글자예요. 사주에서 '나 자신'을 뜻해요.",
        "일지·월지·연지·시지: 태어난 날·달·해·시간의 아래 글자예요. 각각 배우자 자리, 사회생활·부모 자리, 띠·집안 자리, 자녀·말년 자리로 봐요.",
        "오행(목·화·토·금·수): 세상을 이루는 다섯 가지 기운. 나무·불·흙·쇠·물에 비유해요.",
        "상생·상극: 상생은 서로 키워 주는 관계(나무→불→흙→쇠→물→나무), 상극은 서로 누르는 관계예요.",
        "천간합·천간충: 일간처럼 위 글자끼리 서로 끌려서 하나가 되거나(합), 정면으로 맞붙는(충) 관계예요.",
        "육합: 아래 글자 두 개가 짝꿍처럼 붙는 관계예요. 삼합: 세 글자가 모여 한 팀이 되는 관계, 반합: 그중 두 글자만 모인 상태예요.",
        "충·형·해·파·원진: 부딪히거나 불편하거나 서운하거나 어긋나거나 애증이 있는 관계들이에요.",
        "십성(비겁·식상·재성·관성·인성): 내 기준으로 상대 글자가 나와 어떤 관계인지 알려 주는 이름이에요. 내 편·재능·돈·직장·공부로 이해하면 쉬워요.",
        "신강·신약: 내 편 기운이 많으면 신강, 적으면 신약이에요. 좋고 나쁨이 아니라 힘의 세기예요.",
        "용신: 사주의 균형을 맞춰 주는 '나에게 필요한 기운'이에요.",
        "세운: 해마다 들어오는 1년 단위의 운이에요."]}]})
    sections.append({"id": "note", "title": "유의사항", "open": False, "blocks": [
        {"t": "p", "text": "궁합 점수는 전통 명리학의 일간·지지 합충·오행 보완 이론을 간단히 수치화한 참고 지표입니다. 실제 관계는 두 사람의 대화와 노력이 훨씬 더 중요하며, " + DISCLAIMER}]})
    return {"title": f"{n1} ♥ {n2} 궁합", "kind": "pair", "sections": sections}


# =====================================================================
#  리포트 내보내기 (텍스트 / HTML)
# =====================================================================
def report_to_text(report):
    L = [f"■ {report['title']}", "=" * 50, ""]
    for s in report["sections"]:
        L.append(f"【 {s['title']} 】")
        for b in s["blocks"]:
            t = b["t"]
            if t == "p":
                L.append(b["text"])
            elif t == "callout":
                L.append("※ " + b["text"])
            elif t == "bullets":
                L.extend("  - " + i for i in b["items"])
            elif t == "kv":
                L.extend(f"  {k}: {v}" for k, v in b["items"])
            elif t == "bars":
                L.append(b["title"])
                mx = b.get("max") or max([x[1] for x in b["items"]] + [1e-9])
                for lab, val, _, disp in b["items"]:
                    L.append(f"  {lab:<14} {'█' * int(round(14 * val / mx))} {disp}")
            elif t == "table":
                L.append("  " + " | ".join(b["headers"]))
                for row in b["rows"]:
                    L.append("  " + " | ".join(str(x) for x in row))
            elif t == "pillars":
                L.append("  구분: " + " | ".join(c["label"] for c in b["cols"]))
                L.append("  간지: " + " | ".join("—" if c.get("empty") else f"{c['gan']}{c['ji']}({c['gan_h']}{c['ji_h']})" for c in b["cols"]))
                for k, vals in b["rows"]:
                    L.append(f"  {k}: " + " | ".join(str(v) if v else "-" for v in vals))
            elif t == "score":
                L.append(f"  {b['sub']}  ▶ {b['value']}점 — {b['label']}")
        L.append("")
    return "\n".join(L)


_HTML_CSS = """
body{font-family:'Malgun Gothic','Apple SD Gothic Neo','Noto Sans KR',sans-serif;background:#eef1f7;margin:0;color:#222;line-height:1.65}
.wrap{max-width:920px;margin:0 auto;padding:24px 16px 60px}
h1{font-size:26px;margin:8px 0 4px}.sub{color:#667;margin-bottom:18px;font-size:13px}
details{background:#fff;border-radius:12px;margin:12px 0;box-shadow:0 1px 4px rgba(0,0,0,.08);overflow:hidden}
summary{cursor:pointer;padding:13px 18px;font-weight:700;font-size:16px;background:#e6ecf8;color:#2c4a86;list-style:none}
summary::-webkit-details-marker{display:none}summary:before{content:'▶ ';font-size:12px}details[open] summary:before{content:'▼ '}
.body{padding:8px 18px 16px}p{margin:8px 0}
.callout{padding:10px 14px;border-radius:8px;margin:10px 0;font-size:14px}.info{background:#eaf2ff;border-left:4px solid #4a7bd0}.warn{background:#fff6dd;border-left:4px solid #e0a020}
ul{margin:6px 0 6px 18px;padding:0}li{margin:3px 0}
.kv{display:flex;gap:10px;margin:3px 0;font-size:14px}.kv b{min-width:150px;color:#445}
.pillars{display:grid;grid-template-columns:90px repeat(4,1fr);gap:6px;margin:10px 0;text-align:center}
.ph{font-size:12px;color:#667;padding:4px}.pc{border-radius:10px;color:#fff;padding:10px 4px;font-weight:700}
.pc .k{font-size:30px;line-height:1.1}.pc .h{font-size:14px;opacity:.9}.pc.empty{background:#ddd;color:#888}
.pi{font-size:13px;background:#f5f7fb;border-radius:6px;padding:5px 2px;min-height:20px}.pl{font-size:12px;color:#556;text-align:right;padding:6px 8px 0 0}
.bar{display:flex;align-items:center;gap:8px;margin:5px 0;font-size:14px}.bar .l{width:150px}.bar .t{flex:1;background:#eef1f6;border-radius:6px;height:16px}.bar .f{height:16px;border-radius:6px}.bar .v{width:90px;color:#445}
.bt{font-weight:700;margin:12px 0 4px;color:#334}
table{border-collapse:collapse;width:100%;font-size:13.5px;margin:8px 0}th{background:#e6ecf8;text-align:left;padding:6px 8px}td{padding:6px 8px;border-top:1px solid #e3e7ef;vertical-align:top}tr.hl td{background:#fff3c4;font-weight:700}
.score{text-align:center;padding:10px}.big{font-size:56px;font-weight:800}.slabel{font-size:16px;margin-top:2px}.sbar{height:14px;background:#e6e9f0;border-radius:8px;margin:12px auto;max-width:520px}.sbar div{height:14px;border-radius:8px}
@media print{body{background:#fff}.wrap{padding:0}details{box-shadow:none;border:1px solid #ccc;page-break-inside:avoid}}
"""


def _score_color(v):
    return "#4a7bd0" if v >= 70 else "#e0a020" if v >= 50 else "#d9694a"


def report_to_html(report):
    esc = _html.escape
    out = [f"<!DOCTYPE html><html lang='ko'><head><meta charset='utf-8'><title>{esc(report['title'])}</title>"
           f"<style>{_HTML_CSS}</style></head><body><div class='wrap'><h1>{esc(report['title'])}</h1>"
           f"<div class='sub'>{esc(APP_TITLE)} v{APP_VERSION} · 참고용 풀이 · 인쇄(Ctrl+P)하면 PDF로 저장할 수 있어요</div>"]
    for s in report["sections"]:
        out.append(f"<details{' open' if s['open'] else ''}><summary>{esc(s['title'])}</summary><div class='body'>")
        for b in s["blocks"]:
            t = b["t"]
            if t == "p":
                out.append(f"<p>{esc(b['text'])}</p>")
            elif t == "callout":
                out.append(f"<div class='callout {'warn' if b.get('kind') == 'warn' else 'info'}'>{esc(b['text'])}</div>")
            elif t == "bullets":
                out.append("<ul>" + "".join(f"<li>{esc(i)}</li>" for i in b["items"]) + "</ul>")
            elif t == "kv":
                out.append("".join(f"<div class='kv'><b>{esc(k)}</b><span>{esc(str(v))}</span></div>" for k, v in b["items"]))
            elif t == "bars":
                mx = b.get("max") or max([x[1] for x in b["items"]] + [1e-9])
                out.append(f"<div class='bt'>{esc(b['title'])}</div>")
                for lab, val, color, disp in b["items"]:
                    w = max(1.0, min(100.0, 100.0 * val / mx))
                    out.append(f"<div class='bar'><span class='l'>{esc(lab)}</span><div class='t'><div class='f' style='width:{w:.0f}%;background:{color}'></div></div><span class='v'>{esc(disp)}</span></div>")
            elif t == "table":
                out.append("<table><tr>" + "".join(f"<th>{esc(h)}</th>" for h in b["headers"]) + "</tr>")
                for i, row in enumerate(b["rows"]):
                    out.append(f"<tr{' class=hl' if b.get('highlight') == i else ''}>" + "".join(f"<td>{esc(str(x))}</td>" for x in row) + "</tr>")
                out.append("</table>")
            elif t == "pillars":
                out.append("<div class='pillars'><div></div>" + "".join(f"<div class='ph'>{esc(c['label'])}</div>" for c in b["cols"]))
                for key, (kk, hh) in (("천간", ("gan", "gan_h")), ("지지", ("ji", "ji_h"))):
                    out.append(f"<div class='pl'>{key}</div>")
                    for c in b["cols"]:
                        if c.get("empty"):
                            out.append("<div class='pc empty'>—</div>")
                        else:
                            oh = c["gan_oh"] if key == "천간" else c["ji_oh"]
                            out.append(f"<div class='pc' style='background:{OH_COLOR[oh]}'><div class='k'>{c[kk]}</div><div class='h'>{c[hh]} · {oh}</div></div>")
                for k, vals in b["rows"]:
                    out.append(f"<div class='pl'>{esc(k)}</div>" + "".join(f"<div class='pi'>{esc(str(v))}</div>" for v in vals))
                out.append("</div>")
            elif t == "score":
                col = _score_color(b["value"])
                out.append(f"<div class='score'><div>{esc(b['sub'])}</div><div class='big' style='color:{col}'>{b['value']}<span style='font-size:22px'>점</span></div>"
                           f"<div class='sbar'><div style='width:{b['value']}%;background:{col}'></div></div><div class='slabel'>{esc(b['label'])}</div></div>")
        out.append("</div></details>")
    out.append("</div><script>window.onbeforeprint=function(){document.querySelectorAll('details').forEach(function(d){d.open=true})}</script></body></html>")
    return "".join(out)


# =====================================================================
#  화면(GUI)
# =====================================================================
if sys.platform.startswith("win"):
    FONT = "맑은 고딕"
elif sys.platform == "darwin":
    FONT = "Apple SD Gothic Neo"
else:
    FONT = "Noto Sans CJK KR"
BG = "#eef1f7"
CARD = "#ffffff"
HEAD_BG = "#dfe7f6"
ACCENT = "#2c4a86"


def parse_birth_date(text):
    s = (text or "").strip()
    m = re.match(r"^(\d{4})\D+(\d{1,2})\D+(\d{1,2})\D*$", s)
    if m:
        return int(m.group(1)), int(m.group(2)), int(m.group(3))
    digits = re.sub(r"\D", "", s)
    if len(digits) == 8:
        return int(digits[:4]), int(digits[4:6]), int(digits[6:8])
    raise ValueError("생년월일을 숫자 8자리(예: 19900515)로 입력해 주세요.")


def parse_birth_time(text):
    s = (text or "").strip()
    m = re.match(r"^(\d{1,2})\s*[:시]\s*(\d{1,2})?\s*분?$", s)
    if m:
        h, mi = int(m.group(1)), int(m.group(2) or 0)
    else:
        d = re.sub(r"\D", "", s)
        if len(d) == 4:
            h, mi = int(d[:2]), int(d[2:])
        elif len(d) == 3:
            h, mi = int(d[0]), int(d[1:])
        elif len(d) in (1, 2):
            h, mi = int(d), 0
        else:
            raise ValueError("태어난 시각은 4자리(예: 0830) 또는 8:30처럼 입력해 주세요. 모르면 '모름'을 체크하세요.")
    if not (0 <= h <= 23 and 0 <= mi <= 59):
        raise ValueError("태어난 시각이 올바르지 않아요. (0~23시, 0~59분)")
    return h, mi


class PersonForm(ttk.LabelFrame):
    def __init__(self, master, title):
        super().__init__(master, text=title, padding=8)
        self.v_name = tk.StringVar()
        self.v_gender = tk.StringVar(value="남")
        self.v_cal = tk.StringVar(value="양력")
        self.v_leap = tk.BooleanVar(value=False)
        self.v_date = tk.StringVar()
        self.v_time = tk.StringVar()
        self.v_unknown = tk.BooleanVar(value=False)
        self.v_place = tk.StringVar(value="서울")
        self.v_mode = tk.StringVar(value=SOLAR_MODES[0])
        r = 0
        ttk.Label(self, text="이름").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Entry(self, textvariable=self.v_name, width=12).grid(row=r, column=1, sticky="w", padx=4)
        gf = ttk.Frame(self)
        gf.grid(row=r, column=2, columnspan=2, sticky="w")
        ttk.Radiobutton(gf, text="남", variable=self.v_gender, value="남").pack(side="left")
        ttk.Radiobutton(gf, text="여", variable=self.v_gender, value="여").pack(side="left", padx=6)
        r += 1
        ttk.Label(self, text="달력").grid(row=r, column=0, sticky="w", pady=2)
        cf = ttk.Frame(self)
        cf.grid(row=r, column=1, columnspan=3, sticky="w", padx=4)
        ttk.Radiobutton(cf, text="양력", variable=self.v_cal, value="양력", command=self._on_cal).pack(side="left")
        ttk.Radiobutton(cf, text="음력", variable=self.v_cal, value="음력", command=self._on_cal).pack(side="left", padx=6)
        self.chk_leap = ttk.Checkbutton(cf, text="윤달", variable=self.v_leap)
        self.chk_leap.pack(side="left")
        r += 1
        ttk.Label(self, text="생년월일").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Entry(self, textvariable=self.v_date, width=12).grid(row=r, column=1, sticky="w", padx=4)
        ttk.Label(self, text="예) 19900515", foreground="#778").grid(row=r, column=2, columnspan=2, sticky="w")
        r += 1
        ttk.Label(self, text="태어난 시각").grid(row=r, column=0, sticky="w", pady=2)
        self.ent_time = ttk.Entry(self, textvariable=self.v_time, width=8)
        self.ent_time.grid(row=r, column=1, sticky="w", padx=4)
        ttk.Checkbutton(self, text="시간 모름", variable=self.v_unknown, command=self._on_unknown).grid(row=r, column=2, sticky="w")
        ttk.Label(self, text="예) 0830", foreground="#778").grid(row=r, column=3, sticky="w")
        r += 1
        ttk.Label(self, text="출생지").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Combobox(self, textvariable=self.v_place, values=[c for c, _ in CITIES], state="readonly", width=18).grid(
            row=r, column=1, columnspan=2, sticky="w", padx=4)
        r += 1
        ttk.Label(self, text="시각 기준").grid(row=r, column=0, sticky="w", pady=2)
        ttk.Combobox(self, textvariable=self.v_mode, values=SOLAR_MODES, state="readonly", width=26).grid(
            row=r, column=1, columnspan=3, sticky="w", padx=4)
        self._on_cal()

    def _on_cal(self):
        try:
            self.chk_leap.state(["!disabled"] if self.v_cal.get() == "음력" else ["disabled"])
        except Exception:
            pass
        if self.v_cal.get() != "음력":
            self.v_leap.set(False)

    def _on_unknown(self):
        try:
            self.ent_time.state(["disabled"] if self.v_unknown.get() else ["!disabled"])
        except Exception:
            pass

    def chart_args(self, use_history):
        y, m, d = parse_birth_date(self.v_date.get())
        known = not self.v_unknown.get()
        hh, mm = 12, 0
        if known:
            hh, mm = parse_birth_time(self.v_time.get())
        return dict(name=self.v_name.get().strip(), gender=self.v_gender.get(), calendar=self.v_cal.get(),
                    y=y, m=m, d=d, hh=hh, mm=mm, time_known=known, leap=self.v_leap.get(),
                    place=self.v_place.get(), solar_mode=SOLAR_MODES.index(self.v_mode.get()), use_history=use_history)


class ResultView(ttk.Frame):
    """스크롤 가능한 결과 화면. 리포트 모델을 위젯으로 그려 줍니다."""

    def __init__(self, master):
        super().__init__(master)
        self.canvas = tk.Canvas(self, bg=BG, highlightthickness=0)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.inner = tk.Frame(self.canvas, bg=BG)
        self.win = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")
        self.inner.bind("<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all")))
        self.canvas.bind("<Configure>", self._on_canvas)
        self.bind_all("<MouseWheel>", self._on_wheel, add="+")
        self.bind_all("<Button-4>", self._on_wheel, add="+")
        self.bind_all("<Button-5>", self._on_wheel, add="+")
        self._wrap = []
        self._width = 760
        self.show_message("위에서 정보를 입력하고 [사주 보기] 또는 [궁합 보기]를 눌러 주세요.")

    # --- 스크롤/리사이즈
    def _on_wheel(self, e):
        try:
            w = self.winfo_containing(e.x_root, e.y_root)
        except Exception:
            w = None
        inside = False
        while w is not None:
            if w is self:
                inside = True
                break
            w = getattr(w, "master", None)
        if not inside:
            return
        if getattr(e, "num", None) == 4:
            step = -3
        elif getattr(e, "num", None) == 5:
            step = 3
        else:
            d = getattr(e, "delta", 0) or 0
            step = -int(d / 120) * 3 if abs(d) >= 120 else (-3 if d > 0 else 3)
        self.canvas.yview_scroll(step, "units")

    def _on_canvas(self, e):
        self._width = max(360, e.width)
        self.canvas.itemconfigure(self.win, width=self._width)
        for lbl, pad, frac in self._wrap:
            try:
                lbl.configure(wraplength=max(120, int((self._width - pad) * frac)))
            except Exception:
                pass

    def _reg(self, lbl, pad=70, frac=1.0):
        self._wrap.append((lbl, pad, frac))
        lbl.configure(wraplength=max(120, int((self._width - pad) * frac)))
        return lbl

    # --- 화면 그리기
    def clear(self):
        for w in list(self.inner.winfo_children()):
            w.destroy()
        self._wrap = []

    def show_message(self, text):
        self.clear()
        tk.Label(self.inner, text=text, bg=BG, fg="#667", font=(FONT, 12), pady=60).pack(fill="x")

    def render(self, report):
        self.clear()
        tk.Label(self.inner, text=report["title"], bg=BG, fg=ACCENT, font=(FONT, 18, "bold"), anchor="w",
                 padx=14, pady=10).pack(fill="x")
        for s in report["sections"]:
            self._section(s)
        self.canvas.yview_moveto(0)

    def _section(self, s):
        outer = tk.Frame(self.inner, bg=CARD, highlightbackground="#d3dae8", highlightthickness=1)
        outer.pack(fill="x", padx=12, pady=5)
        state = {"open": s["open"]}
        head = tk.Label(outer, text="", bg=HEAD_BG, fg=ACCENT, font=(FONT, 11, "bold"), anchor="w", padx=12, pady=7,
                        cursor="hand2")
        head.pack(fill="x")
        body = tk.Frame(outer, bg=CARD, padx=12, pady=6)

        def refresh():
            head.configure(text=("▼  " if state["open"] else "▶  ") + s["title"])
            if state["open"]:
                body.pack(fill="x")
            else:
                body.pack_forget()

        def toggle(_e=None):
            state["open"] = not state["open"]
            refresh()

        head.bind("<Button-1>", toggle)
        for b in s["blocks"]:
            self._block(body, b)
        refresh()

    def _block(self, parent, b):
        t = b["t"]
        if t == "p":
            lbl = tk.Label(parent, text=b["text"], bg=CARD, fg="#222", font=(FONT, 10), justify="left", anchor="w")
            lbl.pack(fill="x", pady=3)
            self._reg(lbl, 70)
        elif t == "callout":
            warn = b.get("kind") == "warn"
            lbl = tk.Label(parent, text=b["text"], bg="#fff6dd" if warn else "#eaf2ff", fg="#333", font=(FONT, 10),
                           justify="left", anchor="w", padx=10, pady=6)
            lbl.pack(fill="x", pady=4)
            self._reg(lbl, 80)
        elif t == "bullets":
            for item in b["items"]:
                lbl = tk.Label(parent, text="•  " + item, bg=CARD, fg="#222", font=(FONT, 10), justify="left", anchor="w")
                lbl.pack(fill="x", pady=1)
                self._reg(lbl, 80)
        elif t == "kv":
            f = tk.Frame(parent, bg=CARD)
            f.pack(fill="x", pady=2)
            f.grid_columnconfigure(1, weight=1)
            for i, (k, v) in enumerate(b["items"]):
                kl = tk.Label(f, text=k, bg=CARD, fg="#445", font=(FONT, 10, "bold"), anchor="nw", justify="left", wraplength=170)
                kl.grid(row=i, column=0, sticky="nw", padx=(0, 10), pady=1)
                vl = tk.Label(f, text=str(v), bg=CARD, fg="#222", font=(FONT, 10), anchor="nw", justify="left")
                vl.grid(row=i, column=1, sticky="nw", pady=1)
                self._reg(vl, 290)
        elif t == "bars":
            self._bars(parent, b)
        elif t == "table":
            self._table(parent, b)
        elif t == "pillars":
            self._pillars(parent, b)
        elif t == "score":
            self._score(parent, b)

    def _bars(self, parent, b):
        tk.Label(parent, text=b["title"], bg=CARD, fg="#334", font=(FONT, 10, "bold"), anchor="w").pack(fill="x", pady=(8, 2))
        mx = b.get("max") or max([x[1] for x in b["items"]] + [1e-9])
        for lab, val, color, disp in b["items"]:
            row = tk.Frame(parent, bg=CARD)
            row.pack(fill="x", pady=1)
            tk.Label(row, text=lab, bg=CARD, width=11, anchor="w", font=(FONT, 10)).pack(side="left")
            cv = tk.Canvas(row, width=300, height=16, bg="#eef1f6", highlightthickness=0)
            cv.pack(side="left", padx=6)
            w = max(2, int(300 * min(1.0, val / mx)))
            cv.create_rectangle(0, 0, w, 16, fill=color, outline=color)
            tk.Label(row, text=disp, bg=CARD, fg="#445", anchor="w", font=(FONT, 10)).pack(side="left", padx=4)

    def _table(self, parent, b):
        f = tk.Frame(parent, bg="#d9dfeb")
        f.pack(fill="x", pady=6)
        widths = b.get("widths") or [1] * len(b["headers"])
        tot = float(sum(widths))
        for c, wt in enumerate(widths):
            f.grid_columnconfigure(c, weight=wt)
        for c, h in enumerate(b["headers"]):
            lbl = tk.Label(f, text=h, bg=HEAD_BG, fg=ACCENT, font=(FONT, 10, "bold"), anchor="w", justify="left", padx=6, pady=4)
            lbl.grid(row=0, column=c, sticky="nsew", padx=(0, 1), pady=(0, 1))
            self._reg(lbl, 80, widths[c] / tot)
        for r, row in enumerate(b["rows"], start=1):
            hl = (b.get("highlight") == r - 1)
            bg = "#fff3c4" if hl else (CARD if r % 2 else "#f6f8fc")
            for c, val in enumerate(row):
                lbl = tk.Label(f, text=str(val), bg=bg, fg="#222", font=(FONT, 10, "bold" if hl else "normal"),
                               anchor="nw", justify="left", padx=6, pady=3)
                lbl.grid(row=r, column=c, sticky="nsew", padx=(0, 1), pady=(0, 1))
                self._reg(lbl, 80, widths[c] / tot)

    def _pillars(self, parent, b):
        f = tk.Frame(parent, bg=CARD)
        f.pack(fill="x", pady=8)
        f.grid_columnconfigure(0, weight=0)
        for c in range(1, 5):
            f.grid_columnconfigure(c, weight=1, uniform="pil")
        for c, col in enumerate(b["cols"], start=1):
            tk.Label(f, text=col["label"], bg=CARD, fg="#667", font=(FONT, 10)).grid(row=0, column=c, pady=(0, 3))
        for r, (rowname, key_g, key_h, key_oh) in enumerate((("천간", "gan", "gan_h", "gan_oh"), ("지지", "ji", "ji_h", "ji_oh")), start=1):
            tk.Label(f, text=rowname, bg=CARD, fg="#667", font=(FONT, 9), width=9, anchor="e").grid(row=r, column=0, padx=(0, 6))
            for c, col in enumerate(b["cols"], start=1):
                if col.get("empty"):
                    tk.Label(f, text="—\n시간 모름", bg="#dddddd", fg="#777", font=(FONT, 11)).grid(row=r, column=c, sticky="nsew", padx=3, pady=3, ipady=10)
                else:
                    oh = col[key_oh]
                    tk.Label(f, text=f"{col[key_g]}\n{col[key_h]}  {oh}", bg=OH_COLOR[oh], fg="white",
                             font=(FONT, 20, "bold")).grid(row=r, column=c, sticky="nsew", padx=3, pady=3, ipady=6)
        for i, (name, vals) in enumerate(b["rows"], start=3):
            tk.Label(f, text=name, bg=CARD, fg="#556", font=(FONT, 9), anchor="e").grid(row=i, column=0, sticky="e", padx=(0, 6), pady=2)
            for c, v in enumerate(vals, start=1):
                tk.Label(f, text=str(v) if v else "-", bg="#f3f6fb", fg="#223", font=(FONT, 10)).grid(row=i, column=c, sticky="nsew", padx=3, pady=2, ipady=3)

    def _score(self, parent, b):
        v = b["value"]
        col = _score_color(v)
        f = tk.Frame(parent, bg=CARD)
        f.pack(fill="x", pady=8)
        tk.Label(f, text=b["sub"], bg=CARD, fg="#556", font=(FONT, 11)).pack()
        tk.Label(f, text=f"{v}점", bg=CARD, fg=col, font=(FONT, 36, "bold")).pack()
        cv = tk.Canvas(f, width=420, height=16, bg="#e6e9f0", highlightthickness=0)
        cv.pack(pady=4)
        cv.create_rectangle(0, 0, int(420 * v / 100.0), 16, fill=col, outline=col)
        tk.Label(f, text=b["label"], bg=CARD, fg="#222", font=(FONT, 11, "bold")).pack(pady=2)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_TITLE}  v{APP_VERSION}")
        self.geometry("1180x840")
        self.minsize(980, 640)
        self.configure(bg=BG)
        try:
            st = ttk.Style(self)
            st.theme_use("clam")
            st.configure("TFrame", background=BG)
            st.configure("TLabelframe", background=BG)
            st.configure("TLabelframe.Label", background=BG, foreground=ACCENT, font=(FONT, 10, "bold"))
            st.configure("TLabel", background=BG, font=(FONT, 10))
            st.configure("TCheckbutton", background=BG, font=(FONT, 10))
            st.configure("TRadiobutton", background=BG, font=(FONT, 10))
            st.configure("TNotebook", background=BG)
            st.configure("TButton", font=(FONT, 10, "bold"), padding=6)
        except Exception:
            pass
        self.current = None
        self.v_history = tk.BooleanVar(value=True)

        top = ttk.Frame(self, padding=(10, 8, 10, 2))
        top.pack(fill="x")
        nb = ttk.Notebook(top)
        nb.pack(fill="x")
        t1 = ttk.Frame(nb, padding=6)
        nb.add(t1, text="  개인 사주풀이  ")
        self.form_single = PersonForm(t1, "정보 입력")
        self.form_single.pack(side="left", anchor="n")
        bf = ttk.Frame(t1)
        bf.pack(side="left", padx=16, anchor="n")
        ttk.Button(bf, text="사주 보기", command=self.run_personal).pack(pady=(14, 6), fill="x")
        ttk.Label(bf, text="양력·음력(윤달 포함) 입력 가능\n태어난 시각을 모르면 '시간 모름' 체크", foreground="#667", justify="left").pack()
        t2 = ttk.Frame(nb, padding=6)
        nb.add(t2, text="  궁합 보기  ")
        self.form_a = PersonForm(t2, "첫 번째 사람")
        self.form_a.pack(side="left", anchor="n")
        self.form_b = PersonForm(t2, "두 번째 사람")
        self.form_b.pack(side="left", padx=8, anchor="n")
        self.form_b.v_gender.set("여")
        ttk.Button(t2, text="궁합 보기", command=self.run_pair).pack(side="left", padx=12, anchor="n", pady=(14, 0))

        opt = ttk.Frame(self, padding=(12, 0, 10, 0))
        opt.pack(fill="x")
        ttk.Checkbutton(opt, text="한국 표준시 이력 자동 보정 (1954~61년 UTC+8:30 · 서머타임 시기 시각을 현재 표준시로 환산)",
                        variable=self.v_history).pack(side="left")

        bar = ttk.Frame(self, padding=(10, 6, 10, 0))
        bar.pack(fill="x")
        ttk.Label(bar, text="결과 저장:", foreground="#556").pack(side="left")
        ttk.Button(bar, text="HTML 저장", command=self.save_html).pack(side="left", padx=4)
        ttk.Button(bar, text="브라우저로 열기 (인쇄·PDF)", command=self.open_browser).pack(side="left", padx=4)
        ttk.Button(bar, text="텍스트 저장", command=self.save_text).pack(side="left", padx=4)
        ttk.Button(bar, text="클립보드 복사", command=self.copy_text).pack(side="left", padx=4)

        self.view = ResultView(self)
        self.view.pack(fill="both", expand=True, padx=10, pady=6)
        ttk.Label(self, text="참고용 풀이입니다 · 절기는 VSOP87 천문 급수로 분 단위 계산 · 인터넷 불필요", foreground="#889").pack(pady=(0, 4))

    # --- 실행
    def _report(self, report):
        self.current = report
        self.view.render(report)

    def run_personal(self):
        try:
            args = self.form_single.chart_args(self.v_history.get())
            chart = compute_chart(**args)
            an = analyze(chart)
            self._report(build_personal_report(chart, an))
        except ValueError as e:
            messagebox.showerror("입력 확인", str(e))
        except Exception:
            messagebox.showerror("오류", "계산 중 오류가 발생했어요.\n\n" + traceback.format_exc(limit=3))

    def run_pair(self):
        try:
            ca = compute_chart(**self.form_a.chart_args(self.v_history.get()))
            cb = compute_chart(**self.form_b.chart_args(self.v_history.get()))
            aa, ab = analyze(ca), analyze(cb)
            self._report(build_pair_report(ca, aa, cb, ab))
        except ValueError as e:
            messagebox.showerror("입력 확인", str(e))
        except Exception:
            messagebox.showerror("오류", "계산 중 오류가 발생했어요.\n\n" + traceback.format_exc(limit=3))

    # --- 저장
    def _need(self):
        if not self.current:
            messagebox.showinfo("안내", "먼저 사주 또는 궁합 결과를 만들어 주세요.")
            return False
        return True

    def _safe_name(self):
        return re.sub(r'[\\/:*?"<>|]', "_", self.current["title"])

    def save_html(self):
        if not self._need():
            return
        path = filedialog.asksaveasfilename(defaultextension=".html", initialfile=self._safe_name() + ".html",
                                            filetypes=[("HTML 파일", "*.html")])
        if path:
            with open(path, "w", encoding="utf-8") as f:
                f.write(report_to_html(self.current))
            if messagebox.askyesno("저장 완료", "저장했어요. 브라우저로 열어 볼까요?\n(브라우저에서 Ctrl+P → PDF로 저장 가능)"):
                webbrowser.open(Path(path).resolve().as_uri())

    def open_browser(self):
        if not self._need():
            return
        path = os.path.join(tempfile.gettempdir(), "saju_report.html")
        with open(path, "w", encoding="utf-8") as f:
            f.write(report_to_html(self.current))
        webbrowser.open(Path(path).resolve().as_uri())

    def save_text(self):
        if not self._need():
            return
        path = filedialog.asksaveasfilename(defaultextension=".txt", initialfile=self._safe_name() + ".txt",
                                            filetypes=[("텍스트 파일", "*.txt")])
        if path:
            with open(path, "w", encoding="utf-8-sig") as f:
                f.write(report_to_text(self.current))
            messagebox.showinfo("저장 완료", "텍스트로 저장했어요.")

    def copy_text(self):
        if not self._need():
            return
        self.clipboard_clear()
        self.clipboard_append(report_to_text(self.current))
        messagebox.showinfo("복사 완료", "결과를 클립보드에 복사했어요.")


def main():
    try:
        app = App()
        app.mainloop()
    except Exception:
        err = traceback.format_exc()
        try:
            messagebox.showerror("오류", "프로그램 실행 중 오류가 발생했습니다.\n\n" + err)
        except Exception:
            print(err, file=sys.stderr)


if __name__ == "__main__":
    main()
