from __future__ import division
from flask import Flask, request, jsonify,render_template
from dotenv import load_dotenv
from flask_cors import CORS
from math import ceil
from collections import namedtuple as struct
import swisseph as swe
import os
import svgwrite

load_dotenv()
app = Flask(__name__)
CORS(app)
#CORS(app, origins=["http://example.com", "https://another-example.com"]) to add custom cros
Date = struct('Date', ['year', 'month', 'day'])
Place = struct('Place', ['latitude', 'longitude', 'timezone'])


sidereal_year = 365.256360417   # From WolframAlpha

# Hindu sunrise/sunset is calculated w.r.t middle of the sun's disk
# They are geomretic, i.e. "true sunrise/set", so refraction is not considered
_rise_flags = swe.BIT_DISC_CENTER + swe.BIT_NO_REFRACTION

# namah suryaya chandraya mangalaya ... rahuve ketuve namah
swe.KETU = swe.PLUTO  # I've mapped Pluto to Ketu
planet_list = [swe.SUN, swe.MOON, swe.MARS, swe.MERCURY, swe.JUPITER,
               swe.VENUS, swe.SATURN, swe.MEAN_NODE, # Rahu = MEAN_NODE
               swe.KETU, swe.URANUS, swe.NEPTUNE ]

revati_359_50 = lambda: swe.set_sid_mode(swe.SIDM_USER, 1926892.343164331, 0)
galc_cent_mid_mula = lambda: swe.set_sid_mode(swe.SIDM_USER, 1922011.128853056, 0)

set_ayanamsa_mode = lambda: swe.set_sid_mode(swe.SIDM_LAHIRI)
reset_ayanamsa_mode = lambda: swe.set_sid_mode(swe.SIDM_FAGAN_BRADLEY)

masas = {
    "1": "Caitra",
    "2": "Vaishakha",
    "3": "Jyeshtha",
    "4": "Ashadha",
    "5": "Shravana",
    "6": "Bhadrapada",
    "7": "Ashvina",
    "8": "Kartika",
    "9": "Margashirsha",
    "10": "Pushya",
    "11": "Magha",
    "12": "Phalguna"
}




ritus = {
    "0": "Vasanta",
    "1": "Grishma",
    "2": "Varsha",
    "3": "Sharad",
    "4": "Hemanta",
    "5": "Shishira"
}

# Temporary function
def get_planet_name(planet):
  names = { swe.SURYA: 'Surya', swe.CHANDRA: 'Candra', swe.KUJA: 'Mangala',
            swe.BUDHA: 'Budha', swe.GURU: 'Guru', swe.SUKRA: 'Sukra',
            swe.SANI: 'Sani', swe.RAHU: 'Rahu', swe.KETU: 'Ketu', swe.PLUTO: 'Ketu'}
  return names[planet]

# Convert 23d 30' 30" to 23.508333 degrees
from_dms = lambda degs, mins, secs: degs + mins/60 + secs/3600

# the inverse
def to_dms_prec(deg):
  d = int(deg)
  mins = (deg - d) * 60
  m = int(mins)
  s = round((mins - m) * 60, 6)
  return [d, m, s]

def to_dms(deg):
  d, m, s = to_dms_prec(deg)
  return [d, m, int(s)]

def unwrap_angles(angles):
  """Add 360 to those elements in the input list so that
     all elements are sorted in ascending order."""
  result = angles
  for i in range(1, len(angles)):
    if result[i] < result[i-1]: result[i] += 360

  assert(result == sorted(result))
  return result

# Make angle lie between [-180, 180) instead of [0, 360)
norm180 = lambda angle: (angle - 360) if angle >= 180 else angle

# Make angle lie between [0, 360)
norm360 = lambda angle: angle % 360

# Ketu is always 180° after Rahu, so same coordinates but different constellations
# i.e if Rahu is in Pisces, Ketu is in Virgo etc
ketu = lambda rahu: (rahu + 180) % 360

def function(point):
    swe.set_sid_mode(swe.SIDM_USER, point, 0.0)
    #swe.set_sid_mode(swe.SIDM_LAHIRI)
    # Place Revati at 359°50'
    #fval = norm180(swe.fixstar_ut("Revati", point, flag = swe.FLG_SWIEPH | swe.FLG_SIDEREAL)[0]) - ((359 + 49/60 + 59/3600) - 360)
    # Place Revati at 0°0'0"
    #fval = norm180(swe.fixstar_ut("Revati", point, flag = swe.FLG_SWIEPH | swe.FLG_SIDEREAL)[0])
    # Place Citra at 180°
    fval = swe.fixstar_ut("Citra", point, flag = swe.FLG_SWIEPH | swe.FLG_SIDEREAL)[0] - (180)
    # Place Pushya (delta Cancri) at 106°
    # fval = swe.fixstar_ut(",deCnc", point, flag = swe.FLG_SWIEPH | swe.FLG_SIDEREAL)[0] - (106)
    return fval

def bisection_search(func, start, stop):
  left = start
  right = stop
  epsilon = 5E-10   # Anything better than this puts the loop below infinite

  while True:
    middle = (left + right) / 2
    midval =  func(middle)
    rtval = func(right)
    if midval * rtval >= 0:
      right = middle
    else:
      left = middle

    if (right - left) <= epsilon: break

  return (right + left) / 2

def inverse_lagrange(x, y, ya):
  """Given two lists x and y, find the value of x = xa when y = ya, i.e., f(xa) = ya"""
  assert(len(x) == len(y))
  total = 0
  for i in range(len(x)):
    numer = 1
    denom = 1
    for j in range(len(x)):
      if j != i:
        numer *= (ya - y[j])
        denom *= (y[i] - y[j])

    total += numer * x[i] / denom

  return total

# Julian Day number as on (year, month, day) at 00:00 UTC
gregorian_to_jd = lambda date: swe.julday(date.year, date.month, date.day, 0.0)
jd_to_gregorian = lambda jd: swe.revjul(jd, swe.GREG_CAL)   # returns (y, m, d, h, min, s)

def local_time_to_jdut1(year, month, day, hour = 0, minutes = 0, seconds = 0, timezone = 0.0):
  """Converts local time to JD(UT1)"""
  y, m, d, h, mnt, s = swe.utc_time_zone(year, month, day, hour, minutes, seconds, timezone)
  # BUG in pyswisseph: replace 0 by s
  jd_et, jd_ut1 = swe.utc_to_jd(y, m, d, h, mnt, 0, flag = swe.GREG_CAL)
  return jd_ut1

def nakshatra_pada(longitude):
  """Gives nakshatra (1..27) and paada (1..4) in which given longitude lies"""
  # 27 nakshatras span 360°
  one_star = (360 / 27)  # = 13°20'
  # Each nakshatra has 4 padas, so 27 x 4 = 108 padas in 360°
  one_pada = (360 / 108) # = 3°20'
  quotient = int(longitude / one_star)
  reminder = (longitude - quotient * one_star)
  pada = int(reminder / one_pada)
  # convert 0..26 to 1..27 and 0..3 to 1..4
  return [1 + quotient, 1 + pada]

def sidereal_longitude(jd, planet):
  """Computes nirayana (sidereal) longitude of given planet on jd"""
  set_ayanamsa_mode()
  longi = swe.calc_ut(jd, planet, flag = swe.FLG_SWIEPH | swe.FLG_SIDEREAL)
  #print(longi)
  reset_ayanamsa_mode()
  return norm360(longi[0][0]) # degrees

solar_longitude = lambda jd: sidereal_longitude(jd, swe.SUN)
lunar_longitude = lambda jd: sidereal_longitude(jd, swe.MOON)

def sunrise(jd, place):
  """Sunrise when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = swe.CALC_RISE)
  rise = result[1][0]  # julian-day number
  #print(rise)
  # Convert to local time
  return [rise + tz/24., to_dms((rise - jd) * 24 + tz)]

def sunset(jd, place):
  """Sunset when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = swe.CALC_SET)
  setting = result[1][0]  # julian-day number
  # Convert to local time
  return [setting + tz/24., to_dms((setting - jd) * 24 + tz)]

def moonrise(jd, place):
  """Moonrise when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi =  swe.CALC_RISE)
  rise = result[1][0]  # julian-day number
  # Convert to local time
  return to_dms((rise - jd) * 24 + tz)

def moonset(jd, place):
  """Moonset when centre of disc is at horizon for given date and place"""
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi =  swe.CALC_SET)
  setting = result[1][0]  # julian-day number
  # Convert to local time
  return to_dms((setting - jd) * 24 + tz)

# Tithi doesn't depend on Ayanamsa
def tithi(jd, place):
  """Tithi at sunrise for given date and place. Also returns tithi's end time."""
  tz = place.timezone
  # 1. Find time of sunrise
  rise = sunrise(jd, place)[0] - tz / 24

  # 2. Find tithi at this JDN
  moon_phase = lunar_phase(rise)
  today = ceil(moon_phase / 12)
  degrees_left = today * 12 - moon_phase

  # 3. Compute longitudinal differences at intervals of 0.25 days from sunrise
  offsets = [0.25, 0.5, 0.75, 1.0]
  lunar_long_diff = [ (lunar_longitude(rise + t) - lunar_longitude(rise)) % 360 for t in offsets ]
  solar_long_diff = [ (solar_longitude(rise + t) - solar_longitude(rise)) % 360 for t in offsets ]
  relative_motion = [ moon - sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff) ]

  # 4. Find end time by 4-point inverse Lagrange interpolation
  y = relative_motion
  x = offsets
  # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
  approx_end = inverse_lagrange(x, y, degrees_left)
  ends = (rise + approx_end -jd) * 24 + tz
  answer = [int(today), to_dms(ends)]

  # 5. Check for skipped tithi
  moon_phase_tmrw = lunar_phase(rise + 1)
  tomorrow = ceil(moon_phase_tmrw / 12)
  isSkipped = (tomorrow - today) % 30 > 1
  if isSkipped:
    # interpolate again with same (x,y)
    leap_tithi = today + 1
    degrees_left = leap_tithi * 12 - moon_phase
    approx_end = inverse_lagrange(x, y, degrees_left)
    ends = (rise + approx_end -jd) * 24 + place.timezone
    leap_tithi = 1 if today == 30 else leap_tithi
    answer += [int(leap_tithi), to_dms(ends)]

  return answer


def nakshatra(jd, place):
  """Current nakshatra as of julian day (jd)
     1 = Asvini, 2 = Bharani, ..., 27 = Revati
  """
  # 1. Find time of sunrise
  lat, lon, tz = place
  rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

  offsets = [0.0, 0.25, 0.5, 0.75, 1.0]
  longitudes = [ lunar_longitude(rise + t) for t in offsets]

  # 2. Today's nakshatra is when offset = 0
  # There are 27 Nakshatras spanning 360 degrees
  nak = ceil(longitudes[0] * 27 / 360)

  # 3. Find end time by 5-point inverse Lagrange interpolation
  y = unwrap_angles(longitudes)
  x = offsets
  approx_end = inverse_lagrange(x, y, nak * 360 / 27)
  ends = (rise - jd + approx_end) * 24 + tz
  answer = [int(nak), to_dms(ends)]

  # 4. Check for skipped nakshatra
  nak_tmrw = ceil(longitudes[-1] * 27 / 360)
  isSkipped = (nak_tmrw - nak) % 27 > 1
  if isSkipped:
    leap_nak = nak + 1
    approx_end = inverse_lagrange(offsets, longitudes, leap_nak * 360 / 27)
    ends = (rise - jd + approx_end) * 24 + tz
    leap_nak = 1 if nak == 27 else leap_nak
    answer += [int(leap_nak), to_dms(ends)]

  return answer


def yoga(jd, place):
  """Yoga at given jd and place.
     1 = Vishkambha, 2 = Priti, ..., 27 = Vaidhrti
  """
  # 1. Find time of sunrise
  lat, lon, tz = place
  rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

  # 2. Find the Nirayana longitudes and add them
  lunar_long = lunar_longitude(rise)
  solar_long = solar_longitude(rise)
  total = (lunar_long + solar_long) % 360
  # There are 27 Yogas spanning 360 degrees
  yog = ceil(total * 27 / 360)

  # 3. Find how many longitudes is there left to be swept
  degrees_left = yog * (360 / 27) - total

  # 3. Compute longitudinal sums at intervals of 0.25 days from sunrise
  offsets = [0.25, 0.5, 0.75, 1.0]
  lunar_long_diff = [ (lunar_longitude(rise + t) - lunar_longitude(rise)) % 360 for t in offsets ]
  solar_long_diff = [ (solar_longitude(rise + t) - solar_longitude(rise)) % 360 for t in offsets ]
  total_motion = [ moon + sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff) ]

  # 4. Find end time by 4-point inverse Lagrange interpolation
  y = total_motion
  x = offsets
  # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
  approx_end = inverse_lagrange(x, y, degrees_left)
  ends = (rise + approx_end - jd) * 24 + tz
  answer = [int(yog), to_dms(ends)]

  # 5. Check for skipped yoga
  lunar_long_tmrw = lunar_longitude(rise + 1)
  solar_long_tmrw = solar_longitude(rise + 1)
  total_tmrw = (lunar_long_tmrw + solar_long_tmrw) % 360
  tomorrow = ceil(total_tmrw * 27 / 360)
  isSkipped = (tomorrow - yog) % 27 > 1
  if isSkipped:
    # interpolate again with same (x,y)
    leap_yog = yog + 1
    degrees_left = leap_yog * (360 / 27) - total
    approx_end = inverse_lagrange(x, y, degrees_left)
    ends = (rise + approx_end - jd) * 24 + tz
    leap_yog = 1 if yog == 27 else leap_yog
    answer += [int(leap_yog), to_dms(ends)]

  return answer


def karana(jd, place):
  """Returns the karana and their ending times. (from 1 to 60)"""
  # 1. Find time of sunrise
  rise = sunrise(jd, place)[0]

  # 2. Find karana at this JDN
  solar_long = solar_longitude(rise)
  lunar_long = lunar_longitude(rise)
  moon_phase = (lunar_long - solar_long) % 360
  today = ceil(moon_phase / 6)
  degrees_left = today * 6 - moon_phase

  return [int(today)]

def vaara(jd):
  """Weekday for given Julian day. 0 = Sunday, 1 = Monday,..., 6 = Saturday"""
  return int(ceil(jd + 1) % 7)

def masa(jd, place):
  """Returns lunar month and if it is adhika or not.
     1 = Chaitra, 2 = Vaisakha, ..., 12 = Phalguna"""
  ti = tithi(jd, place)[0]
  critical = sunrise(jd, place)[0]  # - tz/24 ?
  last_new_moon = new_moon(critical, ti, -1)
  next_new_moon = new_moon(critical, ti, +1)
  this_solar_month = raasi(last_new_moon)
  next_solar_month = raasi(next_new_moon)
  is_leap_month = (this_solar_month == next_solar_month)
  maasa = this_solar_month + 1
  if maasa > 12: maasa = (maasa % 12)
  return [int(maasa), is_leap_month]

# epoch-midnight to given midnight
# Days elapsed since beginning of Kali Yuga
ahargana = lambda jd: jd - 588465.5

def elapsed_year(jd, maasa_num):
  ahar = ahargana(jd)  # or (jd + sunrise(jd, place)[0])
  kali = int((ahar + (4 - maasa_num) * 30) / sidereal_year)
  saka = kali - 3179
  vikrama = saka + 135
  return kali, saka

# New moon day: sun and moon have same longitude (0 degrees = 360 degrees difference)
# Full moon day: sun and moon are 180 deg apart
def new_moon(jd, tithi_, opt = -1):
  """Returns JDN, where
     opt = -1:  JDN < jd such that lunar_phase(JDN) = 360 degrees
     opt = +1:  JDN >= jd such that lunar_phase(JDN) = 360 degrees
  """
  if opt == -1:  start = jd - tithi_         # previous new moon
  if opt == +1:  start = jd + (30 - tithi_)  # next new moon
  # Search within a span of (start +- 2) days
  x = [ -2 + offset/4 for offset in range(17) ]
  y = [lunar_phase(start + i) for i in x]
  y = unwrap_angles(y)
  y0 = inverse_lagrange(x, y, 360)
  return start + y0

def raasi(jd):
  """Zodiac of given jd. 1 = Mesha, ... 12 = Meena"""
  s = solar_longitude(jd)
  solar_nirayana = solar_longitude(jd)
  # 12 rasis occupy 360 degrees, so each one is 30 degrees
  return ceil(solar_nirayana / 30.)

def lunar_phase(jd):
  solar_long = solar_longitude(jd)
  lunar_long = lunar_longitude(jd)
  moon_phase = (lunar_long - solar_long) % 360
  return moon_phase

def samvatsara(jd, maasa_num):
  kali = elapsed_year(jd, maasa_num)[0]
  # Change 14 to 0 for North Indian tradition
  # See the function "get_Jovian_Year_name_south" in pancanga.pl
  if kali >= 4009:    kali = (kali - 14) % 60
  samvat = (kali + 27 + int((kali * 211 - 108) / 18000)) % 60
  return samvat

def ritu(jd,place):
  """0 = Vasanta,...,5 = Shishira"""
  """Returns lunar month and if it is adhika or not.
     1 = Chaitra, 2 = Vaisakha, ..., 12 = Phalguna"""
  ti = tithi(jd, place)[0]
  critical = sunrise(jd, place)[0]  # - tz/24 ?
  last_new_moon = new_moon(critical, ti, -1)
  next_new_moon = new_moon(critical, ti, +1)
  this_solar_month = raasi(last_new_moon)
  next_solar_month = raasi(next_new_moon)
  is_leap_month = (this_solar_month == next_solar_month)
  maasa = this_solar_month + 1
  if maasa > 12: maasa = (maasa % 12)
  maasa_name = masas[str(int(maasa))]
  ritu_num=(maasa - 1) // 2
  rituname=ritus[str(int(ritu_num))]
  vedic_ritu=rituname + ' Ritu'
  return [int(maasa),maasa_name,rituname,vedic_ritu]
 

def day_duration(jd, place):
  srise = sunrise(jd, place)[0]  # julian day num
  sset = sunset(jd, place)[0]    # julian day num
  diff = (sset - srise) * 24
  day  =to_dms(diff)
  day_duration_str = f"{day[0]} H, {day[1]} M,"
  return day_duration_str
  


# The day duration is divided into 8 parts
# Similarly night duration
def gauri_chogadiya(jd, place):
  lat, lon, tz = place
  tz = place.timezone
  srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)[1][0]
  sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_SET)[1][0]
  day_dur = (sset - srise)

  end_times = []
  for i in range(1, 9):
    end_times.append(to_dms((srise + (i * day_dur) / 8 - jd) * 24 + tz))

  # Night duration = time from today's sunset to tomorrow's sunrise
  srise = swe.rise_trans((jd + 1) - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)[1][0]
  night_dur = (srise - sset)
  for i in range(1, 9):
    end_times.append(to_dms((sset + (i * night_dur) / 8 - jd) * 24 + tz))

  return end_times

def vaara_name(weekday_num):
    vaara_names = {
        0: "Bhanuvara",
        1: "Somavara",
        2: "Mangalavara",
        3: "Budhavara",
        4: "Guruvara",
        5: "Sukravara",
        6: "Sanivara"
    }
    return vaara_names.get(weekday_num)
def trikalam(jd, place, option='rahu'):
    lat, lon, tz = place
    tz = place.timezone
    srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
    print(srise)
    sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
    print(sset)
    day_dur = (sset - srise)
    print(day_dur)
    weekday = vaara(jd)
    print(weekday,"weekday")

    # value in each array is for given weekday (0 = sunday, etc.)
    offsets = {'rahu': [0.875, 0.125, 0.25, 0.625, 0.375, 0.75, 0.5],
               'gulika': [0.75, 0.125, 0.5, 0.625, 0.25, 0.875, 0.0],
               'yamaganda': [0.5, 0.25, 0.625, 0.375, 0.75, 0.0, 0.125],
               'amrit': [0.375, 0.25, 0.5, 0.25, 0.625, 0.0, 0.75]}
    

    start_time = srise + day_dur * offsets[option][weekday]
    end_time = start_time + 0.125 * day_dur

    # Converting start and end times to AM/PM format
    start_hour = (int((start_time - jd) * 24 + tz) % 12) or 12  # Ensure 12 remains 12
    start_minute = int(((start_time - jd) * 24 + tz - int((start_time - jd) * 24 + tz)) * 60)
    start_second = int((((start_time - jd) * 24 + tz - int((start_time - jd) * 24 + tz)) * 60 - start_minute) * 60)
    start_period = "AM" if ((start_time - jd) * 24 + tz) < 12 else "PM"

    end_hour = (int((end_time - jd) * 24 + tz) % 12) or 12  # Ensure 12 remains 12
    end_minute = int(((end_time - jd) * 24 + tz - int((end_time - jd) * 24 + tz)) * 60)
    end_second = int((((end_time - jd) * 24 + tz - int((end_time - jd) * 24 + tz)) * 60 - end_minute) * 60)
    end_period = "AM" if ((end_time - jd) * 24 + tz) < 12 else "PM"

    start_time_formatted = f"{start_hour:02d}:{start_minute:02d} {start_period}"
    end_time_formatted = f"{end_hour:02d}:{end_minute:02d} {end_period}"
    vara=vaara_name(weekday)
    return start_time_formatted, end_time_formatted



# def trikalam(jd, place, option='rahu'):
#     lat, lon, tz = place
#     tz = place.timezone
#     srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
#     sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
#     day_dur = (sset - srise)
#     weekday = vaara(jd)

#     # value in each array is for given weekday (0 = sunday, etc.)
#     offsets = {'rahu': [0.875, 0.125, 0.75, 0.5, 0.625, 0.375, 0.25],
#                'gulika': [0.75, 0.625, 0.5, 0.375, 0.25, 0.125, 0.0],
#                'yamaganda': [0.5, 0.375, 0.25, 0.125, 0.0, 0.75, 0.625],
#                'amrit': [0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75]}

#     if option == 'amrit':
#         start_time = srise
#         end_time = srise + 0.125 * day_dur
#     else:
#         start_time = srise + day_dur * offsets[option][weekday]
#         end_time = start_time + 0.125 * day_dur

#     # to local timezone
#     start_time = (start_time - jd) * 24 + tz
#     end_time = (end_time - jd) * 24 + tz
#     return [to_dms(start_time), to_dms(end_time)]  # decimal hours to H:M:S


rahu_kalam = lambda jd, place: trikalam(jd, place, 'rahu')
yamaganda_kalam = lambda jd, place: trikalam(jd, place, 'yamaganda')
gulika_kalam = lambda jd, place: trikalam(jd, place, 'gulika')
amrit_kalam = lambda jd, place: trikalam(jd, place, 'amrit')


def durmuhurtam(jd, place):
  lat, lon, tz = place
  tz = place.timezone

  # Night = today's sunset to tomorrow's sunrise
  sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_SET)[1][0]
  srise = swe.rise_trans((jd + 1) - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)[1][0]
  night_dur = (srise - sset)

  # Day = today's sunrise to today's sunset
  srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)[1][0]
  day_dur = (sset - srise)

  weekday = vaara(jd)

  # There is one durmuhurtam on Sun, Wed, Sat; the rest have two
  offsets = [[10.4, 0.0],  # Sunday
             [6.4, 8.8],   # Monday
             [2.4, 4.8],   # Tuesday, [day_duration , night_duration]
             [5.6, 0.0],   # Wednesday
             [4.0, 8.8],   # Thursday
             [2.4, 6.4],   # Friday
             [1.6, 0.0]]   # Saturday

  # second durmuhurtam of tuesday uses night_duration instead of day_duration
  dur = [day_dur, day_dur]
  base = [srise, srise]
  if weekday == 2:  dur[1] = night_dur; base[1] = sset

  # compute start and end timings
  start_times = [0, 0]
  end_times = [0, 0]
  for i in range(0, 2):
    offset = offsets[weekday][i]
    if offset != 0.0:
      start_times[i] = base[i] + dur[i] * offsets[weekday][i] / 12
      end_times[i] = start_times[i] + day_dur * 0.8 / 12

      # convert to local time
      start_times[i] = (start_times[i] - jd) * 24 + tz
      end_times[i] = (end_times[i] - jd) * 24 + tz

  return [start_times, end_times]  # in decimal hours
def abhijit_muhurta(jd, place):
    """Abhijit muhurta is the 8th muhurta (middle one) of the 15 muhurtas
    during the day_duration (~12 hours)"""
    lat, lon, tz = place
    tz = place.timezone
    srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
    sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
    day_dur = (sset - srise)

    start_time = srise + 7 / 15 * day_dur
    end_time = srise + 8 / 15 * day_dur

    # Converting start time to AM/PM format
    start_hour = (start_time - jd) * 24 + tz
    start_hour_am_pm = int(start_hour) % 12 if int(start_hour) % 12 != 0 else 12
    start_minute = int((start_hour - int(start_hour)) * 60)
    start_second = int(((start_hour - int(start_hour)) * 60 - start_minute) * 60)

    # Converting end time to AM/PM format
    end_hour = (end_time - jd) * 24 + tz
    end_hour_am_pm = int(end_hour) % 12 if int(end_hour) % 12 != 0 else 12
    end_minute = int((end_hour - int(end_hour)) * 60)
    end_second = int(((end_hour - int(end_hour)) * 60 - end_minute) * 60)

    # Checking if it's AM or PM and formatting the times
    start_period = "AM" if start_hour < 12 else "PM"
    end_period = "AM" if end_hour < 12 else "PM"

    abjith_start_time= f"{start_hour_am_pm:02d}:{start_minute:02d} {start_period}"
    
    abjith_end_time = f"{end_hour_am_pm:02d}:{end_minute:02d} {end_period}"

    return abjith_start_time, abjith_end_time


def planetary_positions(jd, place):
  """Computes instantaneous planetary positions
     (i.e., which celestial object lies in which constellation)

     Also gives the nakshatra-pada division
   """
  jd_ut = jd - place.timezone / 24.
  #print(jd_ut)

  positions = []
  #print(planet_list)
  for planet in planet_list:
    
    #print(planet,"====")
    if planet != swe.KETU:
      #print(planet)
      nirayana_long = sidereal_longitude(jd_ut, planet)
    else: # Ketu
      nirayana_long = ketu(sidereal_longitude(jd_ut, swe._RAHU))

    # 12 zodiac signs span 360°, so each one takes 30°
    # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena ,,need to add +1 to all the 
    constellation = int(nirayana_long / 30)
    #print(constellation)
    coordinates = to_dms(nirayana_long % 30)
    #print(coordinates)
    positions.append([nakshatra_pada(nirayana_long)])
    #positions.append([planet, constellation, coordinates, nakshatra_pada(nirayana_long)])

  return positions

def ascendant(jd, place):
  """Lagna (=ascendant) calculation at any given time & place"""
  lat, lon, tz = place
  jd_utc = jd - (tz / 24.)
  
  #print(jd_utc)
  set_ayanamsa_mode() # needed for swe.houses_ex()

  # returns two arrays, cusps and ascmc, where ascmc[0] = Ascendant
  nirayana_lagna = swe.houses_ex(jd_utc, lat, lon, flag = swe.FLG_SIDEREAL)[1][0]
  #print(nirayana_lagna)
  # 12 zodiac signs span 360°, so each one takes 30°
  # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena
  constellation = int(nirayana_lagna / 30)
  coordinates = to_dms(nirayana_lagna % 30)

  reset_ayanamsa_mode()
  # original return [constellation, coordinates, nakshatra_pada(nirayana_lagna)]
  return [constellation]

# http://www.oocities.org/talk2astrologer/LearnAstrology/Details/Navamsa.html
# Useful for making D9 divisional chart
def navamsa_from_long(longitude):
  """Calculates the navamsa-sign in which given longitude falls
  0 = Aries, 1 = Taurus, ..., 11 = Pisces
  """
  one_pada = (360 / (12 * 9))  # There are also 108 navamsas
  one_sign = 12 * one_pada    # = 40 degrees exactly
  signs_elapsed = longitude / one_sign
  fraction_left = signs_elapsed % 1
  return int(fraction_left * 12)

def navamsa(jd, place):
  """Calculates navamsa of all planets"""
  jd_utc = jd - place.timezone / 24.

  positions = []
  for planet in planet_list:
    if planet != swe.KETU:
      nirayana_long = sidereal_longitude(jd_utc, planet)
    else: # Ketu
      nirayana_long = ketu(sidereal_longitude(jd_utc, swe.RAHU))

    positions.append([planet, navamsa_from_long(nirayana_long)])

  return positions


#sandeep calcualtion durmurtham 
def sdurmuhurtam(jd, place):
    lat, lon, tz = place
    tz = place.timezone

    # Night = today's sunset to tomorrow's sunrise
    sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
    srise = swe.rise_trans((jd + 1) - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
    night_dur = (srise - sset)

    # Day = today's sunrise to today's sunset
    srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
    day_dur = (sset - srise)

    weekday = vaara(jd)

    # There is one durmuhurtam on Sun, Wed, Sat; the rest have two
    offsets = [[10.4, 0.0],  # Sunday
               [6.4, 8.8],   # Monday
               [2.4, 4.8],   # Tuesday, [day_duration , night_duration]
               [5.6, 0.0],   # Wednesday
               [4.0, 8.8],   # Thursday
               [2.4, 6.4],   # Friday
               [1.6, 0.0]]   # Saturday

    # second durmuhurtam of Tuesday uses night_duration instead of day_duration
    dur = [day_dur, day_dur]
    base = [srise, srise]
    if weekday == 2:
        dur[1] = night_dur
        base[1] = sset

    # compute start and end timings
    start_times = [0, 0]
    end_times = [0, 0]
    for i in range(0, 2):
        offset = offsets[weekday][i]
        if offset != 0.0:
            start_times[i] = base[i] + dur[i] * offsets[weekday][i] / 12
            end_times[i] = start_times[i] + day_dur * 0.8 / 12

            # convert to local time and then to hours, minutes, seconds
            start_times[i] = decimal_hours_to_hms((start_times[i] - jd) * 24 + tz)
            end_times[i] = decimal_hours_to_hms((end_times[i] - jd) * 24 + tz)

            # Converting start and end times to AM/PM format
            start_hour = int(start_times[i][0]) % 12
            start_minute = int(start_times[i][1])
            start_second = int(start_times[i][2])
            start_period = "AM" if int(start_times[i][0]) < 12 else "PM"

            end_hour = int(end_times[i][0]) % 12
            end_minute = int(end_times[i][1])
            end_second = int(end_times[i][2])
            end_period = "AM" if int(end_times[i][0]) < 12 else "PM"

            start_times[i] = f"{start_hour:02d}:{start_minute:02d} {start_period}"
            end_times[i] = f"{end_hour:02d}:{end_minute:02d} {end_period}"
    dur_start_1=start_times[0]
    dur_start_2=start_times[1]
    dur_end_1=end_times[0]
    dur_end_2=end_times[1]
    # Replace 0 with space if dur_start_2 is 0
    dur_start_2 = ' ' if dur_start_2 == 0 else dur_start_2

    # Replace 0 with space if dur_end_2 is 0
    dur_end_2 = ' ' if dur_end_2 == 0 else dur_end_2
    return dur_start_1, dur_start_2, dur_end_1, dur_end_2

# def sdurmuhurtam(jd, place):
#     lat, lon, tz = place
#     tz = place.timezone

#     # Night = today's sunset to tomorrow's sunrise
#     sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
#     srise = swe.rise_trans((jd + 1) - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
#     night_dur = (srise - sset)

#     # Day = today's sunrise to today's sunset
#     srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
#     day_dur = (sset - srise)

#     weekday = vaara(jd)

#     # There is one durmuhurtam on Sun, Wed, Sat; the rest have two
#     offsets = [[10.4, 0.0],  # Sunday
#                [6.4, 8.8],   # Monday
#                [2.4, 4.8],   # Tuesday, [day_duration , night_duration]
#                [5.6, 0.0],   # Wednesday
#                [4.0, 8.8],   # Thursday
#                [2.4, 6.4],   # Friday
#                [1.6, 0.0]]   # Saturday

#     # second durmuhurtam of Tuesday uses night_duration instead of day_duration
#     dur = [day_dur, day_dur]
#     base = [srise, srise]
#     if weekday == 2:
#         dur[1] = night_dur
#         base[1] = sset

#     # compute start and end timings
#     start_times = [0, 0]
#     end_times = [0, 0]
#     for i in range(0, 2):
#         offset = offsets[weekday][i]
#         if offset != 0.0:
#             start_times[i] = base[i] + dur[i] * offsets[weekday][i] / 12
#             end_times[i] = start_times[i] + day_dur * 0.8 / 12

#             # convert to local time and then to hours, minutes, seconds
#             start_times[i] = decimal_hours_to_hms((start_times[i] - jd) * 24 + tz)
#             end_times[i] = decimal_hours_to_hms((end_times[i] - jd) * 24 + tz)

#     return start_times, end_times


def decimal_hours_to_hms(decimal_hours):
    # Extract integer part for hours
    hours = int(decimal_hours)
    # Calculate remaining decimal part after extracting hours
    remaining_decimal = decimal_hours - hours
    # Calculate minutes
    minutes = int(remaining_decimal * 60)
    # Calculate remaining decimal part after extracting minutes
    remaining_decimal = remaining_decimal * 60 - minutes / 60
    # Calculate seconds
    seconds = round(remaining_decimal * 60)  # Round seconds to the nearest integer
    # Ensure seconds are within the range [0, 59]
    seconds %= 60
    return hours, minutes, seconds


#calculate disha school sandeep

def disha_shool(jd):
    day=int(ceil(jd + 1) % 7)
    
    directions = {
        0: ["West", "South-West (Southern)"],
        1: ["East", "South-East (fire)"],
        2: ["North", "North-West (Vayavya)"],
        3: ["North", "North-East (east)"],
        4: ["South", "South-East (fire)"],
        5: ["West", "South-West (Southern)"],
        6: ["East", "North-East (Ishaan)"]
    }
    
    # return directions[day]
    primary_direction, secondary_direction = directions[day]
    return primary_direction, secondary_direction
    
    
#moonsign calculatin 
def moonsign(year,month,day,time):
  # Convert birth time to decimal hours
  hours, minutes, seconds = map(float, time.split(":"))
  birth_time_dec = hours + minutes / 60 + seconds / 3600
  swe.set_sid_mode(swe.SIDM_LAHIRI)
  moon_position = swe.calc_ut(swe.julday(year, month, day, birth_time_dec), swe.MOON,flag=swe.FLG_SIDEREAL)
  moon_longitude = moon_position[0][0] % 360
  zodiac_signs = {
    0: "Aries", 30: "Taurus", 60: "Gemini", 90: "Cancer",
    120: "Leo", 150: "Virgo", 180: "Libra", 210: "Scorpio",
    240: "Sagittarius", 270: "Capricorn", 300: "Aquarius", 330: "Pisces"
}
  moon_sign_deg = int(moon_longitude) // 30 * 30  # Round down to nearest sign boundary
  moon_sign = zodiac_signs[moon_sign_deg]
  return moon_sign



def sunsign(year,month,day,time):
  
  hours, minutes, seconds = map(float, time.split(":"))
  birth_time_dec = hours + minutes / 60 + seconds / 3600
  jd=swe.julday(year, month, day, birth_time_dec)
  
  s = swe.calc_ut(jd, swe.SUN,flag=swe.FLG_SIDEREAL)
  
  zodiac_signs = {
    0: "Aries", 30: "Taurus", 60: "Gemini", 90: "Cancer",
    120: "Leo", 150: "Virgo", 180: "Libra", 210: "Scorpio",
    240: "Sagittarius", 270: "Capricorn", 300: "Aquarius", 330: "Pisces"
}
  
  solar_nirayana = (s[0][0] - swe.get_ayanamsa_ut(jd)) % 360
  sign_deg = int(solar_nirayana) // 30 * 30
  sunsign=zodiac_signs[sign_deg]
  return sunsign

#calculate thithi name

# def tithiname(jd, place):
#     """Tithi at sunrise for given date and place. Also returns tithi's end time."""
#     thithi_names = {
#         1: "Shukla Paksha Prathama",
#         2: "Shukla Paksha Dvitiya",
#         3: "Shukla Paksha Tritiya",
#         4: "Shukla Paksha Chaturthi",
#         5: "Shukla Paksha Panchami",
#         6: "Shukla Paksha Shashthi",
#         7: "Shukla Paksha Saptami",
#         8: "Shukla Paksha Ashtami",
#         9: "Shukla Paksha Navami",
#         10: "Shukla Paksha Dashami",
#         11: "Shukla Paksha Ekadashi",
#         12: "Shukla Paksha Dwadashi",
#         13: "Shukla Paksha Trayodashi",
#         14: "Shukla Paksha Chaturdashi",
#         15: "Purnima",
#         16: "Krishna Paksha Prathama",
#         17: "Krishna Paksha Dvitiya",
#         18: "Krishna Paksha Tritiya",
#         19: "Krishna Paksha Chaturthi",
#         20: "Krishna Paksha Panchami",
#         21: "Krishna Paksha Shashthi",
#         22: "Krishna Paksha Saptami",
#         23: "Krishna Paksha Ashtami",
#         24: "Krishna Paksha Navami",
#         25: "Krishna Paksha Dashami",
#         26: "Krishna Paksha Ekadashi",
#         27: "Krishna Paksha Dwadashi",
#         28: "Krishna Paksha Trayodashi",
#         29: "Krishna Paksha Chaturdashi",
#         30: "Amavasya"
#     }

#     def to_12_hour_format(hour, minute):
#         hour %= 24
#         am_pm = "AM" if hour < 12 else "PM"
#         hour %= 12
#         if hour == 0:
#             hour = 12
#         return hour, minute, am_pm

#     tz = place.timezone
#     # Find time of sunrise
#     rise = sunrise(jd, place)[0] - tz / 24

#     # Find tithi at this JDN
#     moon_phase = lunar_phase(rise)
#     today = ceil(moon_phase / 12)
#     degrees_left = today * 12 - moon_phase

#     # Compute longitudinal differences at intervals of 0.25 days from sunrise
#     offsets = [0.25, 0.5, 0.75, 1.0]
#     lunar_long_diff = [(lunar_longitude(rise + t) - lunar_longitude(rise)) % 360 for t in offsets]
#     solar_long_diff = [(solar_longitude(rise + t) - solar_longitude(rise)) % 360 for t in offsets]
#     relative_motion = [moon - sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff)]

#     # Find end time by 4-point inverse Lagrange interpolation
#     y = relative_motion
#     x = offsets
#     # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
#     approx_end = inverse_lagrange(x, y, degrees_left)
#     ends = (rise + approx_end - jd) * 24 + tz

#     # Convert end time to 12-hour format with AM/PM indicator
#     hour, minute, am_pm = to_12_hour_format(int(ends), int((ends - int(ends)) * 60))

#     answer = [(today, thithi_names[today]), f"{hour:02d}:{minute:02d} {am_pm}"]

#     # Check if end time is greater than or equal to 24
#     if ends >= 24:
#         ends -= 24
#         tag = "Tomorrow"
#     else:
#         tag = "Today"

#     answer.append(tag)

#     # Check for skipped tithi
#     moon_phase_tmrw = lunar_phase(rise + 1)
#     tomorrow = ceil(moon_phase_tmrw / 12)
#     is_skipped = (tomorrow - today) % 30 > 1
#     if is_skipped:
#         # interpolate again with same (x,y)
#         leap_tithi = today + 1
#         degrees_left = leap_tithi * 12 - moon_phase
#         approx_end = inverse_lagrange(x, y, degrees_left)
#         ends = (rise + approx_end - jd) * 24 + tz
#         leap_tithi = 1 if today == 30 else int(leap_tithi)

#         # Convert leap end time to 12-hour format with AM/PM indicator
#         hour, minute, am_pm = to_12_hour_format(int(ends), int((ends - int(ends)) * 60))

#         leap_tag = "Tomorrow" if ends >= 24 else "Today"
#         answer += [(leap_tithi, thithi_names[leap_tithi]), f"{hour:02d}:{minute:02d} {am_pm}", leap_tag]

#     return answer
def tithiname(jd, place):
    """Tithi at sunrise for given date and place. Also returns tithi's end time."""
    thithi_names = {
        1: "Shukla Paksha Prathama",
        2: "Shukla Paksha Dvitiya",
        3: "Shukla Paksha Tritiya",
        4: "Shukla Paksha Chaturthi",
        5: "Shukla Paksha Panchami",
        6: "Shukla Paksha Shashthi",
        7: "Shukla Paksha Saptami",
        8: "Shukla Paksha Ashtami",
        9: "Shukla Paksha Navami",
        10: "Shukla Paksha Dashami",
        11: "Shukla Paksha Ekadashi",
        12: "Shukla Paksha Dwadashi",
        13: "Shukla Paksha Trayodashi",
        14: "Shukla Paksha Chaturdashi",
        15: "Purnima",
        16: "Krishna Paksha Prathama",
        17: "Krishna Paksha Dvitiya",
        18: "Krishna Paksha Tritiya",
        19: "Krishna Paksha Chaturthi",
        20: "Krishna Paksha Panchami",
        21: "Krishna Paksha Shashthi",
        22: "Krishna Paksha Saptami",
        23: "Krishna Paksha Ashtami",
        24: "Krishna Paksha Navami",
        25: "Krishna Paksha Dashami",
        26: "Krishna Paksha Ekadashi",
        27: "Krishna Paksha Dwadashi",
        28: "Krishna Paksha Trayodashi",
        29: "Krishna Paksha Chaturdashi",
        30: "Amavasya"
    }

    def to_12_hour_format(hour, minute):
        hour %= 24
        am_pm = "AM" if hour < 12 else "PM"
        hour %= 12
        if hour == 0:
            hour = 12
        return hour, minute, am_pm

    tz = place.timezone
    # Find time of sunrise
    rise = sunrise(jd, place)[0] - tz / 24

    # Find tithi at this JDN
    moon_phase = lunar_phase(rise)
    today = ceil(moon_phase / 12)
    degrees_left = today * 12 - moon_phase

    # Compute longitudinal differences at intervals of 0.25 days from sunrise
    offsets = [0.25, 0.5, 0.75, 1.0]
    lunar_long_diff = [(lunar_longitude(rise + t) - lunar_longitude(rise)) % 360 for t in offsets]
    solar_long_diff = [(solar_longitude(rise + t) - solar_longitude(rise)) % 360 for t in offsets]
    relative_motion = [moon - sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff)]

    # Find end time by 4-point inverse Lagrange interpolation
    y = relative_motion
    x = offsets
    # compute fraction of day (after sunrise) needed to traverse 'degrees_left'
    approx_end = inverse_lagrange(x, y, degrees_left)
    ends = (rise + approx_end - jd) * 24 + tz

    # Convert end time to 12-hour format with AM/PM indicator
    hour, minute, am_pm = to_12_hour_format(int(ends), int((ends - int(ends)) * 60))

    thithi_number = today
    thithi_name = thithi_names[today]
    thithi_end_time = f"{hour:02d}:{minute:02d} {am_pm}"
    tag = "Tomorrow" if ends >= 24 else "Today"

    # Check for skipped tithi
    moon_phase_tmrw = lunar_phase(rise + 1)
    tomorrow = ceil(moon_phase_tmrw / 12)
    is_skipped = (tomorrow - today) % 30 > 1

    if is_skipped:
        # interpolate again with same (x,y)
        leap_tithi = today + 1
        degrees_left = leap_tithi * 12 - moon_phase
        approx_end = inverse_lagrange(x, y, degrees_left)
        ends = (rise + approx_end - jd) * 24 + tz
        leap_tithi = 1 if today == 30 else int(leap_tithi)

        # Convert leap end time to 12-hour format with AM/PM indicator
        hour, minute, am_pm = to_12_hour_format(int(ends), int((ends - int(ends)) * 60))

        thithi_number = leap_tithi
        thithi_name = thithi_names[leap_tithi]
        thithi_end_time = f"{hour:02d}:{minute:02d} {am_pm}"
        tag = "Tomorrow" if ends >= 24 else "Today"

    return thithi_number, thithi_name, thithi_end_time, tag

def snakshatra_pada(jd, place):
   

 
    """Current nakshatra as of julian day (jd) along with its pada
       1 = Asvini, 2 = Bharani, ..., 27 = Revati
       1 pada = 3°20'
    """
   
    lat, lon, tz = place
    rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

    offsets = [0.0, 0.25, 0.5, 0.75, 1.0]
    longitudes = [lunar_longitude(rise + t) for t in offsets]

    nak = ceil(longitudes[0] * 27 / 360)
    answer = []

    for i in range(4):
        y = unwrap_angles(longitudes)
        x = offsets
        approx_end = inverse_lagrange(x, y, (nak - 1) * 360 / 27 + i * 360 / 108)
        ends = (rise - jd + approx_end) * 24 + tz
        ends_hours = int(ends)
        ends_minutes = int((ends - ends_hours) * 60)
        am_pm = "AM" if ends_hours < 12 else "PM"
        ends_hours %= 12
        if ends_hours == 0:
            ends_hours = 12
        answer.append((int(nak), i + 1, f"{ends_hours:02d}:{ends_minutes:02d} {am_pm}"))

    return answer

def snakshatra(jd, place):
    """Current nakshatra as of julian day (jd)
       1 = Asvini, 2 = Bharani, ..., 27 = Revati
    """
    # Find time of sunrise
    lat, lon, tz = place
    rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

    offsets = [0.0, 0.25, 0.5, 0.75, 1.0]
    longitudes = [lunar_longitude(rise + t) for t in offsets]

    # Today's nakshatra is when offset = 0
    # There are 27 Nakshatras spanning 360 degrees
    nak = ceil(longitudes[0] * 27 / 360)

    # Find end time by 5-point inverse Lagrange interpolation
    y = unwrap_angles(longitudes)
    x = offsets
    approx_end = inverse_lagrange(x, y, nak * 360 / 27)
    ends = (rise - jd + approx_end) * 24 + tz

    # Convert end time to 12-hour format with AM/PM indicator
    hours = int(ends)
    minutes = int((ends - hours) * 60)
    am_pm = "AM" if hours < 12 else "PM"
    hours %= 12
    if hours == 0:
        hours = 12

    nakshatra_end_time = f"{hours:02d}:{minutes:02d} {am_pm}"

    # Check if end time is greater than or equal to 24
    if ends >= 24:
        ends -= 24
        tag = "tomorrow"
    else:
        tag = "today"

    nakshatra_name = nakshatra_names(int(nak))

    # Store results for the current nakshatra
    nak_number = int(nak)
    nak_name = nakshatra_name
    nak_end_time = nakshatra_end_time
    nak_tag = tag

 
    # Check for skipped nakshatra
    nak_tmrw = ceil(longitudes[-1] * 27 / 360)
    is_skipped = (nak_tmrw - nak) % 27 > 1

    if is_skipped:
        leap_nak = nak + 1
        approx_end = inverse_lagrange(offsets, longitudes, leap_nak * 360 / 27)
        ends = (rise - jd + approx_end) * 24 + tz
        leap_nak = 1 if nak == 27 else leap_nak

        # Convert leap end time to 12-hour format with AM/PM indicator
        hours = int(ends)
        minutes = int((ends - hours) * 60)
        am_pm = "AM" if hours < 12 else "PM"
        hours %= 12
        if hours == 0:
            hours = 12

        leap_nakshatra_end_time = f"{hours:02d}:{minutes:02d} {am_pm}"

        # Check if leap end time is greater than or equal to 24
        if ends >= 24:
            ends -= 24
            leap_tag = "tomorrow"
        else:
            leap_tag = "today"

        leap_nakshatra_name = nakshatra_names(int(leap_nak))

        nak_number = int(leap_nak)
        nak_name = leap_nakshatra_name
        nak_end_time = leap_nakshatra_end_time
        nak_tag = leap_tag

    return nak_number, nak_name, nak_end_time, nak_tag

def nakshatra_names(nak_number):
    nakshatra_names = {
        1: "Asvini",
        2: "Bharani",
        3: "Krittika",
        4: "Rohini",
        5: "Mrigashira",
        6: "Ardra",
        7: "Punarvasu",
        8: "Pushya",
        9: "Ashlesha",
        10: "Magha",
        11: "Purva Phalguni",
        12: "Uttara Phalguni",
        13: "Hasta",
        14: "Chitra",
        15: "Swati",
        16: "Vishakha",
        17: "Anuradha",
        18: "Jyeshtha",
        19: "Mula",
        20: "Purva Ashadha",
        21: "Uttara Ashadha",
        22: "Shravana",
        23: "Dhanishta",
        24: "Shatabhisha",
        25: "Purva Bhadrapada",
        26: "Uttara Bhadrapada",
        27: "Revati"
    }
    return nakshatra_names.get(nak_number, "Unknown")

# def snakshatra(jd, place):
#   """Current nakshatra as of julian day (jd)
#      1 = Asvini, 2 = Bharani, ..., 27 = Revati
#   """
#   # Find time of sunrise
#   lat, lon, tz = place
#   rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

#   offsets = [0.0, 0.25, 0.5, 0.75, 1.0]
#   longitudes = [lunar_longitude(rise + t) for t in offsets]

#   # Today's nakshatra is when offset = 0
#   # There are 27 Nakshatras spanning 360 degrees
#   nak = ceil(longitudes[0] * 27 / 360)

#   # Find end time by 5-point inverse Lagrange interpolation
#   y = unwrap_angles(longitudes)
#   x = offsets
#   approx_end = inverse_lagrange(x, y, nak * 360 / 27)
#   ends = (rise - jd + approx_end) * 24 + tz
#   print(ends)

#   # Check if end time is greater than or equal to 24
#   if ends >= 24:
#       print(ends)
#       ends -= 24
#       tag = "tomorrow"
#   else:
#       tag="today"
#   # Map Nakshatra number to Nakshatra name
#   nakshatra_name = nakshatra_names(int(nak))

#   # Convert end time to 12-hour format with AM/PM indicator
#   hours = int(ends)
#   minutes = int((ends - hours) * 60)
#   am_pm = "AM" if hours < 12 else "PM"
#   hours %= 12
#   if hours == 0:
#       hours = 12

#   answer = [int(nak), nakshatra_name, f"{hours:02d}:{minutes:02d} {am_pm}",tag]

#   # Check for skipped nakshatra
#   nak_tmrw = ceil(longitudes[-1] * 27 / 360)
#   is_skipped = (nak_tmrw - nak) % 27 > 1
#   if is_skipped:
#       leap_nak = nak + 1
#       approx_end = inverse_lagrange(offsets, longitudes, leap_nak * 360 / 27)
#       ends = (rise - jd + approx_end) * 24 + tz
#       leap_nak = 1 if nak == 27 else leap_nak

#       # Check if leap end time is greater than or equal to 24
#       if ends >= 24:
#         print(ends)
#         ends -= 24
#         tag = "tomorrow"
#       else:
#         tag="today"

#       leap_nakshatra_name = nakshatra_names(int(leap_nak))

#       # Convert leap end time to 12-hour format with AM/PM indicator
#       hours = int(ends)
#       minutes = int((ends - hours) * 60)
#       am_pm = "AM" if hours < 12 else "PM"
#       hours %= 12
#       if hours == 0:
#           hours = 12

#       answer += [int(leap_nak), leap_nakshatra_name, f"{hours:02d}:{minutes:02d} {am_pm}",tag]

#   return answer
# def nakshatra_names(nak_number):
#     nakshatra_names = {
#     1: "Asvini",
#     2: "Bharani",
#     3: "Krittika",
#     4: "Rohini",
#     5: "Mrigashira",
#     6: "Ardra",
#     7: "Punarvasu",
#     8: "Pushya",
#     9: "Ashlesha",
#     10: "Magha",
#     11: "Purva Phalguni",
#     12: "Uttara Phalguni",
#     13: "Hasta",
#     14: "Chitra",
#     15: "Swati",
#     16: "Vishakha",
#     17: "Anuradha",
#     18: "Jyeshtha",
#     19: "Mula",
#     20: "Purva Ashadha",
#     21: "Uttara Ashadha",
#     22: "Shravana",
#     23: "Dhanishta",
#     24: "Shatabhisha",
#     25: "Purva Bhadrapada",
#     26: "Uttara Bhadrapada",
#     27: "Revati"
# }

#     return nakshatra_names.get(nak_number, "Unknown")

yoga_names = {
    1: "Vishkumbha",
    2: "Priti",
    3: "Ayushman",
    4: "Saubhagya",
    5: "Shobhana",
    6: "Atiganda",
    7: "Sukarma",
    8: "Dhriti",
    9: "Shula",
    10: "Ganda",
    11: "Vriddhi",
    12: "Dhruva",
    13: "Vyaghata",
    14: "Harshana",
    15: "Vajra",
    16: "Siddhi",
    17: "Vyatipata",
    18: "Variyana",
    19: "Parigha",
    20: "Shiva",
    21: "Siddha",
    22: "Sadhya",
    23: "Shubha",
    24: "Shukla",
    25: "Brahma",
    26: "Aindra",
    27: "Vaidhriti"
}


def syoga(jd, place):
    def to_12_hour_format(hours):
        if hours >= 12:
            return "PM" if hours > 12 else "PM"
        else:
            return "AM"

    lat, lon, tz = place
    rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

    lunar_long = lunar_longitude(rise)
    solar_long = solar_longitude(rise)
    total = (lunar_long + solar_long) % 360
    yog = ceil(total * 27 / 360)

    degrees_left = yog * (360 / 27) - total

    offsets = [0.25, 0.5, 0.75, 1.0]
    lunar_long_diff = [(lunar_longitude(rise + t) - lunar_longitude(rise)) % 360 for t in offsets]
    solar_long_diff = [(solar_longitude(rise + t) - solar_longitude(rise)) % 360 for t in offsets]
    total_motion = [moon + sun for (moon, sun) in zip(lunar_long_diff, solar_long_diff)]

    approx_end = inverse_lagrange(offsets, total_motion, degrees_left)
    ends = (rise + approx_end - jd) * 24 + tz

    answer = [yoga_names.get(yog, "Unknown")]

    if ends >= 24:
        ends -= 24
        tag = "tomorrow"
    else:
        tag = "today"

    # Convert end time to 12-hour format with AM/PM indicator
    hours = int(ends)
    minutes = int((ends - hours) * 60)
    am_pm = to_12_hour_format(hours)
    hours %= 12
    if hours == 0:
        hours = 12

    answer += [f"{hours:02d}:{minutes:02d} {am_pm} {tag}"]

    # Check for skipped yoga
    lunar_long_tmrw = lunar_longitude(rise + 1)
    solar_long_tmrw = solar_longitude(rise + 1)
    total_tmrw = (lunar_long_tmrw + solar_long_tmrw) % 360
    tomorrow = ceil(total_tmrw * 27 / 360)
    isSkipped = (tomorrow - yog) % 27 > 1

    if isSkipped:
        leap_yog = yog + 1
        degrees_left = leap_yog * (360 / 27) - total
        approx_end = inverse_lagrange(offsets, total_motion, degrees_left)
        ends = (rise + approx_end - jd) * 24 + tz
        leap_yog = 1 if yog == 27 else leap_yog

        if ends >= 24:
            ends -= 24
            tag = "tomorrow"
        else:
            tag = "today"

        hours = int(ends)
        minutes = int((ends - hours) * 60)
        am_pm = to_12_hour_format(hours)
        hours %= 12
        if hours == 0:
            hours = 12

        answer += [yoga_names.get(leap_yog, "Unknown"), f"{hours:02d}:{minutes:02d} {am_pm} {tag}"]
  

    if len(answer) == 2:
        answer += [" ", " "]
    yoga1, yoga1time, yoga2, yoga2time = answer[0], answer[1], answer[2], answer[3]


    print( yoga1, yoga1time, yoga2, yoga2time,"ypga time")
    return yoga1, yoga1time, yoga2, yoga2time    
    # return ans




def calculate_brahma_muhurta(jd, place):
    def convert_to_am_pm_format(hour, minute):
        if hour >= 12:
            am_pm = 'PM'
            if hour > 12:
                hour -= 12
        else:
            am_pm = 'AM'
            if hour == 0:
                hour = 12
        return '{:02d}:{:02d} {}'.format(hour, minute, am_pm)
      
    sunrise1=sunrise(jd,place)
    sunset1=sunset(jd,place)
    # Extract sunrise and sunset times in hours, minutes, and seconds
    sunrise_hr, sunrise_min, sunrise_sec = sunrise1[1]
    sunset_hr, sunset_min, sunset_sec = sunset1[1]

    # Calculate total seconds of sunrise and sunset times
    sunrise_total_seconds = sunrise_hr * 3600 + sunrise_min * 60 + sunrise_sec
    sunset_total_seconds = sunset_hr * 3600 + sunset_min * 60 + sunset_sec

    # Calculate Brahma Muhurta
    brahma_muhurta_start_seconds = sunrise_total_seconds - 1 * 3600 - 36 * 60  # 1 hour 36 minutes before sunrise
    brahma_muhurta_end_seconds = sunrise_total_seconds - 48 * 60  # 48 minutes before sunrise

    # Calculate Pratah Sandhya
    pratah_sandhya_start_seconds = sunrise_total_seconds - 48 * 60  # 48 minutes before sunrise
    pratah_sandhya_end_seconds = sunrise_total_seconds + 24 * 60  # 24 minutes after sunrise

    # Calculate Sayanha Sandhya
    sayanha_sandhya_start_seconds = sunset_total_seconds - 24 * 60  # 24 minutes before sunset
    sayanha_sandhya_end_seconds = sunset_total_seconds + 48 * 60  # 48 minutes after sunset

    # Convert times to hours, minutes, and seconds
    brahma_muhurta_start_hour = brahma_muhurta_start_seconds // 3600
    brahma_muhurta_start_min = (brahma_muhurta_start_seconds % 3600) // 60

    brahma_muhurta_end_hour = brahma_muhurta_end_seconds // 3600
    brahma_muhurta_end_min = (brahma_muhurta_end_seconds % 3600) // 60

    pratah_sandhya_start_hour = pratah_sandhya_start_seconds // 3600
    pratah_sandhya_start_min = (pratah_sandhya_start_seconds % 3600) // 60

    pratah_sandhya_end_hour = pratah_sandhya_end_seconds // 3600
    pratah_sandhya_end_min = (pratah_sandhya_end_seconds % 3600) // 60

    sayanha_sandhya_start_hour = sayanha_sandhya_start_seconds // 3600
    sayanha_sandhya_start_min = (sayanha_sandhya_start_seconds % 3600) // 60

    sayanha_sandhya_end_hour = sayanha_sandhya_end_seconds // 3600
    sayanha_sandhya_end_min = (sayanha_sandhya_end_seconds % 3600) // 60

    # Convert to AM/PM format
    brahma_muhurta_start_ampm = convert_to_am_pm_format(brahma_muhurta_start_hour, brahma_muhurta_start_min)
    brahma_muhurta_end_ampm = convert_to_am_pm_format(brahma_muhurta_end_hour, brahma_muhurta_end_min)
    pratah_sandhya_start_ampm = convert_to_am_pm_format(pratah_sandhya_start_hour, pratah_sandhya_start_min)
    pratah_sandhya_end_ampm = convert_to_am_pm_format(pratah_sandhya_end_hour, pratah_sandhya_end_min)
    sayanha_sandhya_start_ampm = convert_to_am_pm_format(sayanha_sandhya_start_hour, sayanha_sandhya_start_min)
    sayanha_sandhya_end_ampm = convert_to_am_pm_format(sayanha_sandhya_end_hour, sayanha_sandhya_end_min)

    return brahma_muhurta_start_ampm, brahma_muhurta_end_ampm , pratah_sandhya_start_ampm, pratah_sandhya_end_ampm, sayanha_sandhya_start_ampm, sayanha_sandhya_end_ampm

#ayana calculation drik system indian astrology //
# he specific dates for the start of Uttarayana and Dakshinayana can vary depending on the astronomical calculations 
# and the specific tradition or almanac used. Generally, Uttarayana starts around the winter solstice (usually around December 21st), 
# and Dakshinayana starts around the summer solstice (usually around June 21st) in the Gregorian calendar.

def calculate_ayana(jd):
    swe.set_sid_mode(swe.SIDM_LAHIRI, 0.0, 0.0)
    # Convert the date to Julian day
    
    
    # Calculate the Sun's position (ecliptic longitude and declination) for the given JD
    sun_pos = swe.calc_ut(jd, swe.SUN, swe.FLG_SWIEPH | swe.FLG_SPEED)
    print(sun_pos)
    ecliptic_declination =int( sun_pos[0][0])
    print(ecliptic_declination)# Ecliptic longitude and declination of the Sun
    
    # Determine Uttaryana or Dakshinayana based on the declination angle
    if 90 < ecliptic_declination < 270:
        return "Dakshinayana"
    else:
        return "Uttarayana"
      
      
      
def calculate_vikram_samvat_year(jd, place,year):
    
  ti = tithi(jd, place)[0]
  critical = sunrise(jd, place)[0]  # - tz/24 ?
  last_new_moon = new_moon(critical, ti, -1)
  next_new_moon = new_moon(critical, ti, +1)
  this_solar_month = raasi(last_new_moon)
  next_solar_month = raasi(next_new_moon)
  is_leap_month = (this_solar_month == next_solar_month)
  maasa = this_solar_month + 1
  if maasa > 12: maasa = (maasa % 12)
  maasa_num=int(maasa)
  kali = elapsed_year(jd, maasa_num)[0]
  kali_year=kali
  print(kali)
  # Change 14 to 0 for North Indian tradition
  # See the function "get_Jovian_Year_name_south" in pancanga.pl
  if kali >= 4009:    kali = (kali - 14) % 60
  samvat = (kali + 27 + int((kali * 211 - 108) / 18000)) % 60
  month_number=int(maasa)
  masas = {
      1: "Chaitra",
      2: "Vaishakha",
      3: "Jyeshtha",
      4: "Ashadha",
      5: "Shravana",
      6: "Bhadrapada",
      7: "Ashvina",
      8: "Kartika",
      9: "Margashirsha",
      10: "Pushya",
      11: "Magha",
      12: "Phalguna"
  }

  # Determine the month name from the month number
  month_name = masas[month_number]

  # Determine the adjustment based on the month name
  if month_name in ["Chaitra", "Vaishakha", "Jyeshtha", "Ashadha", "Shravana", "Bhadrapada", "Ashvina", "Kartika", "Margashirsha"]:
      adjustment = 57
  elif month_name in ["Pushya", "Magha", "Phalguna"]:
      adjustment = 56
  else:
      raise ValueError("Invalid month number provided")

  # Calculate the Vikram Samvat year
  vikram_samvat_year = year + adjustment

  return vikram_samvat_year,kali_year  



def skarana(jd, place):
    karanas = {
        1: "Kimstughna",
        2: "Bava",
        3: "Balava",
        4: "Kaulava",
        5: "Taitila",
        6: "Garaja",
        7: "Vanija",
        8: "Vishti",
        9: "Bava",
        10: "Balava",
        11: "Kaulava",
        12: "Taitila",
        13: "Garaja",
        14: "Vanija",
        15: "Vishti",
        16: "Bava",
        17: "Balava",
        18: "Kaulava",
        19: "Taitila",
        20: "Garaja",
        21: "Vanija",
        22: "Vishti",
        23: "Bava",
        24: "Balava",
        25: "Kaulava",
        26: "Taitila",
        27: "Garaja",
        28: "Vanija",
        29: "Vishti",
        30: "Bava",
        31: "Balava",
        32: "Kaulava",
        33: "Taitila",
        34: "Garaja",
        35: "Vanija",
        36: "Vishti",
        37: "Bava",
        38: "Balava",
        39: "Kaulava",
        40: "Taitila",
        41: "Garaja",
        42: "Vanija",
        43: "Vishti",
        44: "Bava",
        45: "Balava",
        46: "Kaulava",
        47: "Taitila",
        48: "Garaja",
        49: "Vanija",
        50: "Vishti",
        51: "Bava",
        52: "Balava",
        53: "Kaulava",
        54: "Taitila",
        55: "Garaja",
        56: "Vanija",
        57: "Vishti",
        58: "Shakuni",
        59: "Catushpada",
        60: "Nagava"
    }

    

    lat, lon, tz = place
    rise = sunrise(jd, place)[0] - tz / 24.  # Sunrise at UT 00:00

    lunar_long_rise = lunar_longitude(rise)
    solar_long_rise = solar_longitude(rise)
    moon_phase = (lunar_long_rise - solar_long_rise) % 360
    karana_today = ceil(moon_phase / 6)
    print(karana_today)
    degrees_left_karana = karana_today * 6 - moon_phase
    karana_answer = karanas.get(karana_today, "Unknown")
    karana_answer1=karanas.get(karana_today+1, "Unknown")
    return karana_answer,karana_answer1

def smoonrise(jd, place):
    """Moonrise when centre of disc is at horizon for given date and place"""
    lat, lon, tz = place
    result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi=swe.CALC_RISE)
    rise = result[1][0]  # julian-day number
    # Convert to local time
    moonrise_time = to_dms((rise - jd) * 24 + tz)

    # Converting moonrise time to AM/PM format
    hour = (int(moonrise_time[0]) % 12) or 12  # Ensure 12 remains 12
    minute = int(moonrise_time[1])
    second = int(moonrise_time[2])
    period = "AM" if int(moonrise_time[0]) < 12 else "PM"

    moonrise_time_formatted = f"{hour:02d}:{minute:02d} {period}"
    
    return moonrise_time_formatted
  
  
def smoonset(jd, place):
    """Moonset when centre of disc is at horizon for given date and place"""
    lat, lon, tz = place
    result = swe.rise_trans(jd - tz/24, swe.MOON, lon, lat, rsmi=swe.CALC_SET)
    setting = result[1][0]  # julian-day number
    # Convert to local time
    moonset_time = to_dms((setting - jd) * 24 + tz)
    

    # Converting moonset time to AM/PM format
    hour = (int(moonset_time[0]) % 12) or 12  # Ensure 12 remains 12
    minute = int(moonset_time[1])
    second = int(moonset_time[2])
    period = "AM" if int(moonset_time[0]) < 12 else "PM"

    moonset_time_formatted = f"{hour:02d}:{minute:02d} {period}"
    
    return moonset_time_formatted
  
def ssunrise(jd, place):
    """Sunrise when centre of disc is at horizon for given date and place"""
    lat, lon, tz = place
    result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, swe.CALC_RISE)
    rise = result[1][0]  # julian-day number
    # Convert to local time
    sunrise_time = [rise + tz/24., to_dms((rise - jd) * 24 + tz)]
    print(sunrise_time)

    # Converting sunrise time to AM/PM format
    hour = int(sunrise_time[1][0]) % 12
    minute = int(sunrise_time[1][1])
    second = int(sunrise_time[1][2])
    period = "AM" if int(sunrise_time[1][0]) < 12 else "PM"

    sunrise_time_formatted = f"{hour:02d}:{minute:02d} {period}"
    
    return sunrise_time_formatted

def ssunset(jd, place):
    """Sunset when centre of disc is at horizon for given date and place"""
    lat, lon, tz = place
    result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=swe.CALC_SET)
    setting = result[1][0]  # julian-day number
    # Convert to local time
    sunset_time = [setting + tz/24., to_dms((setting - jd) * 24 + tz)]

    # Converting sunset time to AM/PM format
    hour = int(sunset_time[1][0]) % 12
    minute = int(sunset_time[1][1])
    second = int(sunset_time[1][2])
    period = "AM" if int(sunset_time[1][0]) < 12 else "PM"

    sunset_time_formatted = f"{hour:02d}:{minute:02d} {period}"
    
    return sunset_time_formatted
def varam(jd, place):
    lat, lon, tz = place
    tz = place.timezone
    srise = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_RISE)[1][0]
    #print(srise)
    sset = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi=_rise_flags + swe.CALC_SET)[1][0]
    #print(sset)
    day_dur = (sset - srise)
    #print(day_dur)
    weekday = vaara(jd)
    vaara_names = {
        0: "Bhanuvara",
        1: "Somavara",
        2: "Mangalavara",
        3: "Budhavara",
        4: "Guruvara",
        5: "Sukravara",
        6: "Sanivara"
    }
    varam=vaara_names[weekday]
    return varam

def ritu1(jd,place):
  """0 = Vasanta,...,5 = Shishira"""
  """Returns lunar month and if it is adhika or not.
     1 = Chaitra, 2 = Vaisakha, ..., 12 = Phalguna"""
  ti = tithi(jd, place)[0]
  critical = sunrise(jd, place)[0]  # - tz/24 ?
  last_new_moon = new_moon(critical, ti, -1)
  next_new_moon = new_moon(critical, ti, +1)
  this_solar_month = raasi(last_new_moon)
  next_solar_month = raasi(next_new_moon)
  is_leap_month = (this_solar_month == next_solar_month)
  maasa = this_solar_month + 1
  if maasa > 12: maasa = (maasa % 12)
  maasa_name = masas[str(int(maasa))]
  ritu_num=(maasa - 1) // 2
  rituname=ritus[str(int(ritu_num))]
  vedic_ritu=rituname + ' Ritu'
  # return [int(maasa),maasa_name,rituname,vedic_ritu]
  return rituname
#sunrise chart preperation
def sunrise_ascendent(jd, place):
  """Sunrise when centre of disc is at horizon for given date and place"""
  assendent=[]
  lat, lon, tz = place
  result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)
  
  rise = result[1][0]  # julian-day number
  set_ayanamsa_mode() # needed for swe.houses_ex()
  # returns two arrays, cusps and ascmc, where ascmc[0] = Ascendant
  nirayana_lagna = swe.houses_ex(rise, lat, lon, flag = swe.FLG_SIDEREAL)[1][0]
#   print(nirayana_lagna)
  # 12 zodiac signs span 360°, so each one takes 30°
  # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena
  constellation = int(nirayana_lagna / 30)
#   print([rise + tz/24., to_dms((rise - jd) * 24 + tz)])
#   print(rise,"nee to chech the utc timing" )
#adding +1 because it count 0 to 11 in contellation
  # assendent.append(11)
  assendent.append([11,constellation+1])

 
  
  
  positions = []
  jd_ut=rise
  #print(planet_list)
  for planet in planet_list:
    
    #print(planet,"====")
    if planet != swe.KETU:
      #print(planet)
      nirayana_long = sidereal_longitude(jd_ut, planet)
    else: # Ketu
      nirayana_long = ketu(sidereal_longitude(jd_ut, swe._RAHU))

    # 12 zodiac signs span 360°, so each one takes 30°
    # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena ,,need to add +1 to all the 
    constellation = int(nirayana_long / 30)
    #print(constellation)
    coordinates = to_dms(nirayana_long % 30)
    #print(coordinates)
  
    assendent.append([planet,constellation+1])
    print(assendent)
  
  mapping = {
    0: "Su",
    1: "Mo",
    4: "Ma",
    2: "Me",
    5: "Ju",
    3: "Ve",
    6: "Sa",
    10: "Ra",
    9: "Ke",
    11: "Asc",
    7:"",
    8:""
}

  #assendent = [[11, 1], [0, 1], [1, 9], [4, 12], [2, 12], [5, 1], [3, 1], [6, 11], [10, 12], [9, 6]]

  for inner_list in assendent:
      if inner_list[0] in mapping:
          inner_list[0] = mapping[inner_list[0]]
          
  data=assendent
  values = {
      "planet1": "",
      "planet2": "",
      "planet3": "",
      "planet4": "",
      "planet5": "",
      "planet6": "",
      "planet7": "",
      "planet8": "",
      "planet9": "",
      "planet10": "",
      "planet11": "",
      "planet12": "",
  }

  for item in data:
      planet_number = item[1]
      planet_key = "planet" + str(planet_number)
      if planet_key in values:
          if values[planet_key]:
              values[planet_key] += "," + str(item[0])
          else:
              values[planet_key] = str(item[0])

  print(values)

  dwg = svgwrite.Drawing(size=(350, 350))

  # Create a rectangle
  dwg.add(dwg.rect(insert=(0, 0), size=(350, 350), fill="#FFFEC9", stroke="#FFC000", stroke_width=4))

  # Add lines
  dwg.add(dwg.line(start=(0, 0), end=(350, 350), stroke="#FFC000", stroke_width=2))
  dwg.add(dwg.line(start=(350, 0), end=(0, 350), stroke="#FFC000", stroke_width=2))
  dwg.add(dwg.line(start=(0, 175), end=(175, 0), stroke="#FFC000", stroke_width=2))
  dwg.add(dwg.line(start=(175, 350), end=(350, 175), stroke="#FFC000", stroke_width=2))
  dwg.add(dwg.line(start=(175, 0), end=(350, 175), stroke="#FFC000", stroke_width=2))
  dwg.add(dwg.line(start=(0, 175), end=(175, 350), stroke="#FFC000", stroke_width=2))

    # Add text elements
  text_elements = [
      ("1", (173, 165)),
      (values.get("planet1", ""), (173, 87.5)),
      ("2", (86.5, 78.5)),
      (values.get("planet2", ""), (85.5, 31.818181818182)),
      ("3", (69.5, 93.5)),
      (values.get("planet3", ""), (31.818181818182, 93.5)),
      ("4", (157, 181)),
      (values.get("planet4", ""), (85.5, 175)),
      ("5", (69.5, 268.5)),
      (values.get("planet5", ""), (31.818181818182, 268.5)),
      ("6", (86.5, 282.5)),
      (values.get("planet6", ""), (85.5, 338)),
      ("7", (175, 197)),
      (values.get("planet7", ""), (175, 268.5)),
      ("8", (260.5, 282.5)),
      (values.get("planet8", ""), (262.5, 338)),
      ("9", (278.5, 268.5)),
      (values.get("planet9", ""), (318.18181818182, 268.5)),
      ("10", (190, 181)),
      (values.get("planet10", ""), (262.5, 175)),
      ("11", (276.5, 93.5)),
      (values.get("planet11", ""), (318.18181818182, 93.5)),
      ("12", (260.5, 78.5)),
      (values.get("planet12", ""), (262.5, 31.818181818182))
  ]

  for text, position in text_elements:
      dwg.add(dwg.text(text, insert=position, font_size=15, fill="red", stroke="none", text_anchor="middle"))
  return dwg.tostring()
# def sunrise_ascendent(jd, place):
#   """Sunrise when centre of disc is at horizon for given date and place"""
#   assendent=[]
#   lat, lon, tz = place
#   result = swe.rise_trans(jd - tz/24, swe.SUN, lon, lat, rsmi = _rise_flags + swe.CALC_RISE)
  
#   rise = result[1][0]  # julian-day number
#   set_ayanamsa_mode() # needed for swe.houses_ex()
#   # returns two arrays, cusps and ascmc, where ascmc[0] = Ascendant
#   nirayana_lagna = swe.houses_ex(rise, lat, lon, flag = swe.FLG_SIDEREAL)[1][0]
# #   print(nirayana_lagna)
#   # 12 zodiac signs span 360°, so each one takes 30°
#   # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena
#   constellation = int(nirayana_lagna / 30)
# #   print([rise + tz/24., to_dms((rise - jd) * 24 + tz)])
# #   print(rise,"nee to chech the utc timing" )
# #adding +1 because it count 0 to 11 in contellation
#   # assendent.append(11)
#   assendent.append([11,constellation+1])
  
  
#   positions = []
#   jd_ut=rise
#   #print(planet_list)
#   for planet in planet_list:
    
#     #print(planet,"====")
#     if planet != swe.KETU:
#       #print(planet)
#       nirayana_long = sidereal_longitude(jd_ut, planet)
#     else: # Ketu
#       nirayana_long = ketu(sidereal_longitude(jd_ut, swe._RAHU))

#     # 12 zodiac signs span 360°, so each one takes 30°
#     # 0 = Mesha, 1 = Vrishabha, ..., 11 = Meena ,,need to add +1 to all the 
#     constellation = int(nirayana_long / 30)
#     #print(constellation)
#     coordinates = to_dms(nirayana_long % 30)
#     #print(coordinates)
  
#     assendent.append([planet,constellation+1])
  
#   mapping = {
#     0: "Su",
#     1: "Mo",
#     4: "Ma",
#     2: "Me",
#     5: "Ju",
#     3: "Ve",
#     6: "Sa",
#     10: "Ra",
#     9: "Ke",
#     11: "Asc"
# }

#   #assendent = [[11, 1], [0, 1], [1, 9], [4, 12], [2, 12], [5, 1], [3, 1], [6, 11], [10, 12], [9, 6]]

#   for inner_list in assendent:
#       if inner_list[0] in mapping:
#           inner_list[0] = mapping[inner_list[0]]
          
#   data=assendent
#   values = {
#       "planet1": "",
#       "planet2": "",
#       "planet3": "",
#       "planet4": "",
#       "planet5": "",
#       "planet6": "",
#       "planet7": "",
#       "planet8": "",
#       "planet9": "",
#       "planet10": "",
#       "planet11": "",
#       "planet12": "",
#   }

#   for item in data:
#       planet_number = item[1]
#       planet_key = "planet" + str(planet_number)
#       if planet_key in values:
#           if values[planet_key]:
#               values[planet_key] += "," +str( item[0])
#           else:
#               values[planet_key] = str( item[0])



#   dwg = svgwrite.Drawing(size=(350, 350))

#   # Create a rectangle
#   dwg.add(dwg.rect(insert=(0, 0), size=(350, 350), fill="#FFFEC9", stroke="#FFC000", stroke_width=4))

#   # Add lines
#   dwg.add(dwg.line(start=(0, 0), end=(350, 350), stroke="#FFC000", stroke_width=2))
#   dwg.add(dwg.line(start=(350, 0), end=(0, 350), stroke="#FFC000", stroke_width=2))
#   dwg.add(dwg.line(start=(0, 175), end=(175, 0), stroke="#FFC000", stroke_width=2))
#   dwg.add(dwg.line(start=(175, 350), end=(350, 175), stroke="#FFC000", stroke_width=2))
#   dwg.add(dwg.line(start=(175, 0), end=(350, 175), stroke="#FFC000", stroke_width=2))
#   dwg.add(dwg.line(start=(0, 175), end=(175, 350), stroke="#FFC000", stroke_width=2))

#     # Add text elements
#   text_elements = [
#       ("1", (173, 165)),
#       (values.get("planet1", ""), (173, 87.5)),
#       ("2", (86.5, 78.5)),
#       (values.get("planet2", ""), (85.5, 31.818181818182)),
#       ("3", (69.5, 93.5)),
#       (values.get("planet3", ""), (31.818181818182, 93.5)),
#       ("4", (157, 181)),
#       (values.get("planet4", ""), (85.5, 175)),
#       ("5", (69.5, 268.5)),
#       (values.get("planet5", ""), (31.818181818182, 268.5)),
#       ("6", (86.5, 282.5)),
#       (values.get("planet6", ""), (85.5, 338)),
#       ("7", (175, 197)),
#       (values.get("planet7", ""), (175, 268.5)),
#       ("8", (260.5, 282.5)),
#       (values.get("planet8", ""), (262.5, 338)),
#       ("9", (278.5, 268.5)),
#       (values.get("planet9", ""), (318.18181818182, 268.5)),
#       ("10", (190, 181)),
#       (values.get("planet10", ""), (262.5, 175)),
#       ("11", (276.5, 93.5)),
#       (values.get("planet11", ""), (318.18181818182, 93.5)),
#       ("12", (260.5, 78.5)),
#       (values.get("planet12", ""), (262.5, 31.818181818182))
#   ]

#   for text, position in text_elements:
#       dwg.add(dwg.text(text, insert=position, font_size=15, fill="red", stroke="none", text_anchor="middle"))
#       print(dwg.tostring())
#   return dwg.tostring()

# Function to validate API key
def validate_api_key(api_key):
    print(api_key)
    print("API_KEY from environment:", os.getenv('API_KEY'))
    return api_key == os.getenv('API_KEY')

@app.route('/drik', methods=['GET'])
def sunmoon():
    api_key = request.headers.get('api-key')  # Accessing API key from headers
    if not api_key:
        return jsonify({'error': 'Unauthorized access. API key missing.'}), 401

    year = int(request.args.get('year'))
    month = int(request.args.get('month'))
    day = int(request.args.get('day'))
    lat = float(request.args.get('latitude'))
    lon = float(request.args.get('longitude'))
    tz = float(request.args.get('timezone'))
    time=str(request.args.get('time'))
    date = Date(year, month, day)
    place = Place(lat, lon, tz)




    # Validate API key
    if not validate_api_key(api_key):
        return jsonify({'error': 'Unauthorized access. Invalid API key.'}), 401
    
    
    jd=gregorian_to_jd(date)
    sunrise_result=ssunrise(jd,place)
    sunset_result=ssunset(jd,place)
    moonrise_result=smoonrise(jd,place)
    moonset_result=smoonset(jd,place)
    day_duration_result=day_duration(jd,place)
    ritu_result=ritu1(jd,place)
    abhihth_start,abjijeeth_end=abhijit_muhurta(jd,place)
    rahu_kalam_start,rahukalam_end=trikalam(jd,place,'rahu')
    yamakandam_start,yamakandam_end=trikalam(jd,place,'yamaganda')
    gulika_start,gulika_end=trikalam(jd,place,'gulika')
    amrit_start,amrit_end=trikalam(jd,place,'amrit')
    dur_start_1, dur_start_2, dur_end_1, dur_end_2=sdurmuhurtam(jd,place)
    primary_disha_shool, secondary_disha_shool = disha_shool(jd)
    moonsign_result=moonsign(year,month,day,time)
    sunsign_result=sunsign(year,month,day,time)
    #thithi_number, thithi_name, thithi_end_time, tag

    thithi_number, thithi_name, thithi_end_time, tag=tithiname(jd,place)
    # nak_number, nak_name, nak_end_time, nak_tag

    nak_number, nak_name, nak_end_time, nak_tag=snakshatra(jd,place)
    nakshatra_pada=snakshatra_pada(jd,place)
    yoga_tag=yoga(jd,place)
    # yoga1, yoga1time, yoga2, 
    yoga1, yoga1time, yoga2, yoga2time=syoga(jd,place)
    brahma_muhurta_start_ampm, brahma_muhurta_end_ampm , pratah_sandhya_start_ampm, pratah_sandhya_end_ampm, sayanha_sandhya_start_ampm, sayanha_sandhya_end_ampm=calculate_brahma_muhurta(jd,place)
    ayana=calculate_ayana(jd)
    vikram_samvat,kali_year=calculate_vikram_samvat_year(jd,place,year)
    karana1,karana2=skarana(jd,place)
    vaaram=varam(jd,place)
    sun_chart=sunrise_ascendent(jd,place)
    # print(sun_chart)
    

    
    result={
        'year':year,
        'month':month,
        'day':day,
        'sunrise':sunrise_result,
        'sunset':sunset_result,
        'moonrise':moonrise_result,
        'moonset':moonset_result,
        'day_duration':day_duration_result,
        'ritu':ritu_result,
        'abhijit_muhurta_start':abhihth_start,
        'abhijit_murtham_end':abjijeeth_end,
        'rahukalam_start':rahu_kalam_start,
        'rahukalam_end':rahukalam_end,
        'yamakandam_start':yamakandam_start,
        'yamakandam_end':yamakandam_end,
        'gulika_start':gulika_start,
        'gulika_end':gulika_end,
        'amrit_start':amrit_start,
        'amrit_end':amrit_end,

        'dur_start_1':dur_start_1,
        'dur_start_2':dur_start_2,
        'dur_end_1':dur_end_1,
        'dur_start_2':dur_end_2,

        'disha_shool_primary':primary_disha_shool,
        'disha_shool_secondary':secondary_disha_shool,

        'moonsign':moonsign_result,
        'sunsign':sunsign_result,
        # 'tithi':tithi_result,
        'thithi_number':thithi_number,
        'thithiname':thithi_name,
        'thithiend_time':thithi_end_time,
        'thithi_tag':tag,
        'nakshatra_number':nak_number,
        'nakshatra_name':nak_name,
        'nakshatra_end_time':nak_end_time,
        'nakshatra_tag':nak_tag,
        'nakshatra_pada':nakshatra_pada,
        'yoga_tag':yoga_tag,
        'yoga1':yoga1,
        'yoga2':yoga2,
        'yoga1time':yoga1time,
        'yoga2time':yoga2time,
        # 'yoga_name':yoga_name,
        # 'yoga_end_time':yoga_end_time,
        # "yoga_number":yoga_number,
        # 'yoga_tag':yoga_tag,
        'brahma_start':brahma_muhurta_start_ampm,
        'brama_end':brahma_muhurta_end_ampm,
        'pratah_start':pratah_sandhya_start_ampm,
        "pratah_end":pratah_sandhya_end_ampm,
        "sayanha_start":sayanha_sandhya_start_ampm,
        "sayanha_end":sayanha_sandhya_end_ampm,
        "ayana":ayana,
        'vikram_samvat':vikram_samvat,
        'kali_year':kali_year,
        'karana1':karana1,
        "karana2":karana2,
        "vaaram":vaaram,
        "sunrise_chart":sun_chart
          
        
    }
    #return result 
    return render_template('results.html', **result)
    
if __name__ == "__main__":
     app.run(debug=True)
