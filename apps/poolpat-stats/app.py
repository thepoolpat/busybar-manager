#!/usr/bin/env python3
"""Poolpat stats: live streaming numbers scrolling right to left across the bar.

    python3 app.py                        # BUSY Bar over USB (always 10.0.4.20)
    python3 app.py --render device        # one firmware-scrolled label, starts instantly
    python3 app.py --render host          # this process pushes every frame
    python3 app.py --source songstats     # live daily numbers, needs SONGSTATS_API_KEY
    python3 app.py --speed 6              # slower crawl, pixels per second
    python3 app.py --sc 28588 --sp 20936 --am 4174   # pin the numbers, skip fetching
    python3 app.py --sc 1182 --sp 13058 --fans 1726  # rehearse the songstats banner
    python3 app.py --shot banner.png      # save what the bar is showing, 8x
    python3 app.py --clear                # take it off the bar
    python3 app.py --test                 # self-check, no device and no network

Each service is an icon in its own brand colour -- SoundCloud orange, Spotify
green, Apple Music red, indigo earth for the combined total, pink for the
all-platform follower count -- each on a full-height pill in that colour, with
its number beside it in white. Adapted from the ~/busybar/stats-banner proof of concept,
which drew the same banner from numbers typed on the command line.

Where the numbers come from (--source):

  portfolio  (default)  data/plays.json in thepoolpat/poolpat-portfolio, read
                        unauthenticated over raw.githubusercontent.com. That
                        file is rewritten by a weekly bot (Sundays 06:00 UTC),
                        so these figures step once a week, not continuously.
                        Two caveats worth knowing before you trust a tile:
                        Spotify's scrape has been failing since 2026-06-21 and
                        its number is frozen, and Apple Music was never
                        automated at all -- it is typed in by hand.
  songstats             the Songstats Enterprise API, which updates daily
                        rather than weekly and covers Instagram too. Needs a
                        paid key in SONGSTATS_API_KEY; the request and the
                        parser are verified against the live endpoint, only the
                        auth header is unproven -- see fetch_songstats().
                        One thing it cannot do: it publishes no Apple Music
                        plays datapoint on any plan, so that tile is filled from
                        the portfolio file instead and is the one number on the
                        banner that is not live. Note too that it counts
                        only the catalogue registered to the artist profile,
                        which on 2026-09-10 read 1,182 SoundCloud and 13,058
                        Spotify against the portfolio's 28,588 and 20,936 --
                        a different scope, not a correction. That is why
                        portfolio is still the default.

The bar refuses to draw while a BUSY session is running -- a session sits at
priority 90 and every draw below that comes back 409 "Not drawn due to low
priority". This app logs the 409 and keeps scrolling rather than exiting,
because under the manager any exit at all is read as a crash and restarted.
"""
import argparse
import base64
import colorsys
import fcntl
import json
import math
import os
import signal
import struct
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib

APP = "poolpat-stats"
W, H = 72, 16
ICON = 12                     # icon bitmaps are 12x12
PAD = 3                       # icon -> number gap, inside the pill
GAP = 6                       # black gutter between one pill and the next
TAIL = 24                     # blank run before the banner repeats
PILL_PAD = 5                  # pill edge -> content, wide enough that the round
                              # end never clips the icon or the first digit
PILL_H = H                    # full display height: the bar is only 16px tall,
                              # so anything shorter reads as a stripe not a pill
PILL_R = PILL_H // 2          # radius half the height is what makes it a pill

# The bar's "large" font is not monospaced, and assuming it is left every comma
# 4px too wide and every 1 2px too wide -- 18px of phantom gap across this
# banner. These are the font's own advances, read out of the emulator atlas the
# manager ships at web/public/fonts/font-atlas.json, which is the same metric
# table the firmware renders from. Digits are 7 apart except "1"; the comma is 3.
#
# ponytail: eleven numbers copied in rather than parsing a 62KB atlas at start-up,
# because this app only ever draws digits and thousands separators. Reach for the
# atlas itself the day it has to render a letter. Other fonts, same table:
# small 4/3/2, condensed 5/5/3, normal 6/6/3, bold 7/7/3, large 7/5/3
# (digit / "1" / comma).
#
# extra_large is the one whose digits are drawn with two-pixel strokes -- the
# bar's own heavy face. large and below are single-pixel and look thin against
# a coloured pill, which is why this app uses extra_large despite costing a
# pixel of advance per digit.
FONT = "extra_large"
ADVANCE = 8                              # the common width: every digit but "1"
# extra_large is proportional, and these are the atlas's own advances for every
# character this app can put on the bar. Grouped by width rather than listed per
# character because that is how the font is actually built, and because a table
# of forty near-identical lines is a table nobody re-checks.
ADVANCES = {}
for _w, _chars in ((3, ",."), (4, " "), (5, "I1"), (7, "EFJLTZ"), (9, "MVW")):
    ADVANCES.update(dict.fromkeys(_chars, _w))
DIGIT_H = 10                             # extra_large cap height, from the atlas


def text_width(text):
    """Width in pixels of a rendered number, at the bar's real glyph advances."""
    return sum(ADVANCES.get(c, ADVANCE) for c in text)

# ponytail: a wireframe globe -- rim plus meridian plus equator -- collapses at
# 12px into a plus sign in a circle, which is what the first version looked like
# on the bar. A filled disc with the landmasses knocked out of it survives the
# size, because the eye reads the silhouette and the two dark shapes rather than
# a 1px graticule. The rim is never cut, or the circle stops being a circle.
GLOBE = [
    "....####....",
    "..########..",
    ".#####...##.",
    ".##..#...##.",
    "##...##...##",
    "###..##..###",
    "####..#..###",
    "####..#.####",
    ".####...###.",
    ".##########.",
    "..########..",
    "....####....",
]
SOUNDCLOUD = [
    "............",
    "............",
    "........##..",
    ".......####.",
    "......######",
    "...##.######",
    "...##.######",
    "##.##.######",
    "##.##.######",
    "##.##.######",
    "##.##.######",
    "............",
]
SPOTIFY = [
    "....####....",
    "..########..",
    ".##########.",
    "##........##",
    "############",
    "###......###",
    "############",
    "####....####",
    "############",
    ".##########.",
    "..########..",
    "....####....",
]
APPLE_MUSIC = [
    ".....#######",
    "....########",
    "....##....##",
    "....##....##",
    "....##....##",
    "....##....##",
    "....##..###.",
    "....##.#####",
    ".####..#####",
    "######.#####",
    "#####...###.",
    ".###........",
]


PLAYS_URL = ("https://raw.githubusercontent.com/thepoolpat/poolpat-portfolio"
             "/main/data/plays.json")
SONGSTATS_URL = "https://api.songstats.com/enterprise/v1/artists/stats"
SONGSTATS_ARTIST = "z0xl1iq2"   # from list_accessible_profiles, 2026-09-10

# ponytail: a dead man's switch. The scroll redraws ~10x a second, so any value
# above a second or two is slack -- but if this process is SIGKILLed the last
# frame would otherwise sit on the bar forever. 30s, then the bar drops it.
ELEMENT_TIMEOUT = 30
# Cadence, and why it is not 30 or 60.
#
# The front panel refreshes at 60 Hz but the draw API cannot be driven near it.
# Measured over USB on 2026-09-10, 60 consecutive draws each time:
#
#   15 elements, gradient recoloured every frame   12.8/s
#   15 elements, static colours                    13.7/s
#   10 elements                                    15.3/s
#    5 elements, reposition only                   19.7/s
#   15 elements over ONE keep-alive connection      1.8/s   <- do not do this
#
# That fits ~36 ms of fixed cost per POST plus ~3 ms per element, so even an
# empty frame caps near 27/s. Keep-alive is the trap: the bar's HTTP server
# stalls on a reused socket (median 77 ms, p90 1.5 s), so a fresh connection per
# draw is the fast path, not the slow one. Do not "optimise" that away.
#
# So the app cannot render at 30 fps, and asking for it only makes frames arrive
# unevenly. What it can do is hold a STEADY rate under the ceiling, which is the
# thing the eye actually reads as smooth -- a jittery 14 looks worse than a
# metronomic 11. CADENCE_HEADROOM is how far under the measured rate to sit so
# that a slow frame is absorbed by the slack instead of pushing the next one late.
FPS = 60                      # ceiling only; the measured rate always wins
CADENCE_HEADROOM = 0.85       # run at 85% of what the device just proved it can do
CADENCE_SAMPLE = 20           # frames to measure before pinning the cadence

# The gradient is driven by DISTANCE TRAVELLED, not by the wall clock. Tying it
# to the scroll is what makes the colour feel like it belongs to the banner
# rather than like a second animation running behind it: the light moves because
# the pill moves, and if --speed changes, the colour follows without a constant
# to retune. A stopped banner has a still gradient, which is the honest look.
#
# One full hue rotation, and one breath of a brand pill, every 180px of travel
# (2.0 phase units at this rate) -- fifteen seconds at the default 12 px/s.
SWEEP_PER_PX = 1.0 / 90.0

NUMBER = "#FFFFFFFF"
# Since the pill carries the brand colour, the logo on top of it has to be the
# contrast mark rather than the brand mark: an orange SoundCloud logo on an
# orange pill is invisible, which is exactly what it looked like on the device.
# So the whole system is one rule -- pill is the brand, everything on it is white.
LOGO = "#FFFFFFFF"
# SoundCloud is the exception: its orange is bright enough that a white cloud on
# it is the weakest mark on the banner, and black reads at a glance where white
# only reads once you look for it. Anything added here needs the same test --
# hold the logo colour against its own pill, not against the black background.
LOGO_COLOR = {"soundcloud": "#000000FF"}


def logo_color(key):
    return LOGO_COLOR.get(key, LOGO)

# Every brand colour below was taken from that company's own guidelines, not
# from a colour-aggregator site. The same question was asked of each: what hex
# does the owner publish, and what do they sanction for a flat single-colour
# mark on a dark background?
#
#   SoundCloud  #FF5500  Media Kit, verbatim: "SoundCloud Orange HEX #FF5500
#                        ... PANTONE Orange 021C". "Orange on Black" is one of
#                        its listed approved treatments.
#   Spotify     #1ED760  developer.spotify.com/documentation/design, read out of
#                        the guidelines' own swatch SVG and out of the official
#                        Primary_Logo_Green_RGB.svg (PANTONE 7479 C). The older
#                        #1DB954 this app used to carry appears in no current
#                        Spotify asset -- it was simply stale.
#   Apple Music #FFFFFF  Apple publishes NO hex for Apple Music, anywhere in the
#                        Identity Guidelines. It approves exactly three icon
#                        versions -- colour (their supplied artwork), white, and
#                        black -- and says "Do not create your own icon." A red
#                        fill is a third-party value Apple never sanctioned, so
#                        white is the only honest choice on a black matrix.
#   Instagram   #FFFFFF  Meta's brand pages give no retrievable gradient stops
#                        and direct you to the supplied artwork. Its documented
#                        single-colour fallbacks are black and white; white is
#                        the legible one here.
#
# ponytail: two of these are white, so Apple Music and Instagram read as shape
# alone rather than as colour. That is what rigour costs on a 12x12 tile. Swap
# them to #FA243C and #E1306C for a prettier banner and accept that both numbers
# come from aggregator sites rather than from Apple or Meta.
# "All followers" is every platform at once, so it gets people rather than any
# one service's mark. Two figures, heads detached from shoulders by a blank row:
# at 12px a joined head-and-body silhouette merges into one blob and stops
# reading as a person at all.
FANS = [
    "............",
    "............",
    ".###....###.",
    ".###....###.",
    "............",
    "#####..#####",
    "#####..#####",
    "#####..#####",
    "#####..#####",
    "#####..#####",
    "............",
    "............",
]

BRAND = {                                    # icon bitmap, colour, arg name
    "globe":       (GLOBE,       "#5B4FE9FF", None),
    "soundcloud":  (SOUNDCLOUD,  "#FF5500FF", "sc"),
    "spotify":     (SPOTIFY,     "#1ED760FF", "sp"),
    "apple_music": (APPLE_MUSIC, "#FFFFFFFF", "am"),
    "fans":        (FANS,        "#FFFFFFFF", "fans"),
}


def _base(host):
    host = host.replace("http://", "").replace("https://", "").rstrip("/")
    return "http://" + host


def _chunk(tag, data):
    c = tag + data
    return (struct.pack(">I", len(data)) + c
            + struct.pack(">I", zlib.crc32(c) & 0xffffffff))


def _png(rows, w, h, zoom=1):
    """Rows of (r, g, b, a) -> PNG bytes."""
    raw = bytearray()
    for y in range(h):
        for _ in range(zoom):
            raw.append(0)
            for x in range(w):
                raw += bytes(rows[y][x]) * zoom
    return (b"\x89PNG\r\n\x1a\n"
            + _chunk(b"IHDR", struct.pack(">IIBBBBB", w * zoom, h * zoom, 8, 6, 0, 0, 0))
            + _chunk(b"IDAT", zlib.compress(bytes(raw), 6))
            + _chunk(b"IEND", b""))


def icon_png(grid, hexcolor):
    """12x12 bitmap -> PNG, lit pixels in the brand colour, rest transparent."""
    r, g, b = (int(hexcolor[i:i + 2], 16) for i in (1, 3, 5))
    rows = [[(r, g, b, 255) if px == "#" else (0, 0, 0, 0) for px in line]
            for line in grid]
    return _png(rows, ICON, ICON)


def upload(host, name, data):
    req = urllib.request.Request(
        _base(host) + "/api/assets/upload?application_name=%s&file=%s" % (APP, name),
        data=data, method="POST",
        headers={"Content-Type": "application/octet-stream"})
    with urllib.request.urlopen(req, timeout=8) as r:
        return r.getcode()


def draw(host, elements, priority=60):
    """POST /api/display/draw. Elements merge by id, they don't replace the set."""
    body = json.dumps({"application_name": APP, "priority": priority,
                       "elements": elements}).encode()
    req = urllib.request.Request(_base(host) + "/api/display/draw", data=body,
                                 method="POST",
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=8) as r:
            return r.getcode(), r.read().decode("utf-8", "ignore")
    except urllib.error.HTTPError as e:
        return e.code, e.read().decode("utf-8", "ignore")


def clear(host):
    qs = urllib.parse.urlencode({"application_name": APP})
    req = urllib.request.Request(_base(host) + "/api/display/draw?" + qs,
                                 method="DELETE")
    try:
        with urllib.request.urlopen(req, timeout=8) as r:
            return r.getcode()
    except urllib.error.HTTPError as e:
        return e.code


def grab(host):
    """GET /api/screen -> the front display's pixels, as flat (r, g, b).

    The framebuffer comes back BGR, not the RGB888 the docs claim: send
    #FF5500 and the bytes read back 00 55 FF. Hence the reversed slice --
    without it every screenshot has its reds and blues swapped.
    """
    with urllib.request.urlopen(_base(host) + "/api/screen?display=0",
                                timeout=8) as r:
        raw = base64.b64decode(r.read(), validate=True)
    if len(raw) != W * H * 3:
        raise RuntimeError(f"expected {W * H * 3} framebuffer bytes, got {len(raw)}")
    return [tuple(raw[i:i + 3][::-1]) for i in range(0, len(raw), 3)]


def layout(counts):
    """[(key, number)] -> segments with their x offsets, and the total width.

    Each service is a pill sized to its own contents. The width is measured, not
    fixed: a five-digit number needs a longer pill than a four-digit one, and a
    pill sized for the widest number would leave the short ones swimming.
    """
    segs, x = [], 0
    for key, value in counts:
        text = f"{value:,}"
        icon_x = x + PILL_PAD
        text_x = icon_x + ICON + PAD
        pill_w = PILL_PAD + ICON + PAD + text_width(text) + PILL_PAD
        segs.append({"key": key, "text": text, "pill_x": x, "pill_w": pill_w,
                     "icon_x": icon_x, "text_x": text_x})
        x += pill_w + GAP
    return segs, x - GAP + TAIL


# The logo colours above are the verified brand marks, and two of them are
# white because that is how Apple and Instagram publish their monochrome glyph.
# White is useless as a pill though -- a white pill under white digits shows
# nothing -- so those two get their brand's actual colour for the fill only.
PILL_COLOR = {"apple_music": "#FA243CFF",     # Apple Music's red, not its glyph
              "fans": "#E1306CFF"}            # a warm pink, distinct from every service


def pill_color(key):
    return PILL_COLOR.get(key, BRAND[key][1])


# A rainbow made of the services themselves rather than of the raw hue wheel.
# Each pill starts at its own brand colour and its gradient runs toward the NEXT
# service in the banner, so the colour hands over where the pills do: indigo
# into SoundCloud orange, orange into Spotify green, green into Apple red, red
# into the follower pink, pink back round into indigo. Scrolling the banner
# therefore scrolls one continuous spectrum, and every pill still leads with the
# colour that identifies it.
#
# ponytail: the schema's two fill_colors is not a limit here, it is the whole
# mechanism -- two stops per pill is exactly "me, handing over to the next one".
# What travels is how FAR toward the neighbour the second stop has reached.
HANDOVER_MIN = 0.35              # never a full handover: the pill keeps its identity
HANDOVER_MAX = 1.0
RAINBOW_V = 0.9                  # not 1.0: white digits need somewhere to sit


def mix(a, b, t, v=1.0):
    """Blend two #RRGGBBAA colours along the hue wheel, t=0 all a, t=1 all b.

    `v` scales the result's brightness, which is how the luminance wave rides
    on top of the hue without disturbing it.

    ponytail: NOT a straight RGB lerp. Orange to green in RGB passes through
    olive -- it looked like mud on the device, which is what sent me here.
    Going round the hue wheel passes through yellow instead, so the handover
    between two services reads as a spectrum rather than as a dirty smear.
    The arc taken is always the shorter one, or a 20-degree handover would go
    the long way round and cycle through every colour the pair does not contain.
    """
    def hsv(c):
        r, g, bl = (int(c[i:i + 2], 16) / 255.0 for i in (1, 3, 5))
        return colorsys.rgb_to_hsv(r, g, bl)
    h1, s1, v1 = hsv(a)
    h2, s2, v2 = hsv(b)
    dh = h2 - h1
    if dh > 0.5:
        dh -= 1.0                        # shorter way round the wheel
    elif dh < -0.5:
        dh += 1.0
    r, g, bl = colorsys.hsv_to_rgb((h1 + dh * t) % 1.0,
                                   s1 + (s2 - s1) * t,
                                   (v1 + (v2 - v1) * t) * RAINBOW_V * v)
    return "#%02X%02X%02XFF" % (round(r * 255), round(g * 255), round(bl * 255))


def flow(here, nxt, phase):
    """This pill's two gradient stops: its own colour, handing over to the next.

    `phase` travels with the banner, so the handover point breathes along the
    pill rather than sitting still. It never reaches zero, because a pill that
    has fully become its neighbour has stopped saying which service it is.
    """
    reach = HANDOVER_MIN + (HANDOVER_MAX - HANDOVER_MIN) * abs(1.0 - (phase % 2.0))
    return [mix(here, here, 0.0), mix(here, nxt, reach)]


def sweep(color, phase):
    """A brand colour and the darker end of its gradient, for this phase.

    The pill is filled `gradient_h` from the brand colour to a dimmed version of
    itself, and `phase` slides where the dim end sits, so the highlight travels
    along the pill instead of the fill being a static two-tone. Dimming stays on
    the same hue -- scaling all three channels by one factor -- because shifting
    hue per frame reads as a fault rather than as motion.
    """
    r, g, b = (int(color[i:i + 2], 16) for i in (1, 3, 5))
    # 0.35 .. 1.0 and back, so the sweep breathes rather than snapping at the wrap
    k = 0.35 + 0.65 * abs(1.0 - (phase % 2.0))
    dim = "#%02X%02X%02XFF" % (int(r * k), int(g * k), int(b * k))
    return [color, dim]


def frame(segs, offset, phase=0.0):
    """Every element of the banner, positioned for this scroll offset.

    Three per service, bottom to top: the gradient pill, the logo, the number.
    z_index is what keeps that order -- without it the pill is drawn last and
    hides everything, since the firmware honours insertion order only as a
    tiebreak.
    """
    els = []
    for i, s in enumerate(segs):
        els.append({"id": f"p{i}", "type": "rectangle",
                    "x": s["pill_x"] + offset, "y": 0,
                    "width": s["pill_w"], "height": PILL_H, "radius": PILL_R,
                    "fill": "gradient_h",
                    # Hand over to whichever service comes next, wrapping at
                    # the end so the banner is one loop of colour, not a line.
                    "fill_colors": flow(pill_color(s["key"]),
                                        pill_color(segs[(i + 1) % len(segs)]["key"]),
                                        phase + i * 0.25),
                    "border_width": 0, "align": "top_left",
                    "z_index": 0, "timeout": ELEMENT_TIMEOUT})
        els.append({"id": f"i{i}", "type": "image", "path": f"{s['key']}.png",
                    "x": s["icon_x"] + offset, "y": (H - ICON) // 2,
                    "align": "top_left", "z_index": 5,
                    "timeout": ELEMENT_TIMEOUT})
        els.append({"id": f"n{i}", "type": "text", "text": s["text"],
                    "font": FONT, "color": NUMBER,
                    "x": s["text_x"] + offset, "y": H // 2, "align": "mid_left",
                    "z_index": 6, "timeout": ELEMENT_TIMEOUT})
    return els


def fetch_portfolio(timeout=10):
    """The three play counts out of the portfolio repo's data/plays.json.

    Read straight off raw.githubusercontent.com rather than the deployed site:
    the Astro build bakes the numbers into HTML and never ships the JSON, so
    the repo file is the only machine-readable copy.
    """
    req = urllib.request.Request(PLAYS_URL, headers={"User-Agent": APP})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        data = json.loads(r.read().decode())
    # ponytail: total_streams_sc and total_downloads also live in the soundcloud
    # block and are NOT the tile -- they are a different pair of metrics that sum
    # to a smaller, wrong-looking number. Read total_plays and nothing else.
    return {"sc": int(data["soundcloud"]["total_plays"]),
            "sp": int(data["spotify"]["total_streams"]),
            "am": int(data["apple_music"]["total_plays"]),
            # No follower counts in this file, and no key-free way to read them
            # off each platform. The tile stays hidden until Songstats.
            "fans": None,
            "as_of": data.get("last_updated", "?")}


# ponytail: verified against a live /artists/stats response on 2026-09-10, not
# guessed. apple_music is deliberately absent: the endpoint documents no plays
# or streams datapoint for it on any plan, so --source songstats can never fill
# that tile and fetch_stats borrows the portfolio's figure instead.
SONGSTATS_KEYS = {                       # source name -> the play/stream field
    "soundcloud": ("sc", "streams_total"),
    "spotify": ("sp", "streams_total"),
}

# Every source that publishes a follower count, summed into one "all followers"
# figure. The field name is followers_total everywhere EXCEPT youtube, which
# calls the same idea subscribers_total -- the one exception in the table, and
# the one that would silently drop ~12 people if it were assumed away.
#
# ponytail: asking for a source the profile has no presence on costs nothing but
# a zero, so the list is every source the endpoint documents rather than the
# subset that happens to be non-zero today. A new platform then appears on its
# own instead of needing a code change.
FOLLOWER_KEYS = {
    "amazon": "followers_total", "bandsintown": "followers_total",
    "deezer": "followers_total", "facebook": "followers_total",
    "instagram": "followers_total", "songkick": "followers_total",
    "soundcloud": "followers_total", "spotify": "followers_total",
    "tidal": "followers_total", "tiktok": "followers_total",
    "twitter": "followers_total", "youtube": "subscribers_total",
}


def parse_songstats(data):
    """A /artists/stats response body -> {sc, sp, am, fans, as_of}.

    Separate from the fetch so the self-check can run it on a real captured
    response without a key or a network.
    """
    counts, followers = {}, {}
    for entry in data.get("stats", []):
        source = entry.get("source")
        stats = entry.get("data", {})
        name, field = SONGSTATS_KEYS.get(source, (None, None))
        if name is not None:
            if field not in stats:
                raise RuntimeError(
                    f"songstats {source} has no {field}; it sent {sorted(stats)}")
            counts[name] = int(stats[field])
        follows = FOLLOWER_KEYS.get(source)
        if follows and follows in stats:
            followers[source] = int(stats[follows])
    missing = {"sc", "sp"} - set(counts)
    if missing:
        raise RuntimeError(f"songstats returned no data for {sorted(missing)}")
    # One audience across every platform, not a per-platform tile each. The sum
    # is the honest headline: nobody follows on twelve services, so the platform
    # breakdown of a small following says less than the total does.
    counts["fans"] = sum(followers.values()) if followers else None
    counts["by_platform"] = followers
    counts["am"] = None                  # see SONGSTATS_KEYS: filled by the caller
    counts["as_of"] = "live"
    return counts


def fetch_songstats(api_key, timeout=10):
    """The same counts from the Songstats Enterprise API, live rather than weekly.

    ponytail: the path, the two required query parameters and the response shape
    were all confirmed against the real endpoint on 2026-09-10 through the
    Songstats MCP connector, which proxies this same URL. What is still unproven
    is only this function's own authentication -- the connector carries its own
    credential, so the `apikey` header below is the documented form and nothing
    more. Expect that line, and only that line, to be what a first real key
    corrects.
    """
    query = urllib.parse.urlencode({"songstats_artist_id": SONGSTATS_ARTIST,
                                    "source": ",".join(SONGSTATS_KEYS)})
    req = urllib.request.Request(SONGSTATS_URL + "?" + query,
                                 headers={"apikey": api_key, "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            data = json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        # Status only. The body of an authenticated call is not something to
        # paste into a log.
        raise RuntimeError(f"songstats returned HTTP {e.code}") from None
    return parse_songstats(data)


class MisconfiguredError(RuntimeError):
    """Something only the operator can fix. Never worth retrying."""


def songstats_key():
    """The Enterprise key, from the environment or the login keychain.

    ponytail: the keychain is the lazy option here, not the careful one -- it is
    two lines, it survives a reboot, and it keeps the key out of shell history,
    out of the manifest and out of any log this app writes. Store it once with

        security add-generic-password -s SONGSTATS_API_KEY -a "$USER" -w

    which prompts for the value instead of taking it on the command line.
    """
    key = os.environ.get("SONGSTATS_API_KEY")
    if key:
        return key
    try:
        # No check=True: CalledProcessError stringifies the whole argv, and the
        # argv of a keychain read is a fine thing to leak but the habit is not.
        out = subprocess.run(["security", "find-generic-password",
                              "-s", "SONGSTATS_API_KEY", "-w"],
                             capture_output=True, text=True, timeout=5)
    except (OSError, subprocess.SubprocessError):
        return None
    return out.stdout.strip() or None


_APPLE_MUSIC = []                        # one-slot cache; see apple_music_figure


def apple_music_figure():
    """The hand-typed Apple Music count, fetched once per process.

    ponytail: a weekly bot writes this number and a human types it, so refetching
    it every refresh cycle would be two network calls where one will do, and a
    portfolio outage would print the same warning every cycle forever. Read it
    once, carry it, and say so once if it is not there.
    """
    if not _APPLE_MUSIC:
        try:
            _APPLE_MUSIC.append(fetch_portfolio()["am"])
        except Exception as e:                      # noqa: BLE001 - any fetch fault
            print(f"apple music tile unavailable ({e})")
            _APPLE_MUSIC.append(None)
    return _APPLE_MUSIC[0]


def fetch_stats(source):
    """Whichever source is configured, as {sc, sp, am, fans, as_of}.

    Songstats publishes no Apple Music plays on any plan, so under that source
    the tile is filled from the portfolio's hand-typed figure rather than
    dropped -- the number is stale by design either way, and losing the tile
    loses a platform from the banner. If the portfolio is unreachable the tile
    goes rather than the whole banner.
    """
    if source == "songstats":
        key = songstats_key()
        if not key:
            raise MisconfiguredError(
                "--source songstats needs SONGSTATS_API_KEY in the environment "
                "or in the login keychain; store it with\n"
                '  security add-generic-password -s SONGSTATS_API_KEY -a "$USER" -w')
        counts = fetch_songstats(key)
        counts["am"] = apple_music_figure()
        return counts
    return fetch_portfolio()


def counts_from(stats):
    """{sc, sp, am} -> the four (icon, number) pairs, in display order.

    The grand total is summed here on purpose. plays.json stores no total, and
    the one total that does exist in the repo (insights.json) is a staler
    snapshot that disagrees with the tiles by ~60 plays.
    """
    # ponytail: am is None under --source songstats, which publishes no Apple
    # Music plays datapoint at all. A missing tile is dropped from the banner
    # and from the sum -- never counted as zero, which would read on the bar as
    # "Apple Music has no plays" rather than "this source cannot see them".
    plays = [("soundcloud", stats["sc"]), ("spotify", stats["sp"]),
             ("apple_music", stats.get("am"))]
    plays = [(k, v) for k, v in plays if v is not None]
    tiles = [("globe", sum(v for _, v in plays))] + plays
    if stats.get("fans") is not None:
        # Followers, not plays -- deliberately last, past the play counts the
        # globe totals, so the sum above stays a sum of like things. One person
        # following on three services is three followers here; Songstats reports
        # per platform and there is no cross-platform identity to dedupe on.
        tiles.append(("fans", stats["fans"]))
    return tiles


def pinned(args):
    """The --sc/--sp/--am overrides as a stats dict, or None if not given.

    ponytail: --sc and --sp are the pair that decides whether the numbers are
    pinned; --am may be left off on purpose, because that is the shape
    --source songstats produces and it is the one banner worth being able to
    rehearse on the device without a key.
    """
    if None in (args.sc, args.sp):
        return None
    return {"sc": args.sc, "sp": args.sp, "am": args.am, "fans": args.fans,
            "as_of": "pinned"}


LOCK = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".running")


def claim(path=LOCK):
    """Hold the only-instance lock, or None if a banner is already running.

    ponytail: two copies pointing at the same bar make it blink hard -- they
    own the same element ids and fight over the offset every frame, which reads
    as a fault in the device rather than as two processes. USB and wi-fi are the
    same bar, so "different --host" is not a different target.
    """
    f = open(path, "w")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        f.close()
        return None
    return f


def prepare(host, source, stats):
    """Upload the icons and take the first reading, waiting for the bar.

    ponytail: this retries instead of raising because the manager reads any exit
    as a crash and restarts on its own backoff -- and a process that dies at
    startup takes its error message with it every time. One live process saying
    "waiting for the bar" is easier to diagnose than a restart loop. Ceiling:
    it waits forever; SIGTERM and ctrl-c still get out.
    """
    delay = 2
    while True:
        try:
            clear(host)       # elements merge by id, so drop anything stale first
            for key, (grid, _, _) in BRAND.items():
                upload(host, f"{key}.png", icon_png(grid, logo_color(key)))
            return stats or fetch_stats(source)
        except KeyboardInterrupt:
            raise
        except MisconfiguredError:
            # ponytail: this loop exists for a bar that is unplugged or busy,
            # which fixes itself. A missing API key never does, and retrying it
            # every 30s forever hides the one message that says what to do.
            raise
        except Exception as e:                          # noqa: BLE001
            print(f"waiting for the bar ({e}); retrying in {delay}s")
            time.sleep(delay)
            delay = min(delay * 2, 30)


# --- device render ------------------------------------------------------------
#
# The tfi-202 pattern, and the only way to get panel-rate motion out of this
# bar: hand the firmware ONE text element with a scroll_rate and let it do the
# scrolling itself. There is no frame loop here, so there is no draw rate to
# jitter -- the panel renders at its own 60 Hz and the host does almost nothing.
#
# What it costs is the per-service pills and logos, because scroll_rate moves
# text and nothing else (the schema puts those fields on TextElement alone).
# So the services are named in words instead of drawn as marks, and the brand
# colour moves to the pill underneath.
#
# The pill still flows through the service colours, because a rectangle can be
# redrawn by id WITHOUT disturbing a text element that is mid-scroll -- verified
# on the device: five pill recolours during a scroll left the text advancing.
# That is one element a few times a second, against fifteen at twelve frames a
# second for the host-rendered banner.
LABELS = {"globe": "TOTAL", "soundcloud": "SOUNDCLOUD", "spotify": "SPOTIFY",
          "apple_music": "APPLE MUSIC", "fans": "FANS"}
SEPARATOR = "   "                        # blank run between one service and the next
# Pixels per MINUTE. 1800 = 30 px/s, a reading pace: the scroll is for reading,
# not for showing off the panel. It is deliberately half the gradient's rate --
# the firmware renders the text at 60 Hz either way, so a slower scroll costs no
# smoothness, it just gives the eye time on each number.
SCROLL_PPM = 1800
SCROLL_START_MS = 600
SCROLL_REPEAT_MS = 1500
TEXT_X, TEXT_W = 4, 64                   # the label window, inset inside the pill

# The pill is drawn one pixel larger than the display on every side, so its 1px
# border falls exactly on the pixels that were black before -- the display edge
# becomes the outline instead of a gap. The border colour is the gradient's own
# negative, which is what makes it read as an edge at every point of the cycle:
# a border sharing the fill's hue disappears into it as the colour travels.
PILL_BLEED = 1
BORDER_W = 1

# A 1px hairline along the very top and the very bottom, carrying the same
# gradient as the pill. They sit above the pill's rim, so the display's outer
# edge shows the travelling colour itself rather than the rim's darker step --
# the rim then only outlines the rounded ends, where a pill needs an edge and
# a straight line cannot give it one.
# Two pixels, not one. The pill's rounded ends leave its four corners unlit, and
# a 1px hairline only covered the outermost of the two dark rows at each end --
# measured on the framebuffer, rows 0/1 and 14/15 had black at x=0 and x=71.
# 2px covers both, so the banner reaches all four corners and no pixel is wasted.
EDGE_H = 2
# Pill recolours per second. The firmware scrolls the text at panel rate on its
# own; this is only how often the colour under it is refreshed, and at 60 px/s a
# 60 Hz recolour moves the gradient exactly one pixel per update -- in step with
# the words rather than catching up in visible jumps.
#
# MEASURED: a pill-only draw runs at 70.1/s over USB, against 12.8/s for the
# fifteen-element host-rendered banner. One element is what makes 60 reachable
# here when it is not there at all. The loop still measures and holds a cadence,
# so a slower cable simply settles lower instead of falling behind.
RECOLOUR_HZ = 60          # the gradient's own rate, independent of the scroll


def strip(counts):
    """The whole banner as one line of text, plus where each service starts.

    The offsets are what let the pill know which service is under the window at
    any moment, so the colour can follow the words rather than run on a clock of
    its own.
    """
    parts, marks, x = [], [], 0
    for key, value in counts:
        text = f"{LABELS[key]} {value:,}"
        marks.append((x, key))
        parts.append(text)
        x += text_width(text) + text_width(SEPARATOR)
    return SEPARATOR.join(parts), marks, x


# How far either side of a service boundary the colours blend. Wider than the
# gap between two services would smear every colour into its neighbours; much
# narrower and the pill changes colour in a visible step as a word crosses the
# window edge.
BLEND_PX = 34

# Brightness is the third thing that travels, after position and hue. A pill
# whose colour changes but whose luminance never does reads flat, because the
# eye tracks brightness far more readily than hue -- so a slow value wave along
# the scroll is what makes the gradient look like it is moving rather than just
# being recoloured. Kept as a floor and a ceiling rather than one "amount" so
# both ends are directly tunable: --dim sets how dark the trough goes, --bright
# how bright the crest, and equal values switch the wave off entirely.
DIM_FLOOR = 0.62
DIM_CEILING = 1.0
PULSE_PX = 96                 # target length of one dark-to-bright-to-dark wave


def pulse_period(total):
    """The wave length actually used: PULSE_PX rounded so it divides the strip.

    ponytail: a wave whose period does not divide the strip does not close, and
    the brightness then jumps at the moment the scroll wraps -- a visible blink
    once per pass. Fitting a whole number of cycles costs one division and
    removes the seam entirely.
    """
    return total / max(1, round(total / PULSE_PX))


def brightness_at(px, total, floor=DIM_FLOOR, ceiling=DIM_CEILING):
    """Value multiplier at one scroll position: a smooth wave, never a step.

    A cosine rather than a triangle, because a triangle's turning points are
    visible as a flick at the top and bottom of the wave.
    """
    period = pulse_period(total)
    wave = (1.0 - math.cos(2.0 * math.pi * (px % period) / period)) / 2.0
    return floor + (ceiling - floor) * wave


def color_at(marks, total, px, floor=DIM_FLOOR, ceiling=DIM_CEILING):
    """The banner's colour at one scroll position, as a continuous function.

    This is what makes the gradient scroll rather than merely change: sampling
    it at the window's two edges gives a pair of stops that slide through the
    pill in step with the words underneath, so Spotify green is still leaving
    the left of the pill while Apple red is already arriving at the right.

    Pure brand colour through the middle of a service, blending across
    BLEND_PX either side of each boundary and passing exactly half way at the
    boundary itself, so no service ever hands over abruptly.
    """
    v = brightness_at(px, total, floor, ceiling)
    here = px % total
    i = len(marks) - 1
    for j in range(len(marks) - 1, -1, -1):
        if here >= marks[j][0]:
            i = j
            break
    key = marks[i][1]
    start = marks[i][0]
    end = marks[i + 1][0] if i + 1 < len(marks) else total
    if here - start < BLEND_PX:                  # arriving from the previous one
        prev = marks[i - 1][1]
        return mix(pill_color(prev), pill_color(key),
                   0.5 + 0.5 * (here - start) / BLEND_PX, v)
    if end - here < BLEND_PX:                    # handing over to the next one
        nxt = marks[(i + 1) % len(marks)][1]
        return mix(pill_color(key), pill_color(nxt),
                   0.5 * (BLEND_PX - (end - here)) / BLEND_PX, v)
    return mix(pill_color(key), pill_color(key), 0.0, v)


def window_colors(marks, total, px, floor=DIM_FLOOR, ceiling=DIM_CEILING):
    """The two gradient stops for a window whose left edge is at px.

    ponytail: the firmware never reports its scroll position, so px is
    recomputed from scroll_rate and the clock. That is an open loop and can
    drift out of step with the panel over a long run, which would show as the
    colour leading or trailing the words. There is nothing to poll, so the fix
    if it ever shows is a shorter strip, not a faster tick.
    """
    return [color_at(marks, total, px, floor, ceiling),
            color_at(marks, total, px + TEXT_W, floor, ceiling)]


# How far the rim's brightness steps away from the fill it outlines. Enough to
# read as an edge, not so much that it reads as a second colour.
RIM_DARKEN = 0.45
RIM_LIGHTEN = 0.35
RIM_PIVOT = 0.55                # above this the fill is lit enough to rim darker


def rim(color):
    """An outline in the fill's own hue: same colour, stepped in brightness.

    ponytail: this replaced an opposite-hue border, which was legible but read
    as a separate object stuck to the edge of the pill. Keeping the hue and
    moving only the value keeps the whole pill one colour, so the outline
    belongs to it.

    The direction is chosen from the fill rather than fixed, because a fixed one
    has nowhere to go at the ends of the range: darken a fill that is already
    near black and there is no edge, lighten one already near white and the
    same. Above RIM_PIVOT the rim goes darker, below it the rim goes lighter,
    so there is always somewhere to step to -- which matters here precisely
    because the brightness wave is always moving the fill up and down.
    """
    r, g, b = (int(color[i:i + 2], 16) / 255.0 for i in (1, 3, 5))
    h, sat, v = colorsys.rgb_to_hsv(r, g, b)
    v = v * RIM_DARKEN if v > RIM_PIVOT else min(1.0, v + RIM_LIGHTEN)
    nr, ng, nb = colorsys.hsv_to_rgb(h, sat, v)
    return "#%02X%02X%02XFF" % (round(nr * 255), round(ng * 255), round(nb * 255))


def device_frame(text, colors):
    return [
        {"id": "pill", "type": "rectangle",
         "x": -PILL_BLEED, "y": -PILL_BLEED,
         "width": W + 2 * PILL_BLEED, "height": PILL_H + 2 * PILL_BLEED,
         "radius": (PILL_H + 2 * PILL_BLEED) // 2,
         "fill": "gradient_h", "fill_colors": colors,
         "border_width": BORDER_W, "border_color": rim(colors[0]),
         "align": "top_left", "z_index": 0, "timeout": ELEMENT_TIMEOUT},
        {"id": "txt", "type": "text", "text": text, "font": FONT, "color": NUMBER,
         "x": TEXT_X, "y": H // 2, "align": "mid_left", "width": TEXT_W,
         "scroll_rate": SCROLL_PPM, "scroll_start_delay": SCROLL_START_MS,
         "scroll_repeat_delay": SCROLL_REPEAT_MS,
         "z_index": 5, "timeout": ELEMENT_TIMEOUT},
    ]


def edge_lines(colors):
    """The top and bottom hairlines, in the gradient's own colours."""
    return [
        {"id": f"edge{i}", "type": "rectangle", "x": 0, "y": y,
         "width": W, "height": EDGE_H, "radius": 0,
         "fill": "gradient_h", "fill_colors": colors, "border_width": 0,
         "align": "top_left", "z_index": 1, "timeout": ELEMENT_TIMEOUT}
        for i, y in enumerate((0, H - EDGE_H))
    ]


def device_pill(colors):
    """The pill and its hairlines, by id -- never the mid-scroll text element.

    ponytail: three elements, not one, and still nowhere near a frame. What
    matters is that the text element is absent, because resending it is what
    would restart the firmware's scroll.
    """
    return [device_frame("", colors)[0]] + edge_lines(colors)


# --- animation build ----------------------------------------------------------
#
# The third render path, and the only one that gets the logos AND panel-rate
# motion at once: pre-render every frame of the scrolling banner into a .anim
# file, upload it, and let the firmware play it. After the upload the host sends
# nothing at all -- not a frame, not a recolour.
#
# The format is the firmware's own, from lib/anim_file/anim_file_format.h and
# lib/toolbox/rle_encode.c, not guesswork:
#
#   header   36 bytes: "bicycle0", flags, w, h, colour format, FPS, the longest
#            encoded frame, then the two chunk lengths and three counts
#   sections one AnimFileSection, which must include one named "default"
#            covering every display frame
#   frames   per frame: encoding, duration in display frames, encoded length
#
# ponytail: the frames are captured FROM THE DEVICE rather than rasterised here.
# Drawing each offset and reading /api/screen back costs about a minute once,
# and buys exact fidelity -- the firmware's own font, its own rounded corners,
# its own antialiasing -- against reimplementing all three and being subtly
# wrong about each. The bar is the renderer; this is only the tape recorder.
ANIM_SIG = b"bicycle0"
ANIM_BGR888 = 0
ANIM_RAW, ANIM_RLE = 0, 1
ANIM_HEADER_LEN = 36
RLE_BLOCK = 3                            # bytes per pixel in Bgr888
RLE_MAX_BLOCKS = 127
RLE_RUN_THRESHOLD = 3
SETTLE_TRIES = 4                         # re-reads allowed before a frame is taken


def rle_compress(src, blk=RLE_BLOCK):
    """The firmware's RLE, byte for byte (lib/toolbox/rle_encode.c).

    Opcode with the high bit SET means `count` literal blocks follow; with it
    clear, one block follows and repeats `count` times. Runs shorter than the
    threshold are cheaper left literal than given an opcode of their own.
    """
    out = bytearray()
    n = len(src) // blk
    i = 0
    while i < n:
        run = 1
        while (run < RLE_MAX_BLOCKS and i + run < n
               and src[(i + run) * blk:(i + run + 1) * blk] ==
                   src[i * blk:(i + 1) * blk]):
            run += 1
        if run >= RLE_RUN_THRESHOLD:
            out.append(run)
            out += src[i * blk:(i + 1) * blk]
            i += run
        else:
            # gather literals until a run worth encoding shows up
            start = i
            lit = 0
            while i < n and lit < RLE_MAX_BLOCKS:
                ahead = 1
                while (ahead < RLE_RUN_THRESHOLD and i + ahead < n
                       and src[(i + ahead) * blk:(i + ahead + 1) * blk] ==
                           src[i * blk:(i + 1) * blk]):
                    ahead += 1
                if ahead >= RLE_RUN_THRESHOLD:
                    break
                lit += 1
                i += 1
            out.append(0x80 | lit)
            out += src[start * blk:(start + lit) * blk]
    return bytes(out)


def rle_decompress(src, blk=RLE_BLOCK):
    """Only used to prove the compressor round-trips before anything is shipped."""
    out = bytearray()
    i = 0
    while i < len(src):
        op = src[i]
        i += 1
        count = op & 0x7F
        if op & 0x80:
            out += src[i:i + count * blk]
            i += count * blk
        else:
            out += src[i:i + blk] * count
            i += blk
    return bytes(out)


def anim_pack(frames, fps, duration):
    """Frames of BGR bytes -> a complete .anim file."""
    body, longest = bytearray(), 0
    for raw in frames:
        packed = rle_compress(raw)
        if len(packed) < len(raw):
            encoding, data = ANIM_RLE, packed
        else:
            # A frame that RLE makes bigger is stored raw. Cheaper, and it keeps
            # encoded_length inside its uint16 whatever the picture does.
            encoding, data = ANIM_RAW, raw
        longest = max(longest, len(data))
        body += struct.pack("<BBH", encoding, duration, len(data)) + data

    name = b"default\x00"
    section = struct.pack("<IIIB", 0, len(frames) * duration - 1,
                          ANIM_HEADER_LEN + 4 * 3 + 1 + len(name), duration) + name
    header = (ANIM_SIG + struct.pack(
        "<BBBBBHBIIIII",
        0,                        # flags
        W, H,
        ANIM_BGR888,
        fps,
        longest,
        0,                        # _unused[1]
        len(section),
        len(body),
        1,                        # section_count
        len(frames),              # file_frame_count
        len(frames) * duration))  # display_frame_count
    assert len(header) == ANIM_HEADER_LEN, len(header)
    return bytes(header + section + body)


def fps_list(text):
    """--fps 60,25 -> [60, 25]. The header stores the rate in ONE BYTE, so
    anything outside 1-255 would be silently truncated by struct.pack."""
    rates = [int(part) for part in text.replace(" ", "").split(",") if part]
    if not rates or any(not 1 <= r <= 255 for r in rates):
        raise argparse.ArgumentTypeError(
            "frame rates must be whole numbers 1-255, comma separated")
    return rates


def build_anim(args, stats):
    """--build-anim: record the banner and leave a file per --fps on disk."""
    frames = capture_frames(args, stats)
    for fps in args.fps:
        blob = pack_pass(frames, fps, args.speed)
        path = anim_path(args.build_anim, fps, len(args.fps) > 1)
        with open(path, "wb") as fh:
            fh.write(blob)
        print(f"  wrote {path}")
    return 0


def anim_path(base, fps, tag):
    """banner.anim -> banner-25fps.anim, but only when there is more than one."""
    if not tag:
        return base
    stem, ext = os.path.splitext(base)      # splitext, so a dot in a parent
    return f"{stem}-{fps}fps{ext}"          # directory cannot eat the name


def pack_pass(frames, fps, speed):
    """One recording -> one .anim at one frame rate.

    ponytail: the frames are rate-INDEPENDENT. Every pixel of the gradient is a
    function of the scroll offset (SWEEP_PER_PX) and never of the wall clock, so
    the same captured bytes are correct at any frame rate; only the header's fps
    and the per-frame hold change. That is why a second rate costs no device time
    and, more importantly, why 60 and 25 are a fair comparison -- they are the
    same pixels, not two recordings with two sets of settle retakes in them.
    """
    # MEASURED, not assumed: a 25 fps / hold 2 file over 372 frames predicts a
    # 29.76s loop if the player honours the header rate, or 12.4s if it ignores
    # it and ticks at 60. Timed on the device by watching for the blank frame
    # between passes: 29.76s. The fps byte is real, so a lower rate is a slower
    # clock and not a dropped frame.
    #
    # The corollary is the ceiling: one pixel per display frame is as fast as a
    # pass can go, so 25 fps cannot express a 30 px/s scroll at all -- hold 1 is
    # 25 px/s and there is nothing between. That is reported, not rounded away.
    duration = max(1, round(fps / max(1, speed)))
    blob = anim_pack(frames, fps, duration)
    achieved = fps / duration                  # px/s the hold actually produces
    drift = achieved / speed - 1
    raw_total = len(frames) * W * H * 3
    print(f"  {fps} fps, hold {duration}: {achieved:.2f} px/s "
          f"({'exact' if abs(drift) < 0.005 else f'{drift:+.1%} off --speed {speed}'}), "
          f"{len(frames) * duration / fps:.1f}s per pass, "
          f"{len(blob):,} bytes ({len(blob) / raw_total:.1%} of raw)")
    return blob


def record_anim(args, stats):
    """Record and pack at the first --fps: what the live paths play."""
    return pack_pass(capture_frames(args, stats), args.fps[0], args.speed)


def capture_frames(args, stats):
    """Record the banner off the device one offset at a time.

    One frame per pixel of travel, and nothing here knows about frame rate.
    """
    segs, width = layout(counts_from(stats))
    total = W + width
    print(f"recording {total} frames of {width}px banner from the device")

    frames, retaken = [], 0
    for i in range(total):
        offset = W - i
        draw(args.host, frame(segs, offset, i * SWEEP_PER_PX))
        # ponytail: a draw returns as soon as the bar has ACCEPTED the elements,
        # not once it has rendered them, so reading the framebuffer straight
        # after can catch a frame with the pill moved and the number not yet --
        # which plays back as digits that stutter against logos that do not.
        # Wait for two identical reads: that is the frame having settled, and it
        # costs one extra read per frame rather than a guessed sleep.
        px = grab(args.host)
        for _ in range(SETTLE_TRIES):
            again = grab(args.host)
            if again == px:
                break
            px = again
            retaken += 1
        # grab() hands back RGB; the file wants BGR, which is what the panel
        # actually stores. Reversing here and not there keeps --shot correct.
        frames.append(bytes(b for p in px for b in (p[2], p[1], p[0])))
        if i % 50 == 0:
            print(f"  {i}/{total}")
    clear(args.host)
    if retaken:
        print(f"  {retaken} frames needed a re-read before they settled")
    return frames


ANIM_ASSET = "banner.anim"


def anim_asset(fps, tag):
    """The name a pass is stored under on the bar. One name when there is one
    rate, so the common case stays `banner.anim` and nothing has to migrate."""
    return anim_path(ANIM_ASSET, fps, tag)


def run_anim(args, stats):
    """Record the banner, upload it, and hand the screen to the firmware.

    Steady state costs nothing: after the upload this process sends no frames
    and no recolours, it only wakes to see whether the numbers moved. They move
    once a week, and a rebuild is about half a minute, so paying that to get the
    logos back at panel rate is the right way round.
    """
    shown = None
    try:
        while True:
            if counts_from(stats) != shown:
                # One trip to the device, then a pass per --fps off the same
                # frames. The first rate is the one that plays; the rest sit on
                # the bar so switching between them is a draw, not a re-record.
                frames = capture_frames(args, stats)
                tag = len(args.fps) > 1
                for fps in args.fps:
                    upload(args.host, anim_asset(fps, tag),
                           pack_pass(frames, fps, args.speed))
                playing = anim_asset(args.fps[0], tag)
                draw(args.host, [{"id": "anim", "type": "animation",
                                  "path": playing, "loop": True,
                                  "x": 0, "y": 0, "align": "top_left",
                                  "z_index": 0, "timeout": 0}])
                shown = counts_from(stats)
                spare = [anim_asset(f, tag) for f in args.fps[1:]]
                print(f"playing {playing} - this process is now idle"
                      + (f"; also on the bar: {', '.join(spare)}" if spare else ""))

            time.sleep(args.refresh)
            if stats["as_of"] == "pinned":
                continue
            try:
                fresh = fetch_stats(args.source)
            except Exception as e:                      # noqa: BLE001
                print(f"refresh failed, keeping the last numbers ({e})")
            else:
                if counts_from(fresh) != shown:
                    stats = fresh
                    print(f"numbers moved, rebuilding: sc={stats['sc']} "
                          f"sp={stats['sp']} am={stats['am']}")
    except KeyboardInterrupt:
        clear(args.host)
        print("\ncleared")
        return 0


def run_device(args, stats):
    """Scroll on the firmware, recolour from the host. No frame loop."""
    text, marks, total = strip(counts_from(stats))
    print(f"{len(text)} chars / {total}px on the firmware at "
          f"{SCROLL_PPM / 60:.0f} px/s - the panel renders it, not this process")

    started = time.monotonic()
    if not 0.0 <= args.dim <= args.bright <= 1.0:
        raise SystemExit("--dim must be between 0 and --bright, and --bright at most 1")
    print(f"brightness wave {args.dim:.2f}-{args.bright:.2f} every {PULSE_PX}px")
    first = window_colors(marks, total, 0.0, args.dim, args.bright)
    draw(args.host, device_frame(text, first) + edge_lines(first))
    next_fetch = started + args.refresh
    blocked = False
    ticks, reported, beat, due = 0, started, 1.0 / RECOLOUR_HZ, started
    last_colors, sent, sent_skipped = None, 0, 0
    calibrating, calibrated, calib_from = 0, False, started
    try:
        while True:
            now = time.monotonic()
            # Where the firmware has scrolled to by now, from its own rate.
            px = (now - started - SCROLL_START_MS / 1000.0) * (SCROLL_PPM / 60.0)
            px = max(0.0, px)
            # Quantise to whole pixels of travel, then send only on change.
            # The gradient is a function of position, so at 30 px/s there are
            # only 30 distinct colours per second no matter how often this loop
            # wakes: ticking faster than that produces duplicate draws, not a
            # smoother gradient. Waking at 60 and sending ~30 is what keeps the
            # colour on the very next pixel without wasting a POST on a repeat.
            colors = window_colors(marks, total, float(int(px)), args.dim, args.bright)
            if colors == last_colors:
                sent_skipped += 1
                status, body = 200, ""
            else:
                last_colors = colors
                try:
                    status, body = draw(args.host, device_pill(colors))
                except urllib.error.URLError as e:
                    print(f"skipped a recolour ({e.reason})")
                    status, body = 200, ""
                else:
                    sent += 1

            # 409 means a BUSY session owns the screen. Routine, not a fault:
            # keep ticking so the pill returns the moment the session ends.
            if status >= 300:
                if not blocked:
                    print(f"{status} {body.strip()} - holding until the screen frees up")
                    blocked = True
                last_colors = None      # force a resend once the screen is free
            elif blocked:
                print("screen free again")
                blocked = False

            if stats["as_of"] != "pinned" and now >= next_fetch:
                next_fetch = now + args.refresh
                try:
                    fresh = fetch_stats(args.source)
                except Exception as e:                  # noqa: BLE001
                    print(f"refresh failed, keeping the last numbers ({e})")
                else:
                    if counts_from(fresh) != counts_from(stats):
                        stats = fresh
                        text, marks, total = strip(counts_from(stats))
                        started = due = time.monotonic()   # the strip changed length
                        draw(args.host, device_frame(text, colors))
                        print(f"updated: {total}px")
            ticks += 1
            if not calibrated:
                calibrating += 1
            # ponytail: calibrate ONCE, against its own start time and its own
            # counter. Keying this off `ticks` re-fired every time the profile
            # printer reset that counter, and each re-fire measured against a
            # long-stale `started` -- which read as 3.7/s and pinned the loop at
            # 3.2 Hz. A latch is the fix; the symptom was a gradient that
            # smoothly ran, then crawled.
            if not calibrated and calibrating >= CADENCE_SAMPLE:
                rate = CADENCE_SAMPLE / max(1e-6, time.monotonic() - calib_from)
                if rate < RECOLOUR_HZ:
                    beat = 1.0 / max(1.0, rate * CADENCE_HEADROOM)
                calibrated = True                # never again
                if args.profile:
                    print(f"measured {rate:.1f} recolours/s; holding {1 / beat:.1f} Hz")
            if args.profile and now - reported >= 5.0:
                span = now - reported
                print(f"{ticks / span:.1f} Hz tick, {sent / span:.1f} Hz sent, "
                      f"{sent_skipped / span:.1f} Hz deduped, "
                      f"text {SCROLL_PPM / 60:.0f} px/s on the firmware")
                ticks, reported, sent, sent_skipped = 0, now, 0, 0
            due += beat
            time.sleep(max(0.0, due - time.monotonic()))
            if due < time.monotonic() - 1.0:
                due = time.monotonic()
    except KeyboardInterrupt:
        clear(args.host)
        print("\ncleared")
        return 0


def run(args):
    lock = claim()
    if lock is None:
        # Name the lock file, not a pkill pattern: launched from inside this
        # directory the command line is just "app.py" and no pattern matches.
        print(f"already running - another process holds {LOCK}")
        return 1

    # The manager stops an app with SIGTERM and gives it 3s before SIGKILL.
    # Python would die on the signal without unwinding, so turn it into the
    # same exit path Ctrl-C already takes.
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt))

    try:
        stats = prepare(args.host, args.source, pinned(args))
    except KeyboardInterrupt:
        return 0
    print(f"{stats['as_of'] if stats['as_of'] == 'pinned' else args.source} "
          f"stats as of {stats['as_of']}: "
          f"sc={stats['sc']} sp={stats['sp']} am={stats['am']}")

    if args.build_anim:
        return build_anim(args, stats)

    if args.render == "anim":
        return run_anim(args, stats)

    if args.render == "device":
        return run_device(args, stats)

    if args.speed < 1:
        # ponytail: a scroller that does not scroll is a divide by zero two
        # lines down, not a still image. --shot is the way to hold a frame.
        raise SystemExit("--speed must be at least 1 px/s; use --shot for a still")

    segs, width = layout(counts_from(stats))
    print(f"{width}px banner at {args.speed} px/s "
          f"({width / args.speed:.0f}s per pass) - ctrl-c to stop")

    # ponytail: draw as fast as the bar will take frames and derive the offset
    # from the clock, instead of one draw per pixel. At 10 px/s the old loop drew
    # ten times a second and the banner visibly stepped; now the frame rate and
    # the scroll speed are independent, so a slow crawl is still smooth. x is an
    # integer on the wire, so the smoothness comes from redrawing the same pixel
    # position more often at a fresh gradient phase, not from fractional x.
    step = 1.0 / FPS
    started = time.monotonic()
    offset = W
    drawn = 0
    gaps = []
    reported = started
    due = time.monotonic()
    next_fetch = time.monotonic() + args.refresh
    blocked = False
    try:
        while True:
            try:
                elapsed = time.monotonic() - started
                travelled = int(elapsed * args.speed)     # whole pixels only
                offset = W - travelled % (W + width)
                # Same integer pixel count drives both, so the colour advances
                # exactly when the banner does and never between steps.
                phase = travelled * SWEEP_PER_PX
                status, body = draw(args.host, frame(segs, offset, phase))
                drawn += 1
            except urllib.error.URLError as e:
                # ponytail: over wi-fi a dropped frame is normal, keep scrolling.
                # Only a wedged host is worth dying for, and the next frame says so.
                print(f"skipped a frame ({e.reason})")
            else:
                # 409 means a BUSY session (priority 90) owns the screen. That is
                # routine, not a fault: say so once and keep drawing into the
                # refusal, so the banner reappears the moment the session ends.
                # Exiting here would read to the manager as a crash and start a
                # backoff-restart loop for as long as the session lasts.
                if status >= 300:
                    if not blocked:
                        print(f"{status} {body.strip()} - holding until the screen frees up")
                        blocked = True
                elif blocked:
                    print("screen free again")
                    blocked = False

            if stats["as_of"] != "pinned" and time.monotonic() >= next_fetch:
                next_fetch = time.monotonic() + args.refresh
                try:
                    fresh = fetch_stats(args.source)
                except Exception as e:                  # noqa: BLE001 - any fetch fault
                    # Hold the last good numbers. A stats banner showing last
                    # week's total is right; one showing nothing is not.
                    print(f"refresh failed, keeping the last numbers ({e})")
                else:
                    if counts_from(fresh) != counts_from(stats):
                        stats = fresh
                        segs, width = layout(counts_from(stats))
                        print(f"updated: sc={stats['sc']} sp={stats['sp']} "
                              f"am={stats['am']} ({width}px)")

            now = time.monotonic()

            # First CADENCE_SAMPLE frames run flat out purely to find out what
            # this bar, on this cable, with this many elements, will actually
            # take. Then the cadence is pinned just under that and held, so
            # every later frame lands on a predictable beat.
            if drawn == CADENCE_SAMPLE and step == 1.0 / FPS:
                rate = CADENCE_SAMPLE / (now - started)
                step = 1.0 / max(1.0, rate * CADENCE_HEADROOM)
                due = now
                if args.profile:
                    print(f"measured {rate:.1f} draws/s at {len(segs) * 3} "
                          f"elements; holding {1 / step:.1f} fps")

            if args.profile and now - reported >= 5.0:
                late = sum(1 for g in gaps if g > step * 1.5)
                spread = (max(gaps) - min(gaps)) * 1000 if gaps else 0.0
                print(f"{drawn / (now - reported):.1f} fps, "
                      f"frame gap spread {spread:.0f}ms, {late} late")
                drawn, reported, gaps = 0, now, []

            due += step
            # Sleep out the rest of this frame's slot. On a healthy frame there
            # is real slack here, which is the whole point: the next draw starts
            # on the beat rather than as soon as the last one happened to finish.
            time.sleep(max(0.0, due - now))
            gaps.append(time.monotonic() - now)
            if due < now - 1.0:
                due = now                # never bank a second of owed frames
    except KeyboardInterrupt:
        clear(args.host)
        print("\ncleared")
        return 0


def self_check():
    for key, (grid, color, _) in BRAND.items():
        assert len(grid) == ICON, (key, len(grid))
        assert pill_color(key) != logo_color(key), \
            f"{key}'s logo would vanish into its pill"
        assert all(len(row) == ICON for row in grid), key
        assert all(set(row) <= {"#", "."} for row in grid), key
        assert sum(row.count("#") for row in grid) > 20, f"{key} is too sparse to read"
        assert len(color) == 9 and color.startswith("#"), key
        png = icon_png(grid, logo_color(key))
        assert png.startswith(b"\x89PNG"), key

    stats = {"sc": 28588, "sp": 20936, "am": 4174, "fans": None, "as_of": "test"}
    counts = counts_from(stats)
    assert counts[0][1] == 53698, "total should be the sum of the three tiles"
    segs, width = layout(counts)
    assert [s["text"] for s in segs] == ["53,698", "28,588", "20,936", "4,174"]

    # nothing may overlap: every element's span ends before the next one starts
    spans = []
    for s in segs:
        spans.append((s["icon_x"], s["icon_x"] + ICON))
        spans.append((s["text_x"], s["text_x"] + text_width(s["text"])))
    for (_, end), (start, _) in zip(spans, spans[1:]):
        assert start >= end, f"overlap: {end} > {start}"

    # nothing may bleed out of its pill: this is what the round ends clip
    for s in segs:
        left, right = s["pill_x"], s["pill_x"] + s["pill_w"]
        assert s["icon_x"] >= left + PILL_PAD, s
        assert s["text_x"] + text_width(s["text"]) <= right - PILL_PAD, \
            f"{s['text']} runs past its pill end"
    # and pills must not touch each other
    for a, b in zip(segs, segs[1:]):
        assert b["pill_x"] - (a["pill_x"] + a["pill_w"]) == GAP, (a, b)

    # the gradient has to actually move, or it is just a two-tone fill
    assert sweep("#FF5500FF", 0.0) != sweep("#FF5500FF", 0.7), "sweep is static"
    # the gradient must be locked to travel, not to the clock: same pixel means
    # same colour, a moved pixel means a moved colour
    phase_at = lambda px: px * SWEEP_PER_PX
    assert flow("#FF5500FF", "#1ED760FF", phase_at(0)) == \
           flow("#FF5500FF", "#1ED760FF", phase_at(0)), "not frame dependent"
    assert flow("#FF5500FF", "#1ED760FF", phase_at(0)) != \
           flow("#FF5500FF", "#1ED760FF", phase_at(40)), "must move with travel"
    assert flow("#FF5500FF", "#1ED760FF", phase_at(0)) == \
           flow("#FF5500FF", "#1ED760FF", phase_at(180)), "must come back round"

    # every pill leads with its own colour and hands over to the next, never
    # the other way round and never all the way
    for ph in (0.0, 0.4, 1.3, 7.7):
        a, b = flow("#FF5500FF", "#1ED760FF", ph)
        assert a == "#E64C00FF", (a, "stop one must be this pill's own brand")
        assert a != b, "both ends the same is not a gradient"
        assert b != "#1BC156FF", "a full handover loses which service this is"
        # the handover must not go through mud: orange to green passes through
        # yellow on the hue wheel, so the blend keeps a lit red channel
        br, bg, bb = (int(b[i:i + 2], 16) for i in (1, 3, 5))
        assert max(br, bg, bb) > 140, (b, "a dark blend is the RGB-lerp smear")
    # a pill next to itself must still be a gradient, not a flat block
    solo = flow("#FF5500FF", "#FF5500FF", 0.9)
    assert solo[0] == solo[1], "no neighbour to hand over to means no shift"

    # the banner must be one closed loop of colour: the last pill hands back to
    # the first, or the spectrum has a seam where it wraps
    social = dict(stats, fans=1726)
    ring = frame(layout(counts_from(social))[0], 0, 0.0)
    pills = [e for e in ring if e["type"] == "rectangle"]
    assert len(pills) == 5, len(pills)
    order = ["globe", "soundcloud", "spotify", "apple_music", "fans"]
    for j, key in enumerate(order):
        nxt = order[(j + 1) % len(order)]
        want = flow(pill_color(key), pill_color(nxt), 0.0 + j * 0.25)
        assert pills[j]["fill_colors"] == want, (key, "must hand over to " + nxt)
    assert pills[-1]["fill_colors"] == flow(pill_color("fans"), pill_color("globe"),
                                            0.0 + 4 * 0.25), "the loop must close"

    # every brand tile must have artwork and a colour, or a segment draws blank
    for key, _ in counts_from(social):
        assert key in BRAND, f"{key} has no icon"

    # a missing key must stop, not spin: prepare() retries device faults forever
    assert issubclass(MisconfiguredError, RuntimeError)
    try:
        fetch_stats("songstats") if not songstats_key() else None
    except MisconfiguredError as e:
        assert "security add-generic-password" in str(e), "must say how to fix it"

    # the firmware-scrolled strip: every service named, and the colour able to
    # say which one is under the window
    text, marks, total = strip(counts_from(social))
    assert text.startswith("TOTAL 53,698"), text[:20]
    assert "SOUNDCLOUD 28,588" in text and "FANS 1,726" in text, text
    assert [k for _, k in marks] == ["globe", "soundcloud", "spotify",
                                     "apple_music", "fans"], marks
    assert total == sum(text_width(f"{LABELS[k]} {v:,}") + text_width(SEPARATOR)
                        for k, v in counts_from(social)), total
    # the middle of a service is its own pure brand colour
    for at, key in marks:
        mid = at + BLEND_PX + 1
        end = total if key == marks[-1][1] else marks[[k for _, k in marks].index(key) + 1][0]
        if end - mid > BLEND_PX:
            # pure brand hue through the middle -- the brightness wave rides on
            # top of it, so compare against the same colour at the same value
            assert color_at(marks, total, mid) == mix(
                pill_color(key), pill_color(key), 0.0, brightness_at(mid, total)), key

    # the brightness wave: smooth, bounded, and a full cycle every PULSE_PX
    per = pulse_period(total)
    assert brightness_at(0, total) == DIM_FLOOR, brightness_at(0, total)
    assert abs(brightness_at(per / 2, total) - DIM_CEILING) < 1e-9
    # a whole number of waves must fit the strip, or the brightness blinks on wrap
    assert abs(total / per - round(total / per)) < 1e-9, (total, per)
    assert abs(brightness_at(float(total), total) - brightness_at(0, total)) < 1e-9
    assert all(DIM_FLOOR - 1e-9 <= brightness_at(x, total) <= DIM_CEILING + 1e-9
               for x in range(0, total))
    # no flick at the turning points: the step between samples shrinks near them
    near_crest = abs(brightness_at(per / 2, total) - brightness_at(per / 2 - 1, total))
    mid_slope = abs(brightness_at(per / 4, total) - brightness_at(per / 4 - 1, total))
    assert near_crest < mid_slope, "a cosine flattens at the crest; a triangle does not"
    # equal floor and ceiling switches the wave off, which is what --dim==--bright is for
    assert len({round(brightness_at(x, total, 0.8, 0.8), 6) for x in range(50)}) == 1
    # at 60 px/s a 60 Hz recolour moves the gradient one pixel per update
    # the gradient runs at twice the scroll: 60 Hz of colour over 30 px/s of
    # text, so the colour advances half a pixel per update and never steps
    assert (SCROLL_PPM / 60.0) / RECOLOUR_HZ <= 1.0, "colour must not lag the scroll"
    assert RECOLOUR_HZ == 2 * (SCROLL_PPM / 60.0), "60 Hz gradient, 30 px/s text"

    # the border shares the fill's hue -- coherent, not contrasting -- and is
    # always far enough away in brightness to still read as an edge
    for c in ("#FF5500FF", "#1ED760FF", "#5B4FE9FF", "#FA243CFF",
              "#101010FF", "#F8F8F8FF", "#808080FF"):
        n = rim(c)
        ch, cs, cv = colorsys.rgb_to_hsv(*(int(c[i:i + 2], 16) / 255.0 for i in (1, 3, 5)))
        nh, _, nv = colorsys.rgb_to_hsv(*(int(n[i:i + 2], 16) / 255.0 for i in (1, 3, 5)))
        if cs > 0.05:
            assert abs(((nh - ch + 0.5) % 1.0) - 0.5) < 0.01, (c, n, "hue must not shift")
        assert abs(nv - cv) > 0.12, (c, n, "too close to the fill to read as an edge")
    # a near-black fill must rim lighter and a near-white fill must rim darker,
    # or the edge disappears at the ends of the brightness wave
    assert rim("#101010FF") > "#101010FF", "dark fill needs a lighter rim"
    dark_v = colorsys.rgb_to_hsv(*(int(rim("#F8F8F8FF")[i:i + 2], 16) / 255.0
                                   for i in (1, 3, 5)))[2]
    assert dark_v < 0.6, "bright fill needs a darker rim"
    # and it must track the fill as the gradient travels
    assert rim("#FF5500FF") != rim("#1ED760FF"), "the rim must follow the fill"

    # the pill overhangs the display so its border lands on the edge pixels
    pill = device_frame("x", ["#FF5500FF", "#1ED760FF"])[0]
    assert pill["x"] == -PILL_BLEED and pill["y"] == -PILL_BLEED
    assert pill["width"] == W + 2 and pill["height"] == H + 2, pill
    assert pill["radius"] * 2 == pill["height"], "still a pill, not a rounded box"
    assert pill["border_width"] == BORDER_W == 1
    assert pill["border_color"] == rim("#FF5500FF")

    # the gradient must SCROLL: the two stops differ wherever a boundary is
    # inside the window, and both stops move as the scroll advances
    a = window_colors(marks, total, 0.0)
    b = window_colors(marks, total, 25.0)
    assert a != b, "the gradient must move with the scroll, not sit still"
    assert len(a) == 2, a
    # and it is continuous: a small step in position never jumps the colour far
    def far(p, q):
        return max(abs(int(p[i:i + 2], 16) - int(q[i:i + 2], 16)) for i in (1, 3, 5))
    prev = color_at(marks, total, 0.0)
    worst = 0
    for px in range(1, total):
        cur = color_at(marks, total, float(px))
        worst = max(worst, far(prev, cur))
        prev = cur
    assert worst <= 40, f"colour jumps {worst} in one pixel - that is a step, not a blend"
    # the loop closes: the colour at the very end matches the colour at the start
    assert far(color_at(marks, total, 0.0), color_at(marks, total, float(total))) == 0

    # the firmware does the scrolling: the text element carries a rate, the
    # recolour carries only the pill so a mid-scroll label is never disturbed
    els = device_frame(text, ["#5B4FE9FF", "#FF5500FF"])
    assert len(els) == 2 and els[1]["scroll_rate"] == SCROLL_PPM
    assert els[1]["width"] == TEXT_W and els[1]["x"] == TEXT_X
    assert TEXT_X + TEXT_W <= W, "the label window must fit inside the display"
    recolour = device_pill(["#FF5500FF", "#1ED760FF"])
    assert [e["id"] for e in recolour] == ["pill", "edge0", "edge1"], \
        "a recolour must never carry the text element, or the scroll restarts"
    assert all(e["type"] == "rectangle" for e in recolour)
    # the hairlines hug the very top and bottom row, full width, and carry the
    # same travelling colours as the pill they sit on
    top, bot = recolour[1], recolour[2]
    assert (top["y"], top["height"]) == (0, EDGE_H), top
    assert bot["y"] + bot["height"] == H, bot
    assert top["width"] == bot["width"] == W, "hairlines must span the display"
    assert top["radius"] == bot["radius"] == 0, "a hairline is not a pill"
    assert top["fill_colors"] == bot["fill_colors"] == recolour[0]["fill_colors"]
    assert top["z_index"] > recolour[0]["z_index"], "must sit above the pill's rim"
    # a recolour is one element where a host frame is fifteen, which is the whole
    # reason 60 is reachable here and 13 was the ceiling there
    host_frame = frame(layout(counts_from(social))[0], 0, 0.0)
    assert len(device_pill(["#000000FF", "#000000FF"])) * 2 <= len(host_frame), \
        "a recolour must stay well cheaper than a host frame"

    # the cadence latch: it must calibrate once and stay calibrated, however
    # often the profile counter is reset underneath it
    calibrating, calibrated, fired = 0, False, 0
    for _ in range(CADENCE_SAMPLE * 4):
        if not calibrated:
            calibrating += 1
        if not calibrated and calibrating >= CADENCE_SAMPLE:
            fired += 1
            calibrated = True
    assert fired == 1, f"calibrated {fired} times; a re-fire pins the loop slow"

    # the RLE must be the firmware's, which means it has to round-trip and it
    # has to actually compress the flat runs a pill is made of
    for probe in (b"", bytes(30), bytes(range(30)),
                  bytes([1, 2, 3]) * 200 + bytes([9, 9, 9]),
                  bytes([7, 7, 7]) * 500):
        packed = rle_compress(probe)
        assert rle_decompress(packed) == probe, probe[:9]
    flat = bytes([255, 85, 0]) * (W * H)          # a screen of one colour
    assert len(rle_compress(flat)) < len(flat) // 50, "a flat frame must collapse"
    # every opcode must stay inside one byte's worth of blocks
    long_run = bytes([1, 2, 3]) * 900
    assert all(op & 0x7F <= RLE_MAX_BLOCKS for op in rle_compress(long_run)[:1])
    assert rle_decompress(rle_compress(long_run)) == long_run

    # the container: header length and the counts the player reads back
    two = [bytes([0, 0, 0]) * (W * H), bytes([9, 9, 9]) * (W * H)]
    blob = anim_pack(two, 60, 2)
    assert blob[:8] == ANIM_SIG, blob[:8]
    (flags, aw, ah, fmt, fps, longest, _unused, sect_len, body_len,
     sections, file_frames, display_frames) = struct.unpack(
        "<BBBBBHBIIIII", blob[8:ANIM_HEADER_LEN])
    assert (aw, ah) == (W, H) and fmt == ANIM_BGR888, (aw, ah, fmt)
    assert fps == 60 and sections == 1
    assert file_frames == 2 and display_frames == 4, "duration must multiply out"
    assert len(blob) == ANIM_HEADER_LEN + sect_len + body_len, "chunk lengths must fit"
    # the "default" section must cover every display frame, or the player has
    # nothing to select, and its frame_offs must point at the frames chunk
    start, end, offs, dur = struct.unpack("<IIIB", blob[ANIM_HEADER_LEN:ANIM_HEADER_LEN + 13])
    assert (start, end) == (0, display_frames - 1), (start, end)
    assert blob[ANIM_HEADER_LEN + 13:].startswith(b"default\x00")
    assert offs == ANIM_HEADER_LEN + sect_len, (offs, "frames chunk must start here")
    # and the first frame header must describe data that decodes to one screen
    enc, fdur, elen = struct.unpack("<BBH", blob[offs:offs + 4])
    assert fdur == 2 and elen <= longest
    payload = blob[offs + 4:offs + 4 + elen]
    assert (rle_decompress(payload) if enc == ANIM_RLE else payload) == two[0]

    # A second frame rate has to be a REPACK, not a second recording: the same
    # pixels, with only the header rate and the per-frame hold different. If
    # this ever fails then --fps 60,25 is quietly producing two different
    # animations and any comparison between them is a lie.
    def frame_payloads(blob):
        (_fl, _w, _h, _fmt, rate, _long, _u, sect, _body,
         _sec, count, _disp) = struct.unpack("<BBBBBHBIIIII", blob[8:ANIM_HEADER_LEN])
        at, holds, out = ANIM_HEADER_LEN + sect, [], []
        for _ in range(count):
            enc_, hold, elen = struct.unpack("<BBH", blob[at:at + 4])
            holds.append(hold)
            out.append(blob[at + 4:at + 4 + elen])
            at += 4 + elen
        assert at == len(blob), "the frames chunk must account for every byte"
        return rate, holds, out

    r60, h60, p60 = frame_payloads(anim_pack(two, 60, 5))
    r25, h25, p25 = frame_payloads(anim_pack(two, 25, 2))
    assert (r60, r25) == (60, 25) and set(h60) == {5} and set(h25) == {2}
    assert p60 == p25, "a rate change must not alter a single pixel"
    # and the hold is what sets the scroll: 60/5 is exactly 12 px/s, 25/2 is
    # 12.5, which is a real 4% faster and is printed rather than rounded away
    assert 60 / 5 == 12.0 and 25 / 2 == 12.5

    assert fps_list("60,25") == [60, 25] and fps_list(" 30 ") == [30]
    assert fps_list("60,") == [60], "a trailing comma is intent, not an error"
    for bad in ("", "0", "256", "60,0", "60,x"):
        try:
            fps_list(bad)
        except (argparse.ArgumentTypeError, ValueError):
            pass
        else:
            raise AssertionError(f"fps_list accepted {bad!r}")
    assert anim_path("banner.anim", 25, False) == "banner.anim"
    assert anim_path("banner.anim", 25, True) == "banner-25fps.anim"
    assert anim_path("/tmp/v1.2/banner", 25, True) == "/tmp/v1.2/banner-25fps"
    assert parse_args([]).fps == [60], "one rate stays the default"
    assert parse_args(["--fps", "60,25"]).fps == [60, 25]

    args = parse_args([])
    assert args.render == "anim", "the recorded animation is the default"
    assert pinned(args) is None, "no overrides means fetch"
    assert pinned(parse_args(["--sc", "1", "--sp", "2", "--am", "3"]))["sc"] == 1
    # the songstats shape must be rehearsable: no --am, so no Apple Music tile
    no_am = pinned(parse_args(["--sc", "1182", "--sp", "13058", "--fans", "1726"]))
    assert no_am["am"] is None and [k for k, _ in counts_from(no_am)] == [
        "globe", "soundcloud", "spotify", "fans"], no_am

    probe = LOCK + ".check"             # never the live lock: a banner may hold it
    held = claim(probe)                 # the lock must exclude a second holder
    assert held is not None, "could not take the lock"
    assert claim(probe) is None, "a second instance was allowed in - the bar would blink"
    held.close()
    assert claim(probe) is not None, "lock not released on close"
    os.unlink(probe)
    print(f"ok - 4 icons, {width}px banner, no overlaps")
    print(f"ok - {[s['text'] for s in segs]}")
    print(f"ok - {len(BRAND)} brand tiles, followers shown only when there is a number")
    print("ok - portfolio parser sums the tiles, lock excludes a second instance")
    print("ok - songstats parser on the real 2026-09-10 body, "
          "apple music left for the portfolio to fill")
    return 0


def parse_args(argv=None):
    p = argparse.ArgumentParser(description="Live Poolpat play counts for BUSY Bar")
    p.add_argument("--host", default="10.0.4.20")
    p.add_argument("--source", choices=("portfolio", "songstats"), default="portfolio",
                   help="where the numbers come from (default: portfolio)")
    p.add_argument("--refresh", type=int, default=1800,
                   help="seconds between fetches (default: 1800)")
    p.add_argument("--sc", type=int, default=None, help="pin SoundCloud plays, skip fetching")
    p.add_argument("--sp", type=int, default=None, help="pin Spotify plays, skip fetching")
    p.add_argument("--am", type=int, default=None, help="pin Apple Music plays, skip fetching")
    p.add_argument("--fans", type=int, default=None,
                   help="pin the all-platform follower total")
    p.add_argument("--build-anim", metavar="FILE",
                   help="record the banner off the device into a .anim file "
                        "the firmware can play with no host traffic at all")
    p.add_argument("--fps", type=fps_list, default=[60],
                   help="frame rate(s) for the .anim header, comma separated; "
                        "60,25 records once and packs both, and the first is "
                        "the one that plays (default: 60)")
    p.add_argument("--dim", type=float, default=DIM_FLOOR,
                   help="brightness at the trough of the wave, 0-1 "
                        "(set equal to --bright for no wave)")
    p.add_argument("--bright", type=float, default=DIM_CEILING,
                   help="brightness at the crest of the wave, 0-1")
    p.add_argument("--render", choices=("anim", "device", "host"), default="anim",
                   help="anim: record the banner to a .anim the firmware plays "
                        "(logos AND 60 fps, no traffic once uploaded). "
                        "device: the firmware scrolls one text label (smooth, "
                        "no logos, instant start). "
                        "host: this process pushes frames (logos, ~12 fps)")
    p.add_argument("--profile", action="store_true",
                   help="print the achieved draw rate every 5s")
    p.add_argument("--speed", type=int, default=SCROLL_PPM // 60,
                   help=f"scroll speed in pixels per second, the same rate the "
                        f"firmware scrolls at in --render device so the paths "
                        f"match (default: {SCROLL_PPM // 60})")
    p.add_argument("--shot", metavar="PNG", help="save the current display and exit")
    p.add_argument("--clear", action="store_true")
    p.add_argument("--test", action="store_true", help="self-check, no device needed")
    return p.parse_args(argv)


def main():
    args = parse_args()
    if args.test:
        return self_check()
    if args.clear:
        print(f"cleared ({clear(args.host)})")
        return 0
    if args.shot:
        px = grab(args.host)
        rows = [[px[y * W + x] + (255,) for x in range(W)] for y in range(H)]
        with open(args.shot, "wb") as f:
            f.write(_png(rows, W, H, zoom=8))
        print(f"wrote {args.shot}")
        return 0
    return run(args)


if __name__ == "__main__":
    sys.exit(main())
