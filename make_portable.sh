#!/bin/bash
# Build a self-contained runtime bundle for hosts without PyGObject.
#
# Run this on an INTERNET-CONNECTED dev machine (macOS or Linux); the
# resulting tar is what gets carried into the closed network:
#
#   ./make_portable.sh [output-dir]     # -> flateyes-portable-<ver>-<date>.tar.gz
#
# The bundle holds python + PyGObject + GTK3 (conda-forge, linux-64,
# glibc <= 2.17) plus a launcher that builds the machine-local caches on
# first run.  Target requirement: x86_64 Linux, glibc 2.17+ (RHEL7+).
# Verified end-to-end on a closed-network host on 2026-07-22.
set -euo pipefail

REPO=$(cd "$(dirname "$0")" && pwd)
OUT_DIR=${1:-$REPO}
WORK=${FLATEYES_PORTABLE_WORK:-${TMPDIR:-/tmp}/flateyes-portable-build}
PY_SPEC=python=3.11
GLIBC_CEILING=17          # max minor of GLIBC_2.x any bundled ELF may need
VERSION=$(sed -n 's/^VERSION = "\(.*\)"/\1/p' "$REPO/flateyes.py")
STAMP=$(date +%Y%m%d)
NAME="flateyes-portable-${VERSION}-${STAMP}"

echo "== workdir: $WORK"
rm -rf "$WORK"
mkdir -p "$WORK"
cd "$WORK"

# -- 1. micromamba (static, for the BUILD machine's platform) -----------
case "$(uname -s)-$(uname -m)" in
    Darwin-arm64)  MM_PLAT=osx-arm64 ;;
    Darwin-x86_64) MM_PLAT=osx-64 ;;
    Linux-x86_64)  MM_PLAT=linux-64 ;;
    Linux-aarch64) MM_PLAT=linux-aarch64 ;;
    *) echo "unsupported build machine: $(uname -s)-$(uname -m)"; exit 1 ;;
esac
curl -fsSL -o micromamba \
    "https://github.com/mamba-org/micromamba-releases/releases/latest/download/micromamba-${MM_PLAT}"
chmod +x micromamba

# -- 2. resolve + extract the linux-64 runtime --------------------------
# CONDA_OVERRIDE_GLIBC makes the solver refuse builds newer than the
# RHEL7 baseline.  post-link scripts fail cross-platform (they are the
# target's binaries); the launcher runs their work on first start.
CONDA_OVERRIDE_GLIBC=2.${GLIBC_CEILING} ./micromamba create -y \
    -r "$WORK/mmroot" -p "$WORK/runtime" --platform linux-64 \
    -c conda-forge "$PY_SPEC" pygobject gtk3 \
    || true   # post-link failures still exit nonzero on some versions
[ -x "$WORK/runtime/bin/python3.11" ] || {
    echo "runtime extraction failed"; exit 1; }

# -- 3. slim: build-time payloads never touched at runtime --------------
cd "$WORK/runtime"
rm -rf include share/gir-1.0 share/locale share/doc share/man \
       share/gtk-doc share/cups share/terminfo share/zoneinfo \
       share/aclocal share/bash-completion conda-meta compiler_compat \
       x86_64-conda-linux-gnu sbin lib/pkgconfig lib/cmake \
       lib/python3.11/test lib/python3.11/idlelib \
       lib/python3.11/ensurepip lib/python3.11/lib2to3 \
       lib/python3.11/turtledemo lib/python3.11/tkinter
rm -rf lib/python3.11/site-packages/pip \
       lib/python3.11/site-packages/setuptools \
       lib/python3.11/site-packages/wheel \
       lib/python3.11/site-packages/packaging \
       lib/python3.11/site-packages/*.dist-info \
       lib/python3.11/site-packages/*.egg-info
find . -name "__pycache__" -type d -prune -exec rm -rf {} +
find lib -name "*.a" -delete
cd bin
for f in *; do
    case "$f" in
        python3|python3.11|glib-compile-schemas|gdk-pixbuf-query-loaders|gtk-update-icon-cache) ;;
        *) rm -rf "$f" ;;
    esac
done
cd "$WORK"

# -- 4. verify: pure x86_64, glibc ceiling, key files -------------------
python3 - "$WORK/runtime" "$GLIBC_CEILING" <<'PY'
import os, re, struct, sys
root, ceiling = sys.argv[1], int(sys.argv[2])
pat = re.compile(rb"GLIBC_2\.(\d+)")
bad = []
elves = 0
for dp, _, names in os.walk(root):
    for n in names:
        p = os.path.join(dp, n)
        try:
            with open(p, "rb") as f:
                head = f.read(20)
                if head[:4] != b"\x7fELF":
                    continue
                elves += 1
                if struct.unpack("<H", head[18:20])[0] != 0x3E:
                    bad.append(("arch", p))
                    continue
                f.seek(0)
                vs = [int(m.group(1)) for m in pat.finditer(f.read())]
        except OSError:
            continue
        if vs and max(vs) > ceiling:
            bad.append(("GLIBC_2.%d" % max(vs), p))
for why, p in bad:
    print("FAIL", why, os.path.relpath(p, root))
must = ["bin/python3.11", "lib/libgtk-3.so.0",
        "lib/girepository-1.0/Gtk-3.0.typelib",
        "lib/python3.11/site-packages/gi/__init__.py",
        "share/glib-2.0/schemas", "fonts"]
missing = [m for m in must if not os.path.exists(os.path.join(root, m))]
for m in missing:
    print("MISSING", m)
if bad or missing:
    sys.exit(1)
print("verified: %d ELF files, all x86_64, glibc <= 2.%d" % (elves, ceiling))
PY

# -- 5. assemble the bundle ---------------------------------------------
B="$WORK/flateyes-portable"
rm -rf "$B"
mkdir -p "$B"
mv "$WORK/runtime" "$B/runtime"
cp "$REPO/flateyes.py" "$B/flateyes.py"

cat > "$B/flateyes" <<'EOF'
#!/bin/sh
# flateyes portable launcher: self-contained python + GTK3 runtime.
# Nothing is installed; the bundle runs from wherever it was untarred.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
RT="$HERE/runtime"
CACHE="${XDG_CACHE_HOME:-$HOME/.cache}/flateyes-rt"
mkdir -p "$CACHE/schemas" 2>/dev/null || CACHE="${TMPDIR:-/tmp}/flateyes-rt.$(id -u)"
mkdir -p "$CACHE/schemas" 2>/dev/null

# First run (or after the bundle moved/updated): build the machine-local
# caches that a normal package install would have produced.
if [ ! -f "$CACHE/schemas/gschemas.compiled" ] \
   || [ "$RT/share/glib-2.0/schemas" -nt "$CACHE/schemas/gschemas.compiled" ]; then
    "$RT/bin/glib-compile-schemas" --targetdir="$CACHE/schemas" \
        "$RT/share/glib-2.0/schemas" 2>/dev/null || true
fi
if [ ! -f "$CACHE/pixbuf-loaders.cache" ] \
   || [ "$RT/lib/gdk-pixbuf-2.0/2.10.0/loaders" -nt "$CACHE/pixbuf-loaders.cache" ]; then
    GDK_PIXBUF_MODULEDIR="$RT/lib/gdk-pixbuf-2.0/2.10.0/loaders" \
        "$RT/bin/gdk-pixbuf-query-loaders" \
        > "$CACHE/pixbuf-loaders.cache" 2>/dev/null || true
fi

GDK_PIXBUF_MODULE_FILE="$CACHE/pixbuf-loaders.cache"
GI_TYPELIB_PATH="$RT/lib/girepository-1.0"
GSETTINGS_SCHEMA_DIR="$CACHE/schemas"
XDG_DATA_DIRS="$RT/share:/usr/local/share:/usr/share"
FONTCONFIG_FILE="$HERE/fonts.conf"
LD_LIBRARY_PATH="$RT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
GDK_BACKEND=x11
PYTHONHOME="$RT"
PYTHONNOUSERSITE=1
export GDK_PIXBUF_MODULE_FILE GI_TYPELIB_PATH GSETTINGS_SCHEMA_DIR \
    XDG_DATA_DIRS FONTCONFIG_FILE LD_LIBRARY_PATH GDK_BACKEND \
    PYTHONHOME PYTHONNOUSERSITE
exec "$RT/bin/python3.11" "$HERE/flateyes.py" "$@"
EOF

cat > "$B/selfcheck" <<'EOF'
#!/bin/sh
# Verifies the portable stack on THIS host without opening a window.
# Run it first on the target; every line should end with OK.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
RT="$HERE/runtime"
echo "host glibc:   $(ldd --version 2>/dev/null | head -1)"
echo "arch:         $(uname -m)   (needs x86_64, glibc >= 2.17)"
GI_TYPELIB_PATH="$RT/lib/girepository-1.0" \
LD_LIBRARY_PATH="$RT/lib" PYTHONHOME="$RT" PYTHONNOUSERSITE=1 \
"$RT/bin/python3.11" - <<'PY'
import sys
print("python:       %s OK" % sys.version.split()[0])
import gi
gi.require_version("Gtk", "3.0")
from gi.repository import Gtk, Gdk, GdkPixbuf, GLib
print("pygobject:    OK")
print("GTK typelib:  %d.%d OK" % (Gtk.MAJOR_VERSION, Gtk.MINOR_VERSION))
fmts = sum(1 for f in GdkPixbuf.Pixbuf.get_formats())
print("pixbuf fmts:  builtin(png/jpeg) + %d module(s) pending cache OK" % fmts)
PY
echo "display:      DISPLAY=${DISPLAY:-<unset>}  (open test: ./flateyes <image>)"
EOF

cat > "$B/fonts.conf" <<'EOF'
<?xml version="1.0"?>
<!DOCTYPE fontconfig SYSTEM "fonts.dtd">
<!-- flateyes portable: bundled fonts first, then every common system
     font location, so Korean glyphs come from the host when present. -->
<fontconfig>
  <dir prefix="relative">runtime/fonts</dir>
  <dir>/usr/share/fonts</dir>
  <dir>/usr/share/X11/fonts</dir>
  <dir>/usr/local/share/fonts</dir>
  <dir prefix="xdg">fonts</dir>
  <dir>~/.fonts</dir>
  <cachedir>~/.cache/flateyes-rt/fontcache</cachedir>
  <match target="pattern">
    <test qual="any" name="family"><string>sans-serif</string></test>
    <edit name="family" mode="prepend" binding="weak"><string>DejaVu Sans</string></edit>
  </match>
</fontconfig>
EOF

cat > "$B/README-PORTABLE.txt" <<EOF
flateyes 포터블 번들 (flateyes ${VERSION}, ${STAMP} 빌드)
====================

PyGObject(python3-gobject)가 없는 호스트에서 flateyes를 실행하기 위한
자체 포함 런타임입니다. Python + PyGObject + GTK3와 모든 의존
라이브러리가 runtime/ 안에 들어 있으며, 시스템에는 아무것도 설치하거나
변경하지 않습니다. 시스템에서 가져다 쓰는 것은 X 디스플레이와 (있다면)
한글 시스템 폰트뿐입니다.

요구 사항
---------
- x86_64 리눅스, glibc 2.17 이상 (RHEL/CentOS 7 이상. RHEL6은 불가)
- X 디스플레이 (Exceed TurboX / XQuartz 원격 접속 포함)

설치
----
아무 위치에나 풀면 됩니다:

    tar xzf flateyes-portable-*.tar.gz -C /opt      # 위치는 자유

확인 (창 없이 스택 검증):

    /opt/flateyes-portable/selfcheck

실행
----
    /opt/flateyes-portable/flateyes /path/to/image.png

기존 flateyes.py와 동일하게 동작합니다 (단일 인스턴스 포워딩, 폴더
브라우징, 주석, 스택 등 모든 기능·옵션 동일). 편의상 심볼릭 링크를
걸어 두면 됩니다:

    ln -s /opt/flateyes-portable/flateyes /usr/local/bin/flateyes

첫 실행 시 ~/.cache/flateyes-rt/ 아래에 이 호스트용 캐시(GSettings
스키마, 이미지 로더 목록, 폰트 캐시)를 자동 생성합니다. 홈이 쓰기
불가면 /tmp로 대체됩니다.

flateyes.py 업데이트
--------------------
새 버전의 flateyes.py를 이 폴더의 flateyes.py에 덮어쓰기만 하면
됩니다. 런타임은 그대로 재사용됩니다.

문제 해결
---------
- "cannot execute binary file" / "GLIBC_x.xx not found":
  호스트가 x86_64 glibc 2.17 미만 → 이 번들 사용 불가 (selfcheck로 확인)
- 창이 안 뜨고 코드 3으로 종료: DISPLAY 미설정/접속 불가 (기존과 동일)
- 이미지가 모두 "broken"으로 뜸: ~/.cache/flateyes-rt 삭제 후 재실행
  (로더 캐시 재생성)
EOF

chmod +x "$B/flateyes" "$B/selfcheck"
sh -n "$B/flateyes"
sh -n "$B/selfcheck"

# -- 6. pack -------------------------------------------------------------
cd "$WORK"
COPYFILE_DISABLE=1 tar -czf "$NAME.tar.gz" flateyes-portable
if tar -tzf "$NAME.tar.gz" | grep -q "\._"; then
    echo "AppleDouble entries leaked into the tar"; exit 1
fi
mkdir -p "$OUT_DIR"
mv "$NAME.tar.gz" "$OUT_DIR/"
cd "$OUT_DIR"
if command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$NAME.tar.gz"
else
    sha256sum "$NAME.tar.gz"
fi
ls -lh "$NAME.tar.gz"
echo "done: $OUT_DIR/$NAME.tar.gz"
