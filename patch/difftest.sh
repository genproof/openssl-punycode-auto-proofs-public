#!/usr/bin/env bash
# patch/difftest.sh [N] [SEEDS]: the differential test of the patch and of the header shim (PATCH.md).
#
# Four builds of the code under test, each linked with patch/difftest_drv.c and patch/shim/ossl_shim.c:
#   R  unmodified upstream crypto/punycode.c and crypto/packet.c (the whole file), compiled against OpenSSL's REAL
#      headers (a checkout at COMMIT, `./Configure linux-x86_64 no-asm`, `make build_generated`), with the C
#      library's strlen/strchr/strncmp (the shim's are renamed away) and the WPACKET of include/internal/packet.h
#      (endfirst a 1-bit bit-field);
#   O  unmodified upstream crypto/punycode.c and patch/units/packet_ext.c (the verbatim WPACKET functions),
#      compiled against the header shim patch/include/, with the shim's string functions;
#   I  crypto/punycode.c with the idiom edits only (patch/osslpatch.py --no-fix) and packet_ext.c, with the shim;
#   P  the whole patch (idiom edits and the fix D1) and packet_ext.c, with the shim: the verified code;
# the driver prints every result and an FNV-1a hash of the whole output (array or buffer) of every call on a
# seeded stream of generated inputs (N calls per seed).  Checks, each under gcc -O2:
#   R = O   the header shim, the extraction and the shim's string functions change nothing;
#   O = I   the idiom edits (I1 the gotos, I2 the memmove) change nothing;
#   P ~ O   the fix D1 changes exactly what it fixes: on every ossl_a2ulabel call on a string with an ACE prefix not
#           in lowercase ("A 1" lines) P gives what O gives on the same string with those prefixes in lowercase
#           (the "N" lines), and every other line is identical (patch/difftest_cmp.py);
# and under gcc -O1 with ASan/UBSan (O-san = O-O2, P-san = P-O2, P-san ~ O-san), and P compiled by CompCert's ccomp
# (P-ccomp = P-O2; when ccomp is on PATH, e.g. after `eval $(opam env --switch=liblzma)`).
# Run in a QuickProof workspace that holds this project as projects/openssl-punycode (QP_WORKSPACE, default: the
# workspace this file is in), with QuickProof's tools/qp (QP, default: qp on PATH) and a git clone of OpenSSL that has
# COMMIT (OPENSSL_GIT, default: the clone in qp's cache).  Builds with -j3 at most.
set -euo pipefail
N=${1:-100000}; SEEDS=${2:-"1 2 3"}
HERE=$(cd "$(dirname "$0")" && pwd)
export QP_WORKSPACE=${QP_WORKSPACE:-$(cd "$HERE/../../.." && pwd)}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
QP=${QP:-qp}
"$QP" tree openssl-punycode --orig --out "$T/O" > /dev/null
"$QP" tree openssl-punycode --out "$T/P" > /dev/null
"$QP" tree openssl-punycode --orig --out "$T/I" > /dev/null
(cd "$T/I" && python3 patch/osslpatch.py --no-fix)
COMMIT=${COMMIT:-c8bd5a57108599ac650bbae77fcabe3109dab2e8}   # openssl-3.6.5
REPO=${OPENSSL_GIT:-${QP_CACHE:-$HOME/.cache/quickproof}/upstream/openssl-6232dd81}
git -C "$REPO" worktree add -q --detach "$T/ossl" "$COMMIT"
trap 'git -C "$REPO" worktree remove --force "$T/ossl" 2>/dev/null; rm -rf "$T"' EXIT
(cd "$T/ossl" && ./Configure linux-x86_64 no-asm no-shared > "$T/configure.log" 2>&1 \
   && make -j3 build_generated > "$T/generated.log" 2>&1) || { echo "OpenSSL configure failed"; tail "$T/configure.log" "$T/generated.log"; exit 1; }
SAN="-fsanitize=address,undefined -fno-sanitize-recover=all"
mkdir -p "$T/bin"
ok=1

build() {   # build NAME VARIANT CC FLAGS... : the code of VARIANT (R, O or P) + the driver + the shim
  local name=$1 v=$2 cc=$3; shift 3
  local o="$T/b-$name"; mkdir -p "$o"
  local shim="$T/P/patch/shim/ossl_shim.c" drv="$T/P/patch/difftest_drv.c"
  if [ "$v" = R ]; then
    local real="-DNDEBUG -DOPENSSL_BUILDING_OPENSSL -I$T/ossl/include -I$T/ossl -I$T/ossl/crypto -I$T/ossl/providers/common/include"
    "$cc" "$@" $real -c "$T/ossl/crypto/punycode.c" -o "$o/punycode.o"
    "$cc" "$@" $real -ffunction-sections -c "$T/ossl/crypto/packet.c" -o "$o/packet.o"
    "$cc" "$@" -DNDEBUG -I"$T/P/patch/include" -c "$shim" -o "$o/shim.o"
    objcopy --redefine-sym strlen=shim_strlen --redefine-sym strchr=shim_strchr --redefine-sym strncmp=shim_strncmp "$o/shim.o"
    "$cc" "$@" -c "$T/P/patch/stubs_real.c" -o "$o/stubs.o"
    local extra="$o/stubs.o -Wl,--gc-sections"
  else
    local d="$T/$v"
    "$cc" "$@" -DNDEBUG -I"$d/patch/include" -I"$d/include" -c "$d/crypto/punycode.c" -o "$o/punycode.o"
    "$cc" "$@" -DNDEBUG -I"$d/patch/include" -I"$d/include" -c "$d/patch/units/packet_ext.c" -o "$o/packet.o"
    "$cc" "$@" -DNDEBUG -I"$d/patch/include" -c "$shim" -o "$o/shim.o"
    local extra=""
  fi
  "$cc" "$@" -I"$T/P" -I"$T/P/harness" -c "$drv" -o "$o/drv.o"
  "$cc" "$@" "$o/drv.o" "$o/punycode.o" "$o/packet.o" "$o/shim.o" $extra -o "$T/bin/$name"
}

build R-O2 R gcc -O2 -w
build O-O2 O gcc -O2 -w
build I-O2 I gcc -O2 -w
build P-O2 P gcc -O2 -w
build O-san O gcc -O1 -g -w $SAN
build P-san P gcc -O1 -g -w $SAN
CC_LIST="O-san P-san"
if command -v ccomp > /dev/null; then build P-ccomp P ccomp -w && CC_LIST="$CC_LIST P-ccomp"; else echo "ccomp: not on PATH, skipped"; fi

for s in $SEEDS; do
  for b in R-O2 O-O2 I-O2 P-O2 $CC_LIST; do
    ASAN_OPTIONS=detect_leaks=0 "$T/bin/$b" "$s" "$N" > "$T/out-$b-$s" 2> "$T/sum-$b-$s" || { echo "$b seed $s: FAILED"; cat "$T/sum-$b-$s" | tail -3; ok=0; }
  done
  echo "seed $s: $(cat "$T/sum-P-O2-$s")"
  for pair in R-O2:O-O2 O-O2:I-O2 O-O2:O-san P-O2:P-san $(for c in $CC_LIST; do [ $c = P-ccomp ] && echo P-O2:$c; done); do
    a=${pair%%:*}; b=${pair##*:}
    if cmp -s "$T/out-$a-$s" "$T/out-$b-$s"; then echo "  $a = $b"; else echo "  $a != $b: DIFFERENT"; diff "$T/out-$a-$s" "$T/out-$b-$s" | head -4; ok=0; fi
  done
  for pair in O-O2:P-O2 O-san:P-san; do
    a=${pair%%:*}; b=${pair##*:}
    if res=$(python3 "$HERE/difftest_cmp.py" "$T/out-$a-$s" "$T/out-$b-$s"); then echo "  $b ~ $a: $res"; else echo "  $b ~ $a: UNEXPECTED: $res"; ok=0; fi
  done
done
[ $ok = 1 ] && echo "patch/difftest.sh: the header shim, the extraction and the idiom edits change nothing; D1 changes only what it fixes ($N calls per seed and build)" \
  || { echo "patch/difftest.sh: DIFFERENCE"; exit 1; }
