# The code under test and the quickproof patch of OpenSSL's crypto/punycode.c

The verified source is upstream OpenSSL 3.6.5 (commit c8bd5a57108599ac650bbae77fcabe3109dab2e8; `crypto/punycode.c`
is identical in openssl-4.0.3 and in master 2506f1fc323b of 2026-10-12) plus four things, all in `patch/`:

1. the header shim `patch/include/` (`openssl/e_os2.h`, `internal/common.h`, `internal/packet.h`,
   `internal/cryptlib.h`): the declarations `crypto/punycode.c` and the WPACKET functions need, instead of OpenSSL's
   own headers (upstream's `include/crypto/punycode.h` is used as it is);
2. the verbatim WPACKET functions `patch/units/packet_ext.c`: the ten functions of `crypto/packet.c` (and its
   macros `GETBUF`, `DEFAULT_BUF_SIZE`) that `ossl_a2ulabel` reaches, copied byte for byte (`patch/extract.py --check
   TREE` compares them, and the verbatim parts of the shim, with upstream);
3. the shim unit `patch/shim/ossl_shim.c`: the rest of the program in plain C, verified with the code;
4. the patch `patch/osslpatch.py`: two idiom edits that VST needs (meant to change no behaviour) and one minimal
   fix (D1).  Every changed line carries a `quickproof:` comment that gives the
   original.  `crypto/punycode.c` in this repository is upstream's file after this patch.

The evidence that 1-3 and the idiom edits of 4 change no behaviour, and that the fix changes only what it fixes, is
the differential test `patch/difftest.sh` (below, "Evidence").  It is a test, not a proof.

## 1. The header shim

OpenSSL's headers need `./Configure` (`include/openssl/configuration.h`, `crypto.h`, `opensslv.h` ... are generated)
and pull in most of the library.  The shim declares only what the two files touch, with the definitions of a
Linux x86_64 release build of 3.6.5:

- `openssl/e_os2.h`: `ossl_inline` is `inline` (upstream's definition for a C99 compiler);
- `internal/common.h`: `ossl_likely`/`ossl_unlikely`, `ossl_assert`, `HAS_PREFIX`, `HAS_CASE_PREFIX` (for D1) and
  the prototype of `OPENSSL_strncasecmp`, verbatim.  Configuration: NDEBUG (OpenSSL's Configure puts
  `-DNDEBUG` in `CNF_CPPFLAGS` unless `--debug`), so `ossl_assert(x)` is `ossl_likely((x) != 0)`, a test that never
  aborts: `ossl_a2ulabel(in, NULL, n)` returns -1.  (In a debug build it calls `OPENSSL_die`.)  The shim refuses to
  compile without NDEBUG;
- `internal/cryptlib.h`: `OPENSSL_zalloc`/`OPENSSL_free` (verbatim from `include/openssl/crypto.h.in`) and
  `OPENSSL_FILE ""`/`OPENSSL_LINE 0` (upstream's `include/openssl/macros.h` under `OPENSSL_NO_FILENAMES`: the file
  and line only reach the allocator's debugging hooks);
- `internal/packet.h`: `struct buf_mem_st`/`BUF_MEM`, `struct wpacket_sub`, `struct wpacket_st`, the prototypes of
  the WPACKET functions under test and `WPACKET_put_bytes_u8`, verbatim except one change: the bit-field
  `unsigned int endfirst : 1;` is a plain `unsigned int endfirst;` (VST 2.15 has no bit-fields).  The WPACKET
  code only stores 0 or 1 in it and only tests it for zero, so every stored value fits the bit-field and every read
  gives the value stored; fields are accessed by name, so the layout does not matter (build R of the differential
  test uses the real header with the bit-field).

## 2. The verbatim WPACKET functions

`ossl_a2ulabel` writes its output through a static WPACKET: `WPACKET_init_static_len(&pkt, out, outlen, 0)`,
`WPACKET_memcpy`, `WPACKET_put_bytes_u8`, `WPACKET_cleanup`.  `patch/units/packet_ext.c` holds exactly what these
reach, in upstream's order: `WPACKET_allocate_bytes`, `GETBUF`, `WPACKET_reserve_bytes`, `maxmaxsize`,
`wpacket_intern_init_len`, `WPACKET_init_static_len`, `put_value`, `WPACKET_put_bytes__`, `WPACKET_memcpy`,
`WPACKET_get_curr`, `WPACKET_cleanup` (and `DEFAULT_BUF_SIZE`).  The rest of `crypto/packet.c` (growable buffers,
sub-packets with length prefixes, DER and QUIC encodings) is never called by the code under test and is not part of
it.  `WPACKET_reserve_bytes` keeps its growable-buffer branch, which calls `BUF_MEM_grow`; with a static WPACKET
(`pkt->buf == NULL`) the branch is dead.

## 3. The shim unit (`patch/shim/ossl_shim.c`)

| function | what | why |
|---|---|---|
| `CRYPTO_zalloc` | OpenSSL's default allocator (`crypto/mem.c`): `CRYPTO_malloc` (NULL for 0 octets, else `malloc`) then `memset` to 0; no allocation hooks; the failure report (`ossl_report_alloc_err`, an error-stack entry) is left out | the WPACKET's sub-packet record (`wpacket_intern_init_len`) |
| `CRYPTO_free` | `free` (the NULL test changes nothing: `free(NULL)` is a no-op) | `WPACKET_cleanup` |
| `strlen`, `strchr`, `strncmp` | the C library's, in plain C | `ossl_a2ulabel`; `HAS_PREFIX` is `strncmp` |
| `OPENSSL_strncasecmp` | `crypto/o_str.c` with `ossl_tolower` of `crypto/ctype.c` on an ASCII platform | `HAS_CASE_PREFIX` (D1) |
| `BUF_MEM_grow` | a trap (a null store): `crypto/buffer/buffer.c` is not under test, and the call is dead (above) | lets the units link |

Test knob and counters (globals the specs read and write; in the theorems `malloc` may fail at every call anyway):
`ossl_shim_fail_next` (nonzero: the next `CRYPTO_zalloc` fails; native `malloc` never fails, so this is how native
and interpreter runs reach the allocation-failure path), `ossl_shim_zalloc_failed` (set when `CRYPTO_zalloc` returns
NULL: the specs then expect -1), `ossl_shim_live` (blocks allocated and not freed: the specs check that
`ossl_a2ulabel` releases its record).  `memcpy` and `memset` are the framework's `quickproof/libc/libc.c`.

## 4. The patch (`patch/osslpatch.py`)

| # | function | change | why | evidence |
|---|---|---|---|---|
| I1 | `ossl_a2ulabel` | the two `goto end` (a label that does not decode; a code point above 0x10FFFF) become `break` out of the label loop: the first directly, the second out of the loop over the label's code points and then, by an added `if (result == -1) break;`, out of the label loop; the final `WPACKET_put_bytes_u8(&pkt, '\0')` is guarded by `result != -1`; the label `end:` goes | VST has no rule for `goto` | differential test (O = I) |
| I2 | `ossl_punycode_decode` | `memmove(pDecoded + i + 1, pDecoded + i, (written_out - i) * sizeof(*pDecoded))` becomes a loop of typed element copies, backwards: `for (gp_j = written_out; gp_j > i; gp_j--) pDecoded[gp_j] = pDecoded[gp_j - 1];` | the framework's `memmove` is specified on octets; on an `unsigned int` array VST would need a lemma relating octet copies to the integer cells | differential test (O = I) |
| D1 | `ossl_a2ulabel` | A fix: `if (!HAS_PREFIX(inptr, "xn--"))` becomes `if (!HAS_CASE_PREFIX(inptr, "xn--"))` (upstream's own macro: `OPENSSL_strncasecmp`): a label is decoded when it starts with the ACE prefix in any case | RFC 5890 2.3.1: XN-labels "begin with the prefix "xn--" (case independent)"; upstream copies "XN--..." labels undecoded, and an excluded email name constraint written "XN--..." does not exclude the matching SmtpUTF8Mailbox | differential test (the changed results, characterised: P on a string = O on the string with its ACE prefixes in lowercase) |

### Why the idiom edits preserve behaviour

- **I1.**  After `result = -1;` the original jumps to `end:`, which only runs `WPACKET_cleanup(&pkt)` and returns.
  The first `break` leaves the `while (1)` loop directly (it is not inside an inner loop); the second leaves the
  `for` loop over the code points, and the added test (true exactly then: `result` is set to -1 only on these two
  paths, and is 1 or 0 otherwise) leaves the `while (1)` loop.  After the loop, `result != -1` skips the NUL that the
  original skipped by jumping over it; on the normal exit (`tmpptr == NULL`) `result` is 1 or 0, the test is true
  and the NUL is written as before.  Nothing else runs on either path.
- **I2.**  `0 <= i <= written_out < max_out` at this point, so both ranges are inside the array.  `memmove` moves
  elements `i .. written_out - 1` up by one element as if through a temporary; copying them one by one from the top
  down reads each source element before it is overwritten, so it stores the same values in the same places.  The
  copied elements were all written before (they are the output so far), so no uninitialised value is involved.

## Evidence

**Verbatim copies.**  `patch/extract.py --check TREE` (TREE: an OpenSSL checkout at c8bd5a571085):
every function and macro of `packet_ext.c`, and the verbatim parts of the shim headers, are byte-identical to
upstream (the one changed line, `endfirst`, is compared in its widened form).

**Differential test.**  `patch/difftest.sh [N] [SEEDS]` builds the code four ways, each with
`patch/difftest_drv.c` and the shim unit.  It runs inside a QuickProof workspace that holds this project as
`projects/openssl-punycode` (see its first comment).  The builds:
- R: unmodified `crypto/punycode.c` and the whole `crypto/packet.c`, against OpenSSL's real headers (a checkout at
  c8bd5a571085, `./Configure linux-x86_64 no-asm no-shared`, `make build_generated`), with the C library's string
  functions (the shim's are renamed away) and `patch/stubs_real.c` (trapping QUIC encoders that `packet.c` refers
  to);
- O: unmodified `crypto/punycode.c` and `packet_ext.c` against the shim;
- I: the idiom edits only (`osslpatch.py --no-fix`), against the shim;
- P: the whole patch, against the shim (the verified code).

The driver draws N calls per seed from the project's generators (`env/gen.h`): half `ossl_punycode_decode` on
Punycode-ish strings (valid encodings, mutated ones, overflow boundaries, basic and non-basic octets, known vectors,
random octets) with output bounds at the boundaries; half `ossl_a2ulabel` on host names (labels with "xn--",
"XN--", "Xn--", "xn-" prefixes, LDH labels, high octets, empty labels, a NUL inside) with output sizes at the
boundaries, `out == NULL` and a failing allocation now and then.  It prints the result and an FNV-1a hash of the
whole output (array or buffer, pre-filled with a pattern) of every call, and the shim's counters.  Checks: R = O,
O = I (byte-identical outputs), O and P agree on every call except the `ossl_a2ulabel` calls on a string with an ACE
prefix not in lowercase, and on each of those P gives exactly what O gives on the same string with its ACE prefixes
in lowercase (`patch/difftest_cmp.py`); the same under gcc -O1 with ASan/UBSan, and P compiled by CompCert's ccomp.

Result: see `DIFFTEST` below.

CompCert's interpreter runs every spec on the patched code without a stop ([CHECK.md](../CHECK.md)).

I1 and I2 fix no bug: they are tool limitations (VST's missing `goto` rule; octet-level `memmove` on a typed
array).

## DIFFTEST

`patch/difftest.sh 100000 "1 2 3"`, 2026-10-13 (gcc 13, CompCert 3.15 ccomp; about 26 minutes):

```
seed 1: 100000 calls: decode ok/fail 17958/32297, a2ulabel 1/0/-1 12136/10676/26933 (5918 with an ACE prefix not in lowercase), leaked 0
  R-O2 = O-O2
  O-O2 = I-O2
  O-O2 = O-san
  P-O2 = P-san
  P-O2 = P-ccomp
  P-O2 ~ O-O2: identical except 5918 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2060 of them changed by D1)
  P-san ~ O-san: identical except 5918 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2060 of them changed by D1)
seed 2: 100000 calls: decode ok/fail 17852/32262, a2ulabel 1/0/-1 12135/10549/27202 (5867 with an ACE prefix not in lowercase), leaked 0
  R-O2 = O-O2
  O-O2 = I-O2
  O-O2 = O-san
  P-O2 = P-san
  P-O2 = P-ccomp
  P-O2 ~ O-O2: identical except 5867 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2070 of them changed by D1)
  P-san ~ O-san: identical except 5867 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2070 of them changed by D1)
seed 3: 100000 calls: decode ok/fail 17974/31978, a2ulabel 1/0/-1 12120/10684/27244 (5947 with an ACE prefix not in lowercase), leaked 0
  R-O2 = O-O2
  O-O2 = I-O2
  O-O2 = O-san
  P-O2 = P-san
  P-O2 = P-ccomp
  P-O2 ~ O-O2: identical except 5947 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2050 of them changed by D1)
  P-san ~ O-san: identical except 5947 calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string (2050 of them changed by D1)
patch/difftest.sh: the header shim, the extraction and the idiom edits change nothing; D1 changes only what it fixes (100000 calls per seed and build)
```

Upstream's own tests with D1 applied to a 3.6.5 build from source (`./Configure linux-x86_64 no-asm no-shared`):
`test/punycode_test` passes (5/5: the RFC 3492 vectors, test_dotted_overflow, test_a2ulabel, test_puny_overrun,
test_a2ulabel_bad_decode), and so do the verifications of `test/recipes/25-test_eai_data.t`.
