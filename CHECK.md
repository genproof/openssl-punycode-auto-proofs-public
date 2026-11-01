# The checks before the proof

Every spec was run before the proof of the short specs was written, with `qp check` of QuickProof v0.1.0-beta.1 on
the code of this repository (OpenSSL 3.6.5 + `patch/`), on 2026-10-23. Native runs and the interpreter are testing:
they can show a spec false, never prove it.

## Native runs (AddressSanitizer and UndefinedBehaviorSanitizer, 500 runs per spec)

Each spec ran on the patched code (the code under test) and on the unmodified code. The values of each run are
drawn by `env/<name>.c`: Punycode strings that are valid, nearly valid or not, host names with ACE prefixes in every
case, capacities and output sizes at the boundaries (exact fit, one less, one more), OpenSSL's allocation failing
now and then, code points at the bound of `rt_roundtrip` and its counterexamples.

| specs | patched | unmodified |
|---|---|---|
| the other 15 short specs | ok | ok |
| `rfc_ace_any_case` | ok | fails (`XN--` labels are copied, not decoded; D1 fixes it) |
| `x_a2ulabel` | ok | fails (the same bug) |
| `x_roundtrip` | ok | ok |
| `x_decode` | ok (20 runs stopped by the 10 s time limit; seed 16 passes in 34 s) | the same |

After these runs, `copy_of` in `harness/laws_common.h` was changed to give NULL for a NULL source. A run where an
earlier malloc failed read through NULL; this is possible only in the theorems, where malloc may fail, and was found
at the start of the proof. The 8 specs that use `copy_of` passed 300 more native runs and 5 interpreter runs each.
`rt_roundtrip` (its `adapt` renamed `rfc_adapt`) passed 500 more native runs and 10 interpreter runs.

Coverage (gcov of the specs, 300 runs): every check of every short spec is reached. The branches that need a
successful decoding or conversion are reached in a third to a half of the runs (for example `rfc_unique`'s
comparison of two inputs that decode alike in 82 of 300). The allocation-failure branches are reached through the
env's use of the shim's failure knob.

## CompCert's interpreter (20 runs per spec)

This is the semantics of the theorems: a stop is undefined behaviour. No spec stopped (`x_decode`: 2 runs timed
out).

## Mutants (80 mutants of the code under test, 300 runs per spec and mutant)

`qp check` found 338 mutation sites (comparisons, logical operators, off-by-one constants) in `crypto/punycode.c`,
`patch/units/packet_ext.c` and `patch/shim/ossl_shim.c`. It shuffles them in a fixed random order and takes the first
80 mutants whose compiled code differs from the original. Together the specs kill 57 of the 80. The short specs alone
kill every one of the 57, and so do the `x_` specs alone. The 23 others:

- 10 are equivalent to the original: `seed[6]` to 5 or 7 (two; `codepoint2utf8` writes at most `out[4]`),
  `out[1] = 0` (two; the NUL after a one-byte code point is never read), the threshold test `k >= bias + tmax` with
  `>` (at equality `k - bias` is `tmax`), `initial_bias` 72 to 73 (the first thresholds are the same), `return 1` to
  2 in `wpacket_intern_init_len` and `WPACKET_reserve_bytes` (two; callers test for nonzero), `digit_decoded`'s
  `return -1` to -2 (callers test for a negative value; the mutant that returns 0 is killed by
  `rj_decode_invalid`), and `OPENSSL_strncasecmp`'s NUL test (never reached with the prefix `xn--`);
- 8 are dead in this configuration: `WPACKET_reserve_bytes`'s growable-buffer branch (three), `maxmaxsize`'s last
  return (two), `put_value`'s NULL-buffer return (one), and `strncmp` (two: nothing calls it after fix D1);
- 4 are outside the claims: the shim's failure knob and `num == 0` test in `CRYPTO_zalloc`. They make allocation
  fail more often, and the specs allow any allocation failure;
- 1 mutates `inptr = tmpptr + 1`: the label loop no longer advances, so the call does not return, and termination
  is not claimed.

## VST lint

`qp lint`: clean (no switch falling off its end, no bit-field composites, no goto, no struct copies, no external
outside the environment in any spec's cone).

## The patch

`patch/difftest.sh 20000 1` (2026-10-23): the header shim, the extraction of the WPACKET functions and the idiom
edits change nothing. It builds the code with OpenSSL's real headers, unmodified, with the idiom edits alone and
with the whole patch, under gcc -O2, gcc -O1 with ASan and UBSan, and CompCert. Fix D1 changes results only among
the 1153 calls with an ACE prefix not in lowercase, and each of those calls gives what the lowercase prefix gives.
[patch/PATCH.md](patch/PATCH.md) has a longer run.
