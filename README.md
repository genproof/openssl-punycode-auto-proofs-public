# OpenSSL Punycode: proved C specs

This repository proves 19 specs of `crypto/punycode.c` in OpenSSL 3.6.5: the functions `ossl_punycode_decode`
and `ossl_a2ulabel`, the code of CVE-2022-3602 and CVE-2022-3786. Each spec is a small C program
in `harness/` that states a property and that you can run, and each spec has a Coq theorem. AI agents wrote the proofs, about
36,000 lines of Coq that use VST (a Coq library for proofs about C), with QuickProof v0.1.0. Coq checks them,
so nothing in the proofs has to be trusted.

[SPECS.md](SPECS.md) explains Punycode, how to read a spec, and what each spec says.

## What is proved

For each spec, the theorem says (through VST's adequacy theorem, whose instance for QuickProof's environment is
upcoming; see Limits): for every value the spec draws, no run has undefined behaviour in CompCert's C semantics and
every check (`gp_assert`) holds. A read or write outside an object is undefined behaviour, so every theorem also
rules those out. For example, `rj_decode_any` says that for any bytes of any length and any capacity,
`ossl_punycode_decode` returns 1 or 0, reads and writes nothing outside its input and its array, and leaves the input
unchanged.

- 16 short specs (prefixes `rj_`, `rfc_`, `api_`, `rt_`) state one property each. Both functions accept any input
  and give only documented results; decoding follows RFC 3492 (its 19 samples, digits in either case, one encoding
  per sequence); the reported sizes are exact; labels are converted one by one; and OpenSSL decodes what an RFC 3492
  encoder writes, under the condition in "A limit of RFC 3492" below. Thirteen are 77 to 98 lines, including the 52-line
  shared header `harness/laws_common.h`; three are 124 to 143 lines (the RFC's samples, a UTF-8 writer and an RFC
  3492 encoder). Most use no model: they compare OpenSSL with itself, with the RFC's examples, or with simple facts
  about the input. Input lengths are any size the allocator provides, except that `rt_roundtrip` needs an encoding
  shorter than 2^32 - 1 bytes, OpenSSL's input limit.
- 3 `x_` specs compare both functions with a reference model, `harness/puny_ref.h`, written from the RFCs and from
  OpenSSL's documentation. `ossl_punycode_decode` agrees with the model's decoder on any input and capacity, and
  `ossl_a2ulabel` with the model's conversion on any string and output size. For up to 512 Unicode code points whose
  encoding by the model fits in 16 × count + 1 bytes, `ossl_punycode_decode` gives back the code points the model's
  encoder wrote, and `ossl_a2ulabel` their UTF-8 form when none of them is `.` or NUL.

Each spec is a theorem of its own in `src/contracts/laws.v`, and the theorem `suite` in `src/contracts/suite.v`
states all 19 together.

## Limits

- The code is patched: two edits for VST and one fix (next section). The theorems are about the patched file.
- The theorems are partial correctness. A call that never returns is not covered.
- They are about C as CompCert defines it, on x86_64 (LP64), in a release build (`-DNDEBUG`), compiled against a
  small header shim. They say nothing about a binary built by GCC or Clang.
- `malloc` may fail at any call. Those runs are covered too: they have no undefined behaviour, and each spec either
  states the result (-1) or checks nothing more.
- Only `crypto/punycode.c`, the ten functions of `crypto/packet.c` that it reaches and the shim unit are verified.
  The rest of OpenSSL, including the certificate code that calls `ossl_a2ulabel`, is not.
- The theorems are about runs of one thread. Running out of stack is not covered.
- The step from the Coq theorem to "no run has undefined behaviour" is VST's adequacy theorem, which is not yet
  instantiated in Coq for QuickProof's environment; that instance is upcoming. The theorems rest on eight standard
  axioms and six declarations of VST's malloc library (`qp verify` prints them).
- You must trust Coq, VST, CompCert's semantics of C, and `clightgen`, which translates the C files for Coq; and
  QuickProof's statement of the theorems, its translation scripts and `qp verify`. The specs, `quickproof.conf`,
  the header shim and the edits are what you review: tests check them, no proof does.
  `quickproof/docs/GUARANTEES.md` gives the details.

## The code under test

OpenSSL 3.6.5 (commit c8bd5a571085, tag openssl-3.6.5). `crypto/punycode.c` is identical in openssl-4.0.3 and in
master of 2026-10-12. Here it carries three edits, each marked with a `quickproof:` comment that keeps the original
line (`grep -n quickproof: crypto/punycode.c`):

- I1 and I2 are for the proof. VST has no rule for `goto`, and QuickProof's `memmove` is specified on bytes, which
  VST does not relate to the cells of an `unsigned int` array without extra lemmas. So two `goto end` become
  `break`, and a `memmove` over an `unsigned int` array becomes an element-by-element loop. They are meant
  to change nothing. [patch/PATCH.md](patch/PATCH.md) argues this, and a differential test checks it (100,000 calls
  for each of three seeds, identical outputs). It is tested, not proved.
- D1 fixes a bug (below): `ossl_a2ulabel` accepts the ACE prefix in any case
  (`XN--`, `Xn--`) through OpenSSL's own `HAS_CASE_PREFIX`.

The code is compiled against a header shim, `patch/include/`, instead of OpenSSL's generated headers. The shim
declares the one-bit bit-field `endfirst` as a plain `unsigned int`, since VST has no bit-fields. A small C unit,
`patch/shim/ossl_shim.c`, supplies OpenSSL's allocator and the string functions the code calls; it is verified with
the code. The ten WPACKET functions of `crypto/packet.c` that `ossl_a2ulabel` reaches are copied unchanged into
`patch/units/packet_ext.c`.

On unmodified 3.6.5, `rfc_ace_any_case` and `x_a2ulabel` are false. The other 17 specs also passed the sanitizer
runs on the unmodified code ([CHECK.md](CHECK.md)), but they are proved only for the patched file.

## The bug D1 fixes

`ossl_a2ulabel` decodes a label only when its ACE prefix is `xn--` in lowercase, although RFC
3490 and RFC 5890 make the prefix case-insensitive. An excluded e-mail name constraint written `XN--...` then does
not exclude the internationalized form of the address. We found it by running the spec `x_a2ulabel` natively on the
unmodified code, before its proof, and reported it to the OpenSSL security team on 2026-10-13. OpenSSL answered that
it is not a security issue, because it needs a misbehaving or malicious certificate authority, and asked for a
public issue or pull request with the fix.

## A limit of RFC 3492

This is a property of the RFC, not an OpenSSL bug. With 32-bit integers, the RFC's encoder can write a string that
the RFC's decoder, and OpenSSL's, must refuse. Within Unicode such a string encodes more than 3855 code points, so
it is far longer than a DNS label (63 bytes). `rt_roundtrip` claims the round trip whenever
(largest code point - 127) × count ≤ 2^32, which covers every sequence of up to 3855 Unicode code points. Beyond
that bound the decoder gives back the code points or refuses the string, never other code points.
[SPECS.md](SPECS.md#notes-on-the-behaviour-the-specs-pin-down) has the examples.

## Checking the proof

Use a QuickProof checkout of your own at v0.1.0, the release this repository pins. It needs 64-bit x86 Linux
with the toolchain that QuickProof's README lists (Coq 8.20.1, CompCert 3.15 and VST 2.15, installed with opam in
about half an hour), or QuickProof's Docker image, which contains that toolchain. Then:

```sh
git clone --recursive https://github.com/genproof/openssl-punycode-auto-proofs-public.git
/path/to/your/quickproof/tools/qp verify openssl-punycode-auto-proofs-public --base contract
```

`qp verify` rebuilds every proof. It checks that each theorem's statement is the one fixed at the commit tagged
`contract` (the specs, the code and the unproved theorems), that nothing is admitted, and which axioms each theorem
uses. It also compares the repository's copy of the framework, the `quickproof` submodule, with its own copy in the
16 files that decide what a theorem says and how C becomes Clight (the statement, the libc, the translation
chain), and refuses the repository if they differ. That is why the verifier should be your own checkout. Run from
the submodule (`quickproof/tools/qp verify . --base contract`), it would only compare that copy with itself, and
its report says so. The submodule holds the framework the proof is built with; running its `qp` is a convenience,
not an independent check.

A run takes about 17 minutes with 8 build jobs on 16 CPUs. `qp verify` builds this repository's Coq files with your
rights, so run it in a container if you do not trust them.

## Files

- `crypto/`, `include/`, `doc/`, `test/`, `fuzz/`: 14 files of OpenSSL 3.6.5, unchanged except `crypto/punycode.c`.
  The build uses `crypto/punycode.c` and `include/crypto/punycode.h`. The others are kept for reference: the headers
  the shim copies from, `crypto/packet.c` and `crypto/mem.c`, the caller `crypto/x509/v3_ncons.c`, and the
  documentation, test and fuzzer of the two functions.
- `harness/`: the 19 specs, their shared headers and the reference model `puny_ref.h`.
- `env/`: value generators for the native and interpreter test runs. The theorems do not depend on them.
- `patch/`: the edits (`osslpatch.py`), the header shim, the shim unit, the copied WPACKET functions, the
  differential test and [PATCH.md](patch/PATCH.md).
- `src/`: the Coq files. `src/contracts/` holds the theorem statements, `src/proof/` the proofs, and each `code.v`
  the Clight that `clightgen` generates from a C file.
- `quickproof/`: the framework, a submodule. `quickproof.conf` lists which C files become Clight, with which flags.
- [CONTRACT.md](CONTRACT.md) states what the theorems say and what is frozen; [CHECK.md](CHECK.md) lists the tests
  run before the proof (sanitizer runs, CompCert's interpreter, mutants).

## For Coq readers

`src/proof/punycode/PunySpec.v` specifies `ossl_punycode_decode`, `ossl_a2ulabel` and their static helpers as
exactly the plain-Coq model `src/proof/model/Model.v` (RFC 3492 decoding and OpenSSL's label conversion). The
WPACKET functions (`src/proof/packet/`), the shim (`src/proof/shim/`) and the libc (`src/proof/libc/`) are specified
under them. All 19 specs use these specifications.

The `x_` specs are proved in `src/proof/harness/`, assembled in its `a2ulabel/`, `decode/` and `roundtrip/`. Each
short spec is proved in `src/proof/laws/<name>/`: the facts about the model that it needs (plain Coq), the proof of
its `main` in pieces, and the assembly `<name>_proved`. `src/proof/laws/common/` specifies the seven helpers of
`harness/laws_common.h` and proves their bodies once for every spec that uses them. `rfc_samples` checks the RFC's
19 samples against the model by computation (`vm_compute`).

## Licence

Our files (the specs, the proofs, the scripts, the configuration and the documentation) are under the PolyForm
Noncommercial License 1.0.0 ([LICENSE.md](LICENSE.md), [NOTICE.md](NOTICE.md)), copyright 2026 GenProof. OpenSSL's
files and the files derived from them keep OpenSSL's licence, the Apache License 2.0 ([LICENSE.txt](LICENSE.txt)),
and [NOTICE.md](NOTICE.md) lists them and the one we altered; each Clight file `src/**/code.v` has the licence of the
C file `clightgen` generates it from.

We chose a noncommercial license to make QuickProof freely available for community use while reflecting CompCert’s
licensing restrictions. We remind users that commercial use of CompCert requires separate permission.

Maintained by Vladimir Kukharenko.
