# Contract: OpenSSL's Punycode decoder

This page states what the theorems are about and what was frozen before the proof.

## The code under test

OpenSSL 3.6.5, commit c8bd5a57108599ac650bbae77fcabe3109dab2e8. `crypto/punycode.c` and `include/crypto/punycode.h`
are identical in openssl-4.0.3 and in master of 2026-10-12.

- All of `crypto/punycode.c` (`ossl_punycode_decode`, `ossl_a2ulabel`, `adapt`, `is_basic`, `digit_decoded`,
  `codepoint2utf8`), as `patch/osslpatch.py` leaves it. I1: the two `goto end` of `ossl_a2ulabel` become `break`.
  I2: the `memmove` on the `unsigned int` output array of `ossl_punycode_decode` becomes typed element copies. I1
  and I2 are meant to change no behaviour; this is tested, not proved. D1: a fix, the ACE prefix in any
  case, with OpenSSL's own `HAS_CASE_PREFIX`.
- The ten functions of `crypto/packet.c` that `ossl_a2ulabel` reaches through its static WPACKET, copied verbatim
  into `patch/units/packet_ext.c`. `patch/extract.py --check TREE` compares them with an OpenSSL 3.6.5 checkout `TREE`.
- `patch/shim/ossl_shim.c`, the rest of the program in plain C: OpenSSL's default allocator with a failure knob and
  a live-block counter, `strlen`, `strchr`, `strncmp`, `OPENSSL_strncasecmp`, and a trapping `BUF_MEM_grow` on a
  dead path. It is verified with the code, not trusted.

The code is compiled against a header shim, `patch/include/`, because OpenSSL's generated headers need
`./Configure`. Every changed line of `crypto/punycode.c` keeps the original in a `quickproof:` comment.
[patch/PATCH.md](patch/PATCH.md) describes each edit and the shim, and `patch/difftest.sh` tests them against a
build with OpenSSL's real headers. `quickproof.conf` holds the configuration: x86_64 LP64, a release build
(`-DNDEBUG`).

## The programs

There is one program per spec: `harness/<name>.c` linked with the units it needs, among `crypto/punycode.c`,
`patch/units/packet_ext.c`, `patch/shim/ossl_shim.c`, `quickproof/libc/libc.c` and `quickproof/libc/malloc_unit.c`.
Each unit is one file of `src/units/`, and each spec's `whole_prog_undefined` checks its link.
`quickproof/tools/clight.sh quickproof.conf` translates the C files with `clightgen -normalize`; `malloc` and `free`
become the externals `quickproof_malloc` and `quickproof_free`.

## The specs

There are 19 specs. The 16 short ones (prefixes `api_`, `rfc_`, `rj_`, `rt_`) include the shared header
`harness/laws_common.h`. The 3 `x_` specs (`x_decode`, `x_a2ulabel`, `x_roundtrip`; `x_` stands for "extended")
include `harness/common.h` and the reference model `harness/puny_ref.h`. [SPECS.md](SPECS.md) introduces them. The
first comments of the `x_` specs and their env files call them `decode`, `a2ulabel` and `roundtrip`, without the
prefix. The files `env/*.c` only steer the native and interpreter runs of `quickproof/tools/qp check`; the theorems
do not depend on them.

## The claims

Each spec's theorem is `Theorem <name> : harness_safe whole_prog`, on the `whole_prog` of `src/contracts/<name>.v`.
`harness_safe`
(`quickproof/coq/QuickProof/Contract.v`) is VST's `semax_prog` for `whole_prog`, with the specifications of the
environment `QuickProof.Env`, which adds no axioms of its own. A failing check (`gp_assert`) is undefined behaviour.

VST's adequacy theorem turns such a judgement into a statement about runs: for every value the `nondet_*` functions
return, no run has undefined behaviour in CompCert's Clight semantics, so every check holds. That step is not yet a
Coq theorem about QuickProof's environment: the adequacy theorem has hypotheses about the external functions that
are not proved in Coq for it (`quickproof/docs/GUARANTEES.md`).

`src/contracts/suite.v` states all 19 specs in one theorem, `suite`.

The claims do not cover:

- what each spec leaves out: its first comment states its property, its bounds and its exclusions;
- termination (a run that never returns is not a counterexample);
- a binary built by another compiler, other platforms, other threads, or running out of stack;
- the rest of OpenSSL: only the code listed above is under test.

## Frozen after the commit tagged `contract`

- `harness/**`, `env/**`, the code under test (`crypto/`, `include/`, `patch/`), `quickproof/**` (the framework),
  `quickproof.conf`;
- the generated `src/**/code.v`;
- `src/units/*.v`; in `src/contracts/*.v`: the module `Harness`, the `link_*` definitions, `whole_prog` and the
  statement.

## Proved

Proved means, for each theorem: `Qed`, built from a clean checkout, and `Print Assumptions <name>` lists only
standard axioms and the abstract predicates of VST's malloc library (`mem_mgr`, `malloc_token` and its facts,
`create_mem_mgr`). `quickproof/tools/qp verify` checks this, and that every statement is the one of the contract.

## Status

All 19 specs are proved. The proof commit (`main`) proves `suite`, and each spec as a theorem of its own, with its
generated name and statement, on its contract file's `whole_prog` (`src/contracts/laws.v`: the `x_` specs as
projections of `suite_x`, the short specs as projections of `suite`). The contract files keep only their program. `qp
verify` checks it.
