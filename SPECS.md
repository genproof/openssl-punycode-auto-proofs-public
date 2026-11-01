# The specs

This repository proves properties of OpenSSL's Punycode decoder. Each property is stated by a spec: a small C program
in `harness/` that you can run. QuickProof turns each spec into a Coq theorem: for every input the spec draws, none
of its checks (`gp_assert`) fails and nothing it runs has undefined behaviour (through VST's adequacy theorem, whose
instance for QuickProof's environment is upcoming). This page explains Punycode and the two OpenSSL functions, how to
read a spec, and what each spec says.

## Punycode and the two functions

Domain names with non-ASCII letters ("bücher.example") travel in ASCII. Each such label is written as `xn--`
followed by its Punycode form ("xn--bcher-kva.example"). RFC 3492 defines Punycode; RFC 3490 and RFC 5890-5891
(IDNA) define the `xn--` prefix, the *ACE prefix*.

A label is a sequence of code points (numbers: Unicode characters). Its Punycode form has two parts:

- the *basic* code points (ASCII, below 0x80) are copied literally, in order, followed by a `-` (the *delimiter*)
  when there are any;
- after the last `-`, a sequence of *deltas*, each written as a variable-length number with the digits `a`-`z` and
  `0`-`9` (in either case). Each delta says which code point to insert next and where.

In "bcher-kva", the basic part is "bcher", and the delta "kva" inserts ü (U+00FC) at position 1.

`ossl_punycode_decode(in, len, out, &n)` decodes one Punycode string (without its `xn--`) into an array of `n` code
points. It returns 1 and sets `n` to the number of code points, or 0.

`ossl_a2ulabel(name, out, outlen)` converts a whole host name: every `.`-separated label that starts with `xn--` is
decoded and written in UTF-8, every other label is copied, and a NUL ends the output. It returns 1, 0 ("the output
buffer is too small") or -1 (bad Punycode or another error). OpenSSL uses it when it checks certificates' name
constraints on internationalized e-mail addresses (`crypto/x509/v3_ncons.c`).

Both functions had memory-safety bugs in 2022: CVE-2022-3602 (`ossl_punycode_decode` wrote one code point past the
end of its array) and CVE-2022-3786 (`ossl_a2ulabel` overflowed its output with the `.` between labels).

## How to read a spec

```c
size_t len = upto(PTRDIFF_MAX);            // any length the allocator provides
unsigned char *input = any_bytes(len);     // any len bytes
unsigned int cap = nondet_u32();           // any capacity
unsigned int *out = any_uints(cap);        // an array of exactly cap elements, holding any values
... call OpenSSL ...
gp_assert(r == 1 || r == 0);               // what must hold
```

- `nondet_*`, `upto(max)`, `any_bytes(n)` and `any_uints(n)` stand for *any* value: the theorem covers every one of
  them. Inputs, capacities, output sizes and the initial contents of every buffer are arbitrary.
- Every buffer has exactly the size the spec gives it, so a single byte read or written past its end is undefined
  behaviour, which the theorem excludes.
- `gp_assume(c)` restricts the inputs the spec talks about. An early `return 0` before the checks also leaves a case
  out: a failed allocation, or a result the spec says nothing about.
- `gp_assert(c)` is the property.
- When the allocation fails: `ossl_a2ulabel` allocates a small record with OpenSSL's allocator. In the theorems
  `malloc` may fail at any call; the specs either state what then happens (-1) or claim nothing for that run, and
  say which.
- The first comment of each spec states it in words, with its restrictions, and the tables below summarize it. Where
  the comment and the table differ, the comment is right. The theorem covers exactly the checks in the code.
- Each spec includes one shared header, `harness/laws_common.h` (52 lines: any value up to a bound, any bytes, any
  array, a copy, two comparisons, the position of the last `-`; no model of Punycode). The line counts below include
  it. Most specs use no model at all: they compare OpenSSL with itself (two calls), with the RFC's own examples, or
  with simple facts about the input. Two specs carry a small reference written from an RFC, in their own file:
  `rt_roundtrip` the encoder of RFC 3492, `rfc_a2ulabel_utf8` UTF-8 (RFC 3629).
- Most specs quote the RFC sentence, or the line of OpenSSL's documentation or source, that they come from.

## The code under test

OpenSSL 3.6.5 (`crypto/punycode.c`, and the functions of `crypto/packet.c` that `ossl_a2ulabel` reaches), with the
edits listed in [patch/PATCH.md](patch/PATCH.md): two idiom edits that VST needs (I1, I2) and one fix (D1: the ACE
prefix in any case). Every changed line keeps the original in a `quickproof:` comment.

## The specs

All 19 specs below are proved. [CHECK.md](CHECK.md) lists the tests all 19 passed before the proof of the 16 short
ones. [CONTRACT.md](CONTRACT.md) and `src/contracts/` state each theorem exactly.

### Any input (`rj_`): safe, and only the documented results

| spec | lines | what it says |
|---|---|---|
| `rj_decode_any` | 77 | Any bytes of any length and any capacity: `ossl_punycode_decode` returns 1 (with a length at most the capacity) or 0 (length unchanged), as its documentation says, and leaves the input as it was. |
| `rj_decode_invalid` | 86 | Input with a byte that RFC 3492 6.2 says to fail on is refused (0, length unchanged): a non-ASCII byte before the last `-`, or a byte after it that is neither a letter nor a digit. |
| `rj_a2ulabel_any` | 81 | Any string and any output size, NULL output included: `ossl_a2ulabel` returns 1, 0 or -1 (as documented; -1 for a NULL or empty output), writes only inside its buffer (CVE-2022-3786 overflowed it with the `.` between labels), leaves the string as it was and frees what it allocates. |

### The standard (`rfc_`)

| spec | lines | what it says |
|---|---|---|
| `rfc_samples` | 131 | The 19 sample strings of RFC 3492 7.1 decode to exactly the code points the RFC lists. |
| `rfc_basic_first` | 90 | If any byte before the last `-` is 0x80 or above, decoding fails. On success, the code points below 0x80 are exactly the bytes before the last `-`, in order (RFC 3492 3.1, 6.2). |
| `rfc_digit_case` | 87 | Changing the case of any letters among the deltas changes nothing: the same result, length and code points (RFC 3492 5: "A decoder MUST recognize the letters in both uppercase and lowercase forms"). |
| `rfc_unique` | 88 | Two inputs that both decode (1) to the same code points, into arrays of the same capacity, are the same bytes up to the case of the delta letters (RFC 3492 6.2: "only one encoded string ... can represent a given sequence of integers"). |
| `rfc_ace_any_case` | 91 | `ossl_a2ulabel` converts a name that starts with `xn--`, `Xn--`, `xN--` or `XN--` the same way: the same result and the same buffer (RFC 3490 5: the ACE prefix is "xn--" or any capitalization thereof), when the allocation fails in neither call or in both. False on unmodified OpenSSL, true with fix D1. |
| `rfc_a2ulabel_utf8` | 124 | For s without `.` or NUL and an output of at least one byte: `xn--` + s becomes exactly the UTF-8 form (RFC 3629) of the code points `ossl_punycode_decode` gives for s into 512 elements, and a NUL. The result is -1 when that decoding fails, when it gives a code point above U+10FFFF, or when the allocation fails; it is 0 when the output does not fit. |

### The interface (`api_`)

| spec | lines | what it says |
|---|---|---|
| `api_decode_capacity` | 94 | Nothing is written past the reported length, the reported length is exactly the capacity needed, and one element fewer is refused (CVE-2022-3602 was a write one element past the end). |
| `api_decode_deterministic` | 78 | The result depends only on the bytes given: the same bytes elsewhere, followed by anything, decode the same way into two arrays of the same capacity. |
| `api_a2ulabel_copy` | 88 | With an output of at least one byte, a name with no label starting with `xn--` (in any case) is copied as it is, with its NUL, when it fits ("If it does not start with xn--, it becomes U-label as is", `crypto/punycode.c`); else the result is 0. When the allocation fails, the result is -1. |
| `api_a2ulabel_nul` | 80 | On success (1) the output holds a NUL, and nothing after the first NUL was touched ("The output buffer is NUL-terminated"). |
| `api_a2ulabel_size` | 86 | For a name that converts (1) into some buffer: any buffer of at least that output's size gives 1 and the same output, and any smaller buffer of at least one byte gives 0 (when the allocation fails in no call). |
| `api_a2ulabel_labels` | 98 | Labels are converted one by one. When s1 and s2 each convert (1), the name s1`.`s2 converts, into a buffer as large as their two buffers together, to the output of s1, a `.`, and the output of s2. When either gives -1, so does the name (when the allocation fails in no call). |

### Round trip (`rt_`)

| spec | lines | what it says |
|---|---|---|
| `rt_roundtrip` | 143 | Any number of any 32-bit code points, encoded by an RFC 3492 encoder written in the spec, when the encoder succeeds and the encoding is shorter than 2^32 - 1 bytes (OpenSSL's input limit): OpenSSL decodes them back whenever (largest code point - 127) × count ≤ 2^32. Beyond that bound it decodes them back or refuses them (0), never to other code points (see "The edge of RFC 3492" below). |

### Against a reference model (`x_`)

The three `x_` specs compare the two functions with a complete reference model, `harness/puny_ref.h` (323 lines,
with `harness/common.h`, 50 lines). The model is written from RFC 3492, RFC 3629 and OpenSSL's documentation of
`ossl_a2ulabel`. It also fixes what the RFCs leave open: what the array holds after a failure, a write that does not
fit in the output (skipped, as OpenSSL's WPACKET does), 512 code points per label, and the input limit. The short
specs each say less, but need no model. The first comments of the `x_` specs use their names without the prefix
(`decode`, `a2ulabel`, `roundtrip`).

| spec | lines | what it says |
|---|---|---|
| `x_decode` | 61 + 50 + 323 | `ossl_punycode_decode` on any input and capacity gives exactly what the model's RFC 3492 decoder gives: the result, the length and the whole array. |
| `x_a2ulabel` | 70 + 50 + 323 | `ossl_a2ulabel` on any string and output size, out NULL or not, the allocation failing or not, gives exactly what the model's conversion gives: the result and the whole buffer. |
| `x_roundtrip` | 88 + 50 + 323 | Up to 512 Unicode code points whose encoding by the model fits in 16 × count + 1 bytes: `ossl_punycode_decode` gives them back, and when no code point is `.` or NUL, `ossl_a2ulabel` gives their UTF-8 form. |

The first comment of `harness/x_a2ulabel.c` says that CVE-2022-3602, like CVE-2022-3786, overran the buffer of the
caller `nc_email_eai`. CVE-2022-3602 was the write of one code point past the array that `ossl_a2ulabel` passes to
`ossl_punycode_decode`, as described above.

## What the specs do not say

- **Time.** A theorem says what holds *if* a call returns; it does not say that it returns.
- **The binary.** The theorems are about the C code as CompCert's semantics defines it (x86_64, a release build with
  `NDEBUG`). It is compiled against a small header shim instead of OpenSSL's generated headers, and linked with a C
  unit for OpenSSL's allocator and a few string functions (`patch/PATCH.md`). The theorems say nothing about a binary
  built by another compiler. They are about runs of one thread, and they do not cover running out of stack
  (`ossl_a2ulabel` keeps a 2 KB array on the stack).
- **The rest of OpenSSL.** Only `crypto/punycode.c` and the parts of `crypto/packet.c` it reaches are code under
  test, verified together with the shim unit; the certificate code that calls them is not.

## Notes on the behaviour the specs pin down

- The ACE prefix in any case. Unmodified OpenSSL decodes a label only when it starts with `xn--` in lowercase; `XN--`
  labels are copied as they are, although RFC 3490 and 5890 make the prefix case-insensitive. In a name constraint
  this lets an excluded `XN--...` name fail to exclude the decoded form. We reported it to the OpenSSL security team,
  which answered that it is not a security issue (it needs a misbehaving or malicious certificate authority) and
  asked for a public issue or pull request. Fix D1 applies OpenSSL's own `HAS_CASE_PREFIX` macro. `rfc_ace_any_case`
  fails on the unmodified code.
- The output on 0. When the output does not fit, `ossl_a2ulabel` skips each write that does not fit and still does
  the later ones that fit. The buffer then need not hold a prefix of the result and may have no NUL. (The
  documentation says "The output buffer is NUL-terminated"; `api_a2ulabel_nul` states it for the result 1.) The
  only caller treats 0 as a failure.
- No IDNA validity check. Any `xn--` label is Punycode-decoded: surrogates (U+D800..U+DFFF), which UTF-8 excludes,
  are written as three bytes, and an `xn--` label that decodes to plain ASCII is accepted. `rfc_a2ulabel_utf8`
  states what is written.
- The edge of RFC 3492. The RFC's encoder checks that each delta it writes fits in 32 bits. Its decoder adds each
  delta to the position just after the previous insertion (the counter `i`) and checks that this sum fits in 32
  bits. So the RFC's own encoder can write a string that its decoder must refuse. For the code points 0x80, 0x80,
  0x555555D5 the last delta is exactly 2^32 - 1, and the decoder adds it to 2. For 4368 times U+0080 followed by
  U+F008F, within Unicode, the last delta is 2^32 - 1 too, and the decoder adds it to 4368. OpenSSL follows the RFC
  and refuses these strings (result 0). This is a property of RFC 3492 with 32-bit integers, not an OpenSSL bug.
  Within Unicode it needs encoded strings far longer than a DNS label (63 bytes). `rt_roundtrip` claims the round
  trip under a simple sufficient condition: (largest code point - 127) × count ≤ 2^32. That keeps the decoder's
  counter below 2^32 and covers every sequence of up to 3855 Unicode code points. Past that bound, the decoder gives
  back the code points or refuses them, never other code points.
