// The reference model of the openssl-punycode laws: RFC 3492 (Punycode) decoding and encoding, RFC 3629 UTF-8, and
// the conversion ossl_a2ulabel documents (doc/internal/man3/ossl_punycode_decode.pod), over an output that behaves
// as OpenSSL's static WPACKET does (a write that does not fit is not done, and fails).
//
// Written from the RFC texts, not from OpenSSL's code: index-based plain C, 64-bit arithmetic with explicit
// comparisons against maxint (RFC 3492 6.4, "fail on overflow") instead of OpenSSL's division-based tests, the
// output a plain array with an explicit insertion.  It is part of each law's program, so it is verified too (its
// own functions get specifications in the proof).  Parameters (RFC 3492 section 5): base 36, tmin 1, tmax 26,
// skew 38, damp 700, initial_bias 72, initial_n 0x80, delimiter 0x2D; maxint = 2^32 - 1 (OpenSSL decodes into
// unsigned int).
#ifndef OSSL_PUNY_REF_H
#define OSSL_PUNY_REF_H
#include <stddef.h>

#define PR_BASE 36ull
#define PR_TMIN 1ull
#define PR_TMAX 26ull
#define PR_SKEW 38ull
#define PR_DAMP 700ull
#define PR_INITIAL_BIAS 72ull
#define PR_INITIAL_N 128ull
#define PR_DELIMITER 45                 // '-'
#define PR_MAXINT 4294967295ull         // 2^32 - 1: the decoder's integers are 32-bit unsigned
#define PR_LABEL_CAP 512                // ossl_a2ulabel decodes each "xn--" label into 512 code points (LABEL_BUF_SIZE)

// RFC 3492 section 5: the digit-value of a code point: 41..5A (A-Z) = 0..25, 61..7A (a-z) = 0..25, 30..39 (0-9)
// = 26..35; PR_BASE (36) when it has none.
static unsigned long long pr_digit_value(unsigned char c)
{
	if (c >= 65 && c <= 90)
		return (unsigned long long) c - 65;
	if (c >= 97 && c <= 122)
		return (unsigned long long) c - 97;
	if (c >= 48 && c <= 57)
		return (unsigned long long) c - 48 + 26;
	return PR_BASE;
}

// The code point of a digit-value d < 36, as an encoder writes it: a-z for 0..25, 0-9 for 26..35 (lowercase,
// RFC 3492 section 5).
static unsigned char pr_digit_char(unsigned long long d)
{
	if (d < 26)
		return (unsigned char) (97 + d);
	return (unsigned char) (48 + (d - 26));
}

// RFC 3492 6.2/6.3: the threshold t for position k with the current bias, clamped to [tmin, tmax].
static unsigned long long pr_threshold(unsigned long long k, unsigned long long bias)
{
	if (k <= bias)
		return PR_TMIN;
	if (k >= bias + PR_TMAX)
		return PR_TMAX;
	return k - bias;
}

// RFC 3492 6.1: bias adaptation.
static unsigned long long pr_adapt(unsigned long long delta, unsigned long long numpoints, int firsttime)
{
	unsigned long long k = 0;
	if (firsttime)
		delta = delta / PR_DAMP;
	else
		delta = delta / 2;
	delta = delta + delta / numpoints;
	while (delta > ((PR_BASE - PR_TMIN) * PR_TMAX) / 2) {
		delta = delta / (PR_BASE - PR_TMIN);
		k = k + PR_BASE;
	}
	return k + ((PR_BASE - PR_TMIN + 1) * delta) / (delta + PR_SKEW);
}

// The result of a decoding: ok, and the number of code points in the output array: at the end of a success, and at
// the moment of a failure (the output so far: basic code points copied before a non-basic one, the insertions made
// before the failing one).
struct pr_dec {
	int ok;
	size_t count;
};

// RFC 3492 6.2, the decoding procedure, into out[0..cap): the input is in[0..len) (octets, each one code point).
// Failure when a basic code point is not basic, a digit is missing or has no digit-value, an integer overflows
// maxint (6.4), or the output would hold more than cap code points (the interface of the RFC's sample decoder,
// appendix C: punycode_big_output; the basic code points are checked against cap before any is copied).
static void pr_decode(const unsigned char *in, size_t len, unsigned int *out, size_t cap, struct pr_dec *d)
{
	size_t b = 0;                   // the position of the last delimiter, 0 when there is none
	size_t j;
	d->ok = 0;
	d->count = 0;
	for (j = 0; j < len; j++)
		if (in[j] == PR_DELIMITER)
			b = j;
	// "consume all code points before the last delimiter (if there is one) and copy them to output, fail on any
	// non-basic code point"
	if (b > cap)
		return;
	for (j = 0; j < b; j++) {
		if (in[j] >= 128)
			return;
		out[j] = in[j];
		d->count = j + 1;
	}
	// "if more than zero code points were consumed then consume one more (which will be the last delimiter)"
	size_t pos = 0;
	if (b > 0)
		pos = b + 1;
	unsigned long long n = PR_INITIAL_N, i = 0, bias = PR_INITIAL_BIAS;
	while (pos < len) {
		unsigned long long oldi = i, w = 1, k = PR_BASE;
		for (;;) {
			if (pos >= len)
				return;                         // "consume a code point, or fail if there was none to consume"
			unsigned long long digit = pr_digit_value(in[pos]);
			pos++;
			if (digit >= PR_BASE)
				return;                         // "fail if it has none"
			i = i + digit * w;                      // i <= maxint, w <= maxint: no 64-bit overflow
			if (i > PR_MAXINT)
				return;                         // "fail on overflow"
			unsigned long long t = pr_threshold(k, bias);
			if (digit < t)
				break;
			w = w * (PR_BASE - t);
			if (w > PR_MAXINT)
				return;                         // "fail on overflow"
			k = k + PR_BASE;
		}
		size_t outlen = d->count;
		bias = pr_adapt(i - oldi, (unsigned long long) outlen + 1, oldi == 0);
		n = n + i / ((unsigned long long) outlen + 1);
		if (n > PR_MAXINT)
			return;                                 // "fail on overflow"
		i = i % ((unsigned long long) outlen + 1);
		if (outlen >= cap)
			return;                                 // the output is full
		// "insert n into output at position i"
		for (j = outlen; j > i; j--)
			out[j] = out[j - 1];
		out[i] = (unsigned int) n;
		d->count = outlen + 1;
		i = i + 1;
	}
	d->ok = 1;
}

// RFC 3492 6.3, the encoding procedure (no case flags): cps[0..m) into o[0..ocap), *olen octets.  Returns 1, or 0
// on an overflow (6.4) or when the output does not fit in ocap octets.
static int pr_encode(const unsigned int *cps, size_t m, unsigned char *o, size_t ocap, size_t *olen)
{
	unsigned long long n = PR_INITIAL_N, delta = 0, bias = PR_INITIAL_BIAS;
	size_t out = 0, b = 0, h, j;
	// "copy the basic code points to the output in order, followed by a delimiter if b > 0"
	for (j = 0; j < m; j++) {
		if (cps[j] < 128) {
			if (out >= ocap)
				return 0;
			o[out] = (unsigned char) cps[j];
			out++;
			b++;
		}
	}
	h = b;
	if (b > 0) {
		if (out >= ocap)
			return 0;
		o[out] = PR_DELIMITER;
		out++;
	}
	while (h < m) {
		// "let m = the minimum code point >= n in the input" (one exists: h < m)
		unsigned long long mm = PR_MAXINT + 1;
		for (j = 0; j < m; j++)
			if (cps[j] >= n && cps[j] < mm)
				mm = cps[j];
		// "let delta = delta + (m - n) * (h + 1), fail on overflow"
		if (delta > PR_MAXINT || mm - n > (PR_MAXINT - delta) / ((unsigned long long) h + 1))
			return 0;
		delta = delta + (mm - n) * ((unsigned long long) h + 1);
		n = mm;
		for (j = 0; j < m; j++) {
			unsigned long long c = cps[j];
			if (c < n) {
				delta = delta + 1;
				if (delta > PR_MAXINT)
					return 0;
			}
			if (c == n) {
				unsigned long long q = delta, k = PR_BASE;
				for (;;) {
					unsigned long long t = pr_threshold(k, bias);
					if (q < t)
						break;
					if (out >= ocap)
						return 0;
					o[out] = pr_digit_char(t + (q - t) % (PR_BASE - t));
					out++;
					q = (q - t) / (PR_BASE - t);
					k = k + PR_BASE;
				}
				if (out >= ocap)
					return 0;
				o[out] = pr_digit_char(q);
				out++;
				bias = pr_adapt(delta, (unsigned long long) h + 1, h == b);
				delta = 0;
				h++;
			}
		}
		delta = delta + 1;
		n = n + 1;
	}
	*olen = out;
	return 1;
}

// RFC 3629 section 3: the UTF-8 octets of code point c into o[0..4), their number; 0 for c > 0x10FFFF.  The
// surrogates U+D800..U+DFFF are encoded like every other code point below 0x10000 (three octets), as
// ossl_a2ulabel's codepoint2utf8 does (RFC 3629 forbids them in UTF-8; see STATUS.md).
static size_t pr_utf8(unsigned long long c, unsigned char *o)
{
	if (c < 128) {
		o[0] = (unsigned char) c;
		return 1;
	}
	if (c < 2048) {
		o[0] = (unsigned char) (192 + c / 64);
		o[1] = (unsigned char) (128 + c % 64);
		return 2;
	}
	if (c < 65536) {
		o[0] = (unsigned char) (224 + c / 4096);
		o[1] = (unsigned char) (128 + (c / 64) % 64);
		o[2] = (unsigned char) (128 + c % 64);
		return 3;
	}
	if (c <= 1114111) {
		o[0] = (unsigned char) (240 + c / 262144);
		o[1] = (unsigned char) (128 + (c / 4096) % 64);
		o[2] = (unsigned char) (128 + (c / 64) % 64);
		o[3] = (unsigned char) (128 + c % 64);
		return 4;
	}
	return 0;
}

// The output of ossl_a2ulabel: a buffer of cap octets that is filled from the start; a write of m octets is done
// when it fits in the room left (cap - len >= m) and is otherwise not done at all and marks the output short.
// This is OpenSSL's static WPACKET (WPACKET_init_static_len: "A failure will occur if you attempt to write beyond
// the end of the buffer"; WPACKET_memcpy and WPACKET_put_bytes write nothing when they fail; writing 0 octets
// always succeeds).
struct pr_sink {
	unsigned char *buf;
	size_t cap;
	size_t len;
	int short_;
};

static void pr_put(struct pr_sink *k, const unsigned char *p, size_t m)
{
	size_t j;
	if (m == 0)
		return;
	if (k->cap - k->len < m) {
		k->short_ = 1;
		return;
	}
	for (j = 0; j < m; j++)
		k->buf[k->len + j] = p[j];
	k->len = k->len + m;
}

// The conversion of ossl_a2ulabel, for a string s[0..n) (no NUL in it) and an output k with cap >= 1: the labels
// of s (split at every '.', empty ones included) in order, each followed by a '.' except the last, then a NUL.  A
// label that starts with the ACE prefix "xn--" in any case ("xn--", "Xn--", "xN--", "XN--": RFC 5890 2.3.1,
// XN-labels "begin with the prefix "xn--" (case independent)"; upstream tests the lowercase prefix only, fixed
// by patch D1) is the Punycode of its code points: its rest is decoded (pr_decode, at
// most PR_LABEL_CAP code points; a rest of 2^32 - 1 octets or more is rejected, as ossl_punycode_decode rejects
// such an input) and each code point is written in UTF-8; any other label is written as it is.  Returns -1 at the
// first label that does not decode or the first code point above 0x10FFFF (what was written before stays, no
// NUL), else 0 when some write did not fit, else 1.  cps: PR_LABEL_CAP code points of scratch space.
static int pr_a2ulabel(const unsigned char *s, size_t n, struct pr_sink *k, unsigned int *cps)
{
	size_t st = 0;
	unsigned char sep = 46;         // '.'
	unsigned char nul = 0;
	for (;;) {
		size_t e = st;
		while (e < n && s[e] != 46)
			e++;
		size_t m = e - st;
		if (m >= 4 && (s[st] == 120 || s[st] == 88) && (s[st + 1] == 110 || s[st + 1] == 78) && s[st + 2] == 45
		    && s[st + 3] == 45) {                                       // "xn--", any case
			struct pr_dec d;
			size_t j;
			if (m - 4 >= PR_MAXINT)
				return -1;
			pr_decode(s + st + 4, m - 4, cps, PR_LABEL_CAP, &d);
			if (!d.ok)
				return -1;
			for (j = 0; j < d.count; j++) {
				unsigned char u[4];
				size_t ul = pr_utf8(cps[j], u);
				if (ul == 0)
					return -1;
				pr_put(k, u, ul);
			}
		} else {
			pr_put(k, s + st, m);
		}
		if (e == n)
			break;
		pr_put(k, &sep, 1);
		st = e + 1;
	}
	pr_put(k, &nul, 1);
	if (k->short_)
		return 0;
	return 1;
}

#endif
