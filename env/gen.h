// Input generators shared by the openssl-punycode env files (untrusted: they only steer native and interpreter
// runs; the theorems quantify over every value).  Plain C, so CompCert's interpreter runs it too.  It uses the
// harness's reference (harness/puny_ref.h) to build valid encodings and to aim the output sizes at the boundaries
// (exact fit, one short, one more).
#ifndef OSSL_PUNYCODE_ENV_GEN_H
#define OSSL_PUNYCODE_ENV_GEN_H
#include <stddef.h>
#include <stdint.h>
#include "../harness/puny_ref.h"

uint64_t quickproof_rnd(void);

#ifdef __COMPCERT__
#define EG_SMALL 1
#else
#define EG_SMALL 0
#endif

static size_t eg_r(size_t n)
{
	return n == 0 ? 0 : (size_t) (quickproof_rnd() % n);
}

static void eg_put32(uint8_t *buf, uint32_t v)
{
	buf[0] = (uint8_t) v;
	buf[1] = (uint8_t) (v >> 8);
	buf[2] = (uint8_t) (v >> 16);
	buf[3] = (uint8_t) (v >> 24);
}

static const char eg_alnum[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

// A code point: basic ones (letters and digits mostly, any ASCII sometimes), 2-, 3- and 4-octet ones, the
// surrogates, the boundaries of the UTF-8 forms; with wide != 0 also any 32-bit value (overflow paths).
static unsigned int eg_cp(int wide)
{
	size_t k = eg_r(wide ? 12 : 11);
	static const unsigned int edge[] = { 0x7F, 0x80, 0x81, 0x7FF, 0x800, 0xD7FF, 0xD800, 0xDBFF, 0xDC00, 0xDFFF, 0xE000,
	                                     0xFFFD, 0xFFFF, 0x10000, 0x10FFFE, 0x10FFFF };
	if (k < 2)
		return (unsigned int) eg_alnum[eg_r(sizeof eg_alnum - 1)];
	if (k == 2)
		return (unsigned int) eg_r(128);
	if (k < 5)
		return (unsigned int) (0x80 + eg_r(0x780));
	if (k < 7)
		return (unsigned int) (0x800 + eg_r(0xF800));
	if (k == 7)
		return (unsigned int) (0xD800 + eg_r(0x800));
	if (k == 8)
		return (unsigned int) (0x10000 + eg_r(0x100000));
	if (k < 11)
		return edge[eg_r(sizeof edge / sizeof edge[0])];
	k = eg_r(4);
	if (k == 0)
		return 0x110000u + (unsigned int) eg_r(16);
	if (k == 1)
		return 0xFFFFFFFFu - (unsigned int) eg_r(300);
	if (k == 2)
		return 0x80000000u + (unsigned int) eg_r(300);
	return (unsigned int) quickproof_rnd();
}

// m code points into cps, in one of a few shapes.
static void eg_cps(unsigned int *cps, size_t m, int wide)
{
	size_t k = eg_r(8), j;
	unsigned int a = eg_cp(wide), b = eg_cp(wide);
	for (j = 0; j < m; j++) {
		if (k == 0)
			cps[j] = a;                                 // all equal
		else if (k == 1)
			cps[j] = (j % 2) ? a : b;                   // alternating
		else if (k == 2)
			cps[j] = a > j ? a - (unsigned int) j : a;  // descending
		else if (k == 3)
			cps[j] = (j % 3 == 0) ? 0x10FFFF : (j % 3 == 1) ? 0x80 : 0x10000; // large deltas
		else
			cps[j] = eg_cp(wide);
	}
}

// A mutation of s[0..n) in place (room for n + 1): one octet replaced, inserted or deleted.  Returns the new length.
static size_t eg_mutate(unsigned char *s, size_t n, size_t room)
{
	static const unsigned char odd[] = { '-', '-', '*', 0x80, 0xFF, 'z', '9', 'A', '0', ' ', 0x7F };
	unsigned char c = eg_r(2) ? odd[eg_r(sizeof odd)] : (unsigned char) eg_alnum[eg_r(sizeof eg_alnum - 1)];
	size_t k = eg_r(3), p = eg_r(n + 1), j;
	if (k == 0 && n > 0) {
		s[p < n ? p : n - 1] = c;
		return n;
	}
	if (k == 1 && n + 1 <= room) {
		for (j = n; j > p; j--)
			s[j] = s[j - 1];
		s[p] = c;
		return n + 1;
	}
	if (n > 0) {
		if (p >= n)
			p = n - 1;
		for (j = p; j + 1 < n; j++)
			s[j] = s[j + 1];
		return n - 1;
	}
	return n;
}

// RFC 3492 section 7.1's sample strings and OpenSSL's own test vectors (test/punycode_test.c), as encoded.
static const char *const eg_vectors[] = {
	"e28h", "egbpdaj6bu4bxfgehfvwxn", "ihqwcrb4cv8a8dqg056pqjye", "ihqwctvzc91f659drss3x8bo0yb",
	"Proprostnemluvesky-uyb24dma41a", "4dbcagdahymbxekheh6e0a7fei0b", "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd",
	"n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa", "b1abfaaepdrnnbgefbaDotcwatmq2g4l",
	"PorqunopuedensimplementehablarenEspaol-fmd56a", "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g",
	"3B-ww4c5e180e575a65lsy2b", "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n", "Hello-Another-Way--fc4qua05auwb3674vfr0b",
	"2-u9tlzr9756bt3uc0v", "MajiKoi5-783gue6qz075azm5e", "de-jg4avhby1noc0d", "d9juau41awczczp", "-> $1.00 <--",
	"e-*", "e-999", "e-999999999", "e-Oy65t", "a", "", "-", "--", "-a", "a-", "abc-", "99999999", "zzzzzzzz",
};

static size_t eg_copy_str(unsigned char *s, size_t room, const char *v)
{
	size_t n = 0;
	while (v[n] != 0 && n < room) {
		s[n] = (unsigned char) v[n];
		n++;
	}
	return n;
}

// The variable-length integer of q (any 64-bit value: above 2^32 - 1 too) with the given bias, as RFC 3492's encoder
// writes a delta (lowercase digits), into s; its length.
static size_t eg_varint(unsigned long long q, unsigned long long bias, unsigned char *s, size_t room)
{
	unsigned long long k = PR_BASE;
	size_t n = 0;
	for (;;) {
		unsigned long long t = pr_threshold(k, bias);
		if (q < t)
			break;
		if (n < room)
			s[n++] = pr_digit_char(t + (q - t) % (PR_BASE - t));
		q = (q - t) / (PR_BASE - t);
		k += PR_BASE;
	}
	if (n < room)
		s[n++] = pr_digit_char(q);
	return n;
}

// Deltas at the overflow boundaries of the decoder: a first delta i near 2^32 - 1 - 0x7F (n = 0x80 + i just below or
// above 2^32 - 1) or just above 2^32 - 1 (i overflows); or a first delta that takes n near 2^32 - 1 and a second one
// that takes it over (n + i / 2 > 2^32 - 1, the bound of the n check with one code point in the output).
static size_t eg_overflow(unsigned char *s, size_t room)
{
	size_t k = eg_r(4), n = 0;
	unsigned long long v;
	if (k == 0) {
		v = PR_MAXINT - 127 - 4 + eg_r(9);
		return eg_varint(v, PR_INITIAL_BIAS, s, room);
	}
	if (k == 1) {
		v = PR_MAXINT - 3 + eg_r(8);
		return eg_varint(v, PR_INITIAL_BIAS, s, room);
	}
	if (k == 2 && room > 2) {               // basic code points first: n = 0x80 + i / (b + 1)
		size_t b = 1 + eg_r(3), j;
		for (j = 0; j < b; j++)
			s[n++] = 'a';
		s[n++] = '-';
		v = (PR_MAXINT - 127) * (b + 1) - 2 + eg_r(4);
		if (v > PR_MAXINT)
			v = PR_MAXINT - eg_r(3);
		return n + eg_varint(v, PR_INITIAL_BIAS, s + n, room - n);
	}
	unsigned long long v1 = PR_MAXINT - 127 - eg_r(1000);       // n = 0x80 + v1, then i = 1
	n = eg_varint(v1, PR_INITIAL_BIAS, s, room);
	unsigned long long left = PR_MAXINT - (128 + v1);            // n may grow by this much
	unsigned long long v2 = 2 * left + eg_r(6);                   // n + (1 + v2) / 2 near 2^32 - 1
	if (v2 >= 2)
		v2 -= 2;
	return n + eg_varint(v2, pr_adapt(v1, 1, 1), s + n, room - n);
}

// A Punycode-ish string into s (room octets), its length.
static size_t eg_puny(unsigned char *s, size_t room)
{
	unsigned int cps[600];
	size_t k = eg_r(20), n = 0, m, j;
	if (k >= 18)
		return eg_overflow(s, room);
	if (k < 7 || k == 15 || k == 16) {          // a valid encoding, sometimes mutated or with uppercase digits
		m = k == 15 ? 100 + eg_r(EG_SMALL ? 60 : 500) : k == 16 ? 500 + eg_r(30) : eg_r(eg_r(4) ? 12 : 60);
		if (EG_SMALL && m > 160)
			m = 160;
		eg_cps(cps, m, 0);
		if (!pr_encode(cps, m, s, room, &n))
			n = 0;
		if (eg_r(4) == 0)
			for (j = 0; j < n; j++)
				if (s[j] >= 'a' && s[j] <= 'z' && eg_r(2))
					s[j] = (unsigned char) (s[j] - 32);
		if (k >= 5 && k < 7) {
			size_t e = 1 + eg_r(3);
			while (e-- > 0)
				n = eg_mutate(s, n, room);
		}
		return n;
	}
	if (k == 7) {                               // any letters, digits, hyphens
		m = eg_r(30);
		for (j = 0; j < m && n < room; j++)
			s[n++] = (unsigned char) (eg_r(8) == 0 ? '-' : eg_alnum[eg_r(sizeof eg_alnum - 1)]);
		return n;
	}
	if (k == 8) {                               // tiny, over the octets that matter
		static const unsigned char tiny[] = { '-', '-', 'a', 'b', '9', 'z', 'A', 0x80, 0xFF, '*', '0', '.' };
		m = eg_r(7);
		for (j = 0; j < m && n < room; j++)
			s[n++] = tiny[eg_r(sizeof tiny)];
		return n;
	}
	if (k == 9) {                               // long digit runs: the overflow checks
		static const unsigned char big[] = { '9', 'z', 'Z', '8', '0', 'a', 'y' };
		if (eg_r(2))
			n = eg_copy_str(s, room, eg_r(2) ? "ab-" : "a-");
		m = 3 + eg_r(12);
		for (j = 0; j < m && n < room; j++)
			s[n++] = big[eg_r(sizeof big)];
		return n;
	}
	if (k == 10) {                              // basic code points (any ASCII), a delimiter, some digits
		m = eg_r(eg_r(3) ? 20 : EG_SMALL ? 200 : 600);
		for (j = 0; j < m && n < room; j++)
			s[n++] = (unsigned char) (eg_r(3) ? eg_alnum[eg_r(sizeof eg_alnum - 1)] : eg_r(128));
		if (n < room)
			s[n++] = '-';
		m = eg_r(6);
		for (j = 0; j < m && n < room; j++)
			s[n++] = (unsigned char) eg_alnum[eg_r(sizeof eg_alnum - 1)];
		return n;
	}
	if (k == 11) {                              // a non-basic octet before the last delimiter
		m = eg_r(8);
		for (j = 0; j < m && n < room; j++)
			s[n++] = (unsigned char) eg_alnum[eg_r(sizeof eg_alnum - 1)];
		if (n < room)
			s[n++] = (unsigned char) (128 + eg_r(128));
		if (n < room)
			s[n++] = '-';
		if (n < room)
			s[n++] = 'a';
		return n;
	}
	if (k == 12)                                // known vectors
		return eg_copy_str(s, room, eg_vectors[eg_r(sizeof eg_vectors / sizeof eg_vectors[0])]);
	if (k == 13) {                              // encodings of any 32-bit values: overflow at the boundaries
		m = 1 + eg_r(4);
		eg_cps(cps, m, 1);
		if (!pr_encode(cps, m, s, room, &n))
			n = 0;
		return n;
	}
	// k == 14, 17: random octets of any value
	m = eg_r(12);
	for (j = 0; j < m && n < room; j++)
		s[n++] = (unsigned char) quickproof_rnd();
	return n;
}

// The output bound of a decoding of s[0..n), aimed at the boundaries: the number of code points the reference
// decodes (scratch: room code points), one less, one more, the number of basic code points, 0..2, a large one, any.
static uint32_t eg_cap(const unsigned char *s, size_t n, unsigned int *scratch, size_t room)
{
	struct pr_dec d;
	size_t b = 0, j;
	pr_decode(s, n, scratch, room, &d);
	for (j = 0; j < n; j++)
		if (s[j] == '-')
			b = j;
	size_t c = d.count, k = eg_r(12);
	if (k < 3)
		return (uint32_t) c;
	if (k < 5)
		return (uint32_t) (c > 0 ? c - 1 : 0);
	if (k == 5)
		return (uint32_t) (c + 1);
	if (k == 6)
		return (uint32_t) (eg_r(2) ? b : b > 0 ? b - 1 : 0);
	if (k == 7)
		return (uint32_t) eg_r(3);
	if (k == 8)
		return (uint32_t) (EG_SMALL ? 600 : 1 + eg_r(70000));
	return (uint32_t) eg_r(c + 4);
}

// One label of a host name at s (room octets left), its length: "xn--" + a Punycode-ish string (env/gen.h),
// "XN--"/"Xn--"/"xN--"/"xn-"/"xn"/"x"/"xn---" (+ one sometimes), an LDH label, any octets but '.' and NUL, empty.
static size_t eg_label(unsigned char *s, size_t room)
{
	size_t k = eg_r(12), j, m, n = 0;
	static const char *const pre[] = { "xn--", "XN--", "Xn--", "xN--", "xn-", "xn", "x", "xn---" };
	if (room < 8)
		return 0;
	if (k < 5) {
		n = eg_copy_str(s, room, "xn--");
		return n + eg_puny(s + n, room - n);
	}
	if (k == 5) {
		n = eg_copy_str(s, room, pre[eg_r(sizeof pre / sizeof pre[0])]);
		if (eg_r(2))
			n += eg_puny(s + n, room - n);
		return n;
	}
	if (k < 9) {
		m = eg_r(eg_r(4) ? 16 : 70);
		for (j = 0; j < m && n < room; j++)
			s[n++] = (unsigned char) (eg_r(10) == 0 ? '-' : eg_alnum[eg_r(sizeof eg_alnum - 1)]);
		return n;
	}
	if (k == 9) {
		m = eg_r(10);
		for (j = 0; j < m && n < room; j++) {
			unsigned char c = (unsigned char) quickproof_rnd();
			s[n++] = (c == 0 || c == '.') ? 0xC3 : c;
		}
		return n;
	}
	return 0;
}

// A host name into s (room octets): labels joined by '.', sometimes a NUL inside (the string ends there).  Its
// length (the NUL included when there is one inside).
static size_t eg_host(unsigned char *s, size_t room)
{
	size_t labels = eg_r(8) == 0 ? eg_r(EG_SMALL ? 12 : 40) : 1 + eg_r(4), j, n = 0;
	for (j = 0; j < labels && n + 8 < room; j++) {
		if (j > 0)
			s[n++] = '.';
		n += eg_label(s + n, room - n - 1);
	}
	if (eg_r(20) == 0 && n > 0)
		s[eg_r(n)] = 0;
	return n;
}

// The output size for ossl_a2ulabel on s[0..n) (up to its first NUL), aimed at the boundaries: what the
// reference conversion needs with its NUL, one less, one more, 0..2, less than the first label, a large one, any.
// scratch: room octets for the reference output; cps: PR_LABEL_CAP code points.
static size_t eg_outlen(const unsigned char *s, size_t n, unsigned char *scratch, size_t room, unsigned int *cps)
{
	struct pr_sink k;
	size_t sl = 0, first = 0;
	while (sl < n && s[sl] != 0)
		sl++;
	k.buf = scratch;
	k.cap = room;
	k.len = 0;
	k.short_ = 0;
	int r = pr_a2ulabel(s, sl, &k, cps);
	size_t need = k.len, c = eg_r(14);
	while (first < sl && s[first] != '.')
		first++;
	if (r < 0)
		return eg_r(4) == 0 ? 0 : eg_r(need + 8);
	if (c < 4)
		return need;
	if (c < 7)
		return need > 0 ? need - 1 : 0;
	if (c == 7)
		return need + 1;
	if (c == 8)
		return eg_r(3);
	if (c == 9)
		return first > 1 ? eg_r(first) : 1;
	if (c == 10)
		return EG_SMALL ? 256 : 4096;
	return eg_r(need + 3);
}

#endif
