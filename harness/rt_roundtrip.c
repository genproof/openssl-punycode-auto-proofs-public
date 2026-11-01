// Law rt_roundtrip: OpenSSL decodes what RFC 3492's encoder writes. For any m code points (any number the allocator
// provides, any 32-bit values), encoded by encode() below (RFC 3492 6.3, the overflow checks of 6.4, maxint = 2^32 - 1)
// into an object of any size: when the encoding fits and has fewer than 2^32 - 1 octets (the most OpenSSL takes),
// ossl_punycode_decode, into an array of exactly m elements holding any values, gives back the m code points (result
// 1) whenever (largest code point - 127) * m <= 2^32; otherwise it gives them back or fails (0, *pout_length
// unchanged): there its i (insertion position plus delta) can pass 2^32 - 1 where the encoder's delta does not.
#include "laws_common.h"

static uint64_t rfc_adapt(uint64_t delta, uint64_t numpoints, int firsttime) {   // RFC 3492 6.1, adapt
	uint64_t k = 0;
	delta = firsttime ? delta / 700 : delta / 2;                            // damp = 700
	delta = delta + delta / numpoints;
	for (; delta > 455; k = k + 36)                                        // ((base - tmin) * tmax) div 2; base
		delta = delta / 35;                                                 // base - tmin
	return k + 36 * delta / (delta + 38);                                   // skew = 38
}
static int put(unsigned char *out, size_t room, size_t *len, uint64_t c) {   // output c, if there is room
	if (*len >= room)
		return 0;
	out[*len] = (unsigned char) c;
	*len = *len + 1;
	return 1;
}
static uint64_t digit(uint64_t d) { return d < 26 ? 'a' + d : '0' + d - 26; }   // RFC 3492 5, in lowercase
// RFC 3492 6.3 in 64-bit arithmetic: 1 with the encoding in out[0..*len), or 0 on an overflow or when out is full
static int encode(const unsigned int *cps, size_t m, unsigned char *out, size_t room, size_t *len) {
	uint64_t n = 128, delta = 0, bias = 72, b = 0, h, q, k, t;            // initial_n, initial_bias
	*len = 0;
	for (size_t j = 0; j < m; j++)        // "copy them to the output in order, followed by a delimiter if b > 0"
		if (cps[j] < 128) {
			if (!put(out, room, len, cps[j]))
				return 0;
			b = b + 1;
		}
	if (b > 0 && !put(out, room, len, '-'))
		return 0;
	for (h = b; h < m; n = n + 1) {
		uint64_t min = UINT64_MAX;        // "let m = the minimum {non-basic} code point >= n in the input"
		for (size_t j = 0; j < m; j++)
			if (cps[j] >= n && cps[j] < min)
				min = cps[j];
		if (delta > 0xFFFFFFFF || min - n > (0xFFFFFFFF - delta) / (h + 1))   // "fail on overflow"
			return 0;
		delta = delta + (min - n) * (h + 1);
		n = min;
		for (size_t j = 0; j < m; j++) {
			if (cps[j] < n) {             // "increment delta, fail on overflow"
				delta = delta + 1;
				if (delta > 0xFFFFFFFF)
					return 0;
			}
			if (cps[j] == n) {            // "output" delta as a generalized variable-length integer
				q = delta;
				for (k = 36;; k = k + 36) {   // t: tmin = 1, tmax = 26
					t = k <= bias ? 1 : k >= bias + 26 ? 26 : k - bias;
					if (q < t)
						break;
					if (!put(out, room, len, digit(t + (q - t) % (36 - t))))
						return 0;
					q = (q - t) / (36 - t);
				}
				if (!put(out, room, len, digit(q)))
					return 0;
				bias = rfc_adapt(delta, h + 1, h == b);
				delta = 0;
				h = h + 1;
			}
		}
		delta = delta + 1;
	}
	return 1;
}

int main(void) {
	// Choose the inputs: any number of any code points, any room for the encoding
	size_t m = upto(PTRDIFF_MAX / sizeof(unsigned int)), room = upto(PTRDIFF_MAX), len;
	unsigned int *cps = any_uints(m), *out = any_uints(m);
	unsigned char *encoding = malloc(room);
	if (cps == NULL || out == NULL || encoding == NULL || !encode(cps, m, encoding, room, &len) || len >= 0xFFFFFFFF)
		return 0;
	uint64_t largest = 0;
	for (size_t j = 0; j < m; j++)
		largest = cps[j] > largest ? cps[j] : largest;
	unsigned int count = (unsigned int) m;
	int r = ossl_punycode_decode((const char *) encoding, len, out, &count);
	// Check
	if (largest <= 127 || largest - 127 <= ((uint64_t) 1 << 32) / m)
		gp_assert(r == 1);
	gp_assert(r == 1 ? count == m && uints_eq(out, cps, m) : r == 0 && count == m);
	return 0;
}
