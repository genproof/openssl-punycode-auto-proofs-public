// Law decode: ossl_punycode_decode is RFC 3492 decoding, exactly.  For ANY input of ANY length len (any octets,
// NUL and octets >= 0x80 included; a NULL pointer when len is 0 and malloc(0) gives one) and ANY output bound
// cap (any unsigned int; *pout_length = cap on entry), with an output array of exactly cap unsigned ints holding
// any values: no undefined behaviour, and
//  - len >= 2^32 - 1 (UINT_MAX): the result is 0 (OpenSSL's input limit: its counters are unsigned int);
//  - otherwise the result is 1 exactly when the reference decoder (puny_ref.h pr_decode: RFC 3492 6.2 with the
//    overflow detection of 6.4 for 32-bit integers, and the output bound of the RFC's sample interface) succeeds
//    into cap code points, else 0; failure covers a non-basic code point before the last delimiter, a missing
//    digit or one with no digit-value, any overflow of 2^32 - 1, and an output of more than cap code points;
//  - on success *pout_length is the number of code points; on failure it is cap, unchanged;
//  - the array holds exactly what the reference leaves in its own copy of the initial array: on success the code
//    points, in order, then the initial values; on failure the output so far (the basic code points copied
//    before a non-basic one, or the insertions made before the failing step) and the initial values; so nothing
//    at or past index cap is ever written (CVE-2022-3602 was a 4-octet write past the end of this array);
//  - the input is unchanged.
#include "common.h"

int main(void)
{
	size_t len = nondet_size();
	unsigned char *enc = malloc(len);
	unsigned char *snap = malloc(len);
	if ((enc == NULL || snap == NULL) && len != 0)
		return 0;
	if (len != 0)          // enc may be NULL when len is 0 (malloc(0)): nothing to fill
		nondet_bytes(enc, len);
	copy_bytes(snap, enc, len);
	unsigned int cap;
	pick(cap);
	size_t bytes = (size_t) cap * sizeof(unsigned int);
	unsigned int *out = malloc(bytes);
	unsigned int *want = malloc(bytes);
	if ((out == NULL || want == NULL) && cap != 0)
		return 0;
	size_t j;
	for (j = 0; j < cap; j++) {
		pick(out[j]);
		want[j] = out[j];
	}
	unsigned int olen = cap;

	int r = ossl_punycode_decode((const char *) enc, len, out, &olen);

	if (len >= 4294967295u) {
		gp_assert(r == 0);
		gp_assert(olen == cap);
	} else {
		struct pr_dec d;
		pr_decode(snap, len, want, cap, &d);
		if (d.ok) {
			gp_assert(r == 1);
			gp_assert(olen == d.count);
		} else {
			gp_assert(r == 0);
			gp_assert(olen == cap);
		}
	}
	gp_assert(same_uints(out, want, cap));
	gp_assert(same_bytes(enc, snap, len));
	return 0;
}
