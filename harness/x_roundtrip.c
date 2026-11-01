// Law roundtrip: OpenSSL's decoders invert the RFC 3492 encoder.  For ANY sequence of m <= 512 Unicode code points
// (each at most 0x10FFFF: basic ones, the surrogates and the noncharacters included) whose encoding by the
// reference encoder (puny_ref.h pr_encode: RFC 3492 6.3, no case flags, lowercase digits) succeeds into a buffer
// of 16 m + 1 octets (natively it did for every sequence drawn):
//  - ossl_punycode_decode on the encoding, with an output array of exactly m unsigned ints, returns 1, sets
//    *pout_length to m and gives back the code points, in order;
//  - when no code point is '.' or NUL (so the encoding is one label), ossl_a2ulabel on "xn--" followed by the
//    encoding, with an output buffer of exactly the size of the UTF-8 form (RFC 3629) of the code points plus
//    its NUL, returns 1 and writes exactly that UTF-8 form and the NUL, unless the allocation of its sub-packet
//    record failed (then -1).
// OpenSSL's half of the IDNA identity ToUnicode(ToASCII(label)) = label, for labels of up to 512 code points (the
// Punycode form of an all-ASCII sequence included, which IDNA's ToASCII would not produce).
#include "common.h"

int main(void)
{
	size_t m = nondet_size();
	gp_assume(m <= PR_LABEL_CAP);
	unsigned int *cps = malloc(m * sizeof(unsigned int));
	if (cps == NULL && m != 0)
		return 0;
	size_t j;
	int one_label = 1;
	size_t ulen = 1;                // the UTF-8 form and its NUL
	for (j = 0; j < m; j++) {
		pick(cps[j]);
		gp_assume(cps[j] <= 1114111);
		if (cps[j] == 46 || cps[j] == 0)
			one_label = 0;
		if (cps[j] < 128)
			ulen = ulen + 1;
		else if (cps[j] < 2048)
			ulen = ulen + 2;
		else if (cps[j] < 65536)
			ulen = ulen + 3;
		else
			ulen = ulen + 4;
	}
	size_t ecap = 16 * m + 1;
	unsigned char *lab = malloc(4 + ecap + 1);      // "xn--", the encoding, a NUL
	if (lab == NULL)
		return 0;
	size_t elen;
	if (!pr_encode(cps, m, lab + 4, ecap, &elen))
		return 0;
	unsigned char *enc = malloc(elen);              // the encoding alone, in a buffer of its size
	unsigned int *out = malloc(m * sizeof(unsigned int));
	if ((enc == NULL && elen != 0) || (out == NULL && m != 0))
		return 0;
	copy_bytes(enc, lab + 4, elen);
	unsigned int olen = (unsigned int) m;

	int r = ossl_punycode_decode((const char *) enc, elen, out, &olen);

	gp_assert(r == 1);
	gp_assert(olen == m);
	gp_assert(same_uints(out, cps, m));

	if (one_label) {
		lab[0] = 120;                           // "xn--"
		lab[1] = 110;
		lab[2] = 45;
		lab[3] = 45;
		lab[4 + elen] = 0;
		unsigned char *u = malloc(ulen);
		unsigned char *want = malloc(ulen);
		if (u == NULL || want == NULL)
			return 0;
		size_t at = 0;
		for (j = 0; j < m; j++)
			at = at + pr_utf8(cps[j], want + at);
		want[at] = 0;
		ossl_shim_fail_next = 0;
		ossl_shim_zalloc_failed = 0;
		ossl_shim_live = 0;

		int r2 = ossl_a2ulabel((const char *) lab, (char *) u, ulen);

		if (ossl_shim_zalloc_failed == 0) {
			gp_assert(r2 == 1);
			gp_assert(same_bytes(u, want, ulen));
		} else {
			gp_assert(r2 == -1);
		}
		gp_assert(ossl_shim_live == 0);
	}
	return 0;
}
