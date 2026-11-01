// Law rj_a2ulabel_any: For any string (any octets up to its NUL, any length the allocator provides) and any outlen
// (any size_t), with out NULL or an object of exactly outlen octets holding any values, ossl_a2ulabel returns one of
// the results its documentation gives, and -1 when out is NULL or outlen is 0; it reads and writes nothing outside
// the string and out[0..outlen), leaves the string unchanged and frees every block it allocates. (CVE-2022-3786 was
// an overflow of this buffer by the '.' written between labels.)
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any string, any outlen, out NULL or any outlen octets
	size_t len = upto(PTRDIFF_MAX - 1);
	unsigned char *in = any_bytes(len + 1);
	if (in == NULL)
		return 0;
	in[len] = 0;
	unsigned char *saved = copy_of(in, len + 1);
	size_t outlen = nondet_size();
	unsigned char *out = nondet_u8() == 0 ? NULL : any_bytes(outlen);
	if (saved == NULL)
		return 0;
	int r = ossl_a2ulabel((const char *) in, (char *) out, outlen);
	// Check. ossl_punycode_decode.pod: "ossl_a2ulabel() returns 1 on success, 0 if the output buffer is too small and
	// -1 if an invalid PUNYCODE string is passed or another error occurs."
	gp_assert(r == 1 || r == 0 || r == -1);
	if (out == NULL || outlen == 0)
		gp_assert(r == -1);
	gp_assert(bytes_eq(in, saved, len + 1));
	gp_assert(ossl_shim_live == 0);
	return 0;
}
