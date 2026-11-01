// Law rj_decode_any: For any input octets of any length the allocator provides (NUL and octets >= 0x80 included) and
// any capacity cap (any unsigned int), with an output array of exactly cap elements holding any values,
// ossl_punycode_decode returns one of the two results its documentation gives: 1 with *pout_length at most cap, or
// 0 with *pout_length unchanged; it reads and writes nothing outside the input and the array, and leaves the input
// unchanged.
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets, any capacity, any initial contents of the array
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *input = any_bytes(len);
	unsigned char *saved = copy_of(input, len);
	unsigned int cap = nondet_u32();
	unsigned int *out = any_uints(cap);
	if (input == NULL || saved == NULL || out == NULL)
		return 0;
	unsigned int count = cap;
	int r = ossl_punycode_decode((const char *) input, len, out, &count);
	// Check. ossl_punycode_decode.pod: "ossl_punycode_decode() returns 1 on success, 0 on error. On success,
	// *pout_length contains the number of codepoints decoded."
	gp_assert(r == 1 || r == 0);
	gp_assert(r == 1 ? count <= cap : count == cap);
	gp_assert(bytes_eq(input, saved, len));
	return 0;
}
