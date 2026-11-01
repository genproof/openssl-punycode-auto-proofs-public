// Law api_decode_deterministic: ossl_punycode_decode depends only on the enc_len octets it is given. For any input
// (any octets, any length the allocator provides) followed by any number of other octets, decoded once there and once
// from a copy of exactly enc_len octets, into two arrays of the same capacity (any unsigned int) holding any values
// each: both calls return the same result and report the same length, and on success the same code points.
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets followed by any others, a copy of the input alone, any capacity and contents
	size_t len = upto(PTRDIFF_MAX);
	size_t more = upto(PTRDIFF_MAX - len);
	unsigned char *first = any_bytes(len + more);
	unsigned char *second = copy_of(first, len);
	unsigned int cap = nondet_u32();
	unsigned int *out1 = any_uints(cap);
	unsigned int *out2 = any_uints(cap);
	if (first == NULL || second == NULL || out1 == NULL || out2 == NULL)
		return 0;
	unsigned int count1 = cap, count2 = cap;
	int r1 = ossl_punycode_decode((const char *) first, len, out1, &count1);
	int r2 = ossl_punycode_decode((const char *) second, len, out2, &count2);
	// Check
	gp_assert(r1 == r2 && count1 == count2);
	if (r1 == 1)
		gp_assert(uints_eq(out1, out2, count1));
	return 0;
}
