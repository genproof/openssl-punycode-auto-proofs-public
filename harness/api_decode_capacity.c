// Law api_decode_capacity: The output never goes past the capacity, and the length reported is exact. For any input
// (any octets, any length the allocator provides) and any capacity cap (any unsigned int), with an array of exactly
// cap elements holding any values: when ossl_punycode_decode returns 1 with *pout_length = count, the elements from
// count on keep their values; decoding the same input again into an array of exactly count elements returns 1 with
// the same count and code points, and into count - 1 elements (count > 0) returns 0. (CVE-2022-3602 was a write of
// one element past the end of this array when the code points did not fit.)
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets, any capacity, any initial contents of the array (and a copy of them)
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *input = any_bytes(len);
	unsigned int cap = nondet_u32();
	unsigned int *out = any_uints(cap);
	unsigned int *saved = malloc((size_t) cap * sizeof(unsigned int));
	if (input == NULL || out == NULL || saved == NULL)
		return 0;
	for (unsigned int i = 0; i < cap; i++)
		saved[i] = out[i];
	unsigned int count = cap;
	if (ossl_punycode_decode((const char *) input, len, out, &count) != 1)
		return 0;
	// Check: nothing written from count on
	gp_assert(count <= cap && uints_eq(out + count, saved + count, cap - count));
	// Check: count elements are enough...
	unsigned int *exact = any_uints(count);
	unsigned int exact_count = count;
	if (exact == NULL)
		return 0;
	gp_assert(ossl_punycode_decode((const char *) input, len, exact, &exact_count) == 1);
	gp_assert(exact_count == count && uints_eq(exact, out, count));
	// ... and needed: one element fewer is too few
	if (count > 0) {
		unsigned int *fewer = any_uints(count - 1);
		unsigned int fewer_count = count - 1;
		if (fewer == NULL)
			return 0;
		gp_assert(ossl_punycode_decode((const char *) input, len, fewer, &fewer_count) == 0);
		gp_assert(fewer_count == count - 1);
	}
	return 0;
}
