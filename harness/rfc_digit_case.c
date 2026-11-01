// Law rfc_digit_case: The decoder reads the digits of the deltas in either case. For any input (any octets, any
// length the allocator provides) and any capacity (any unsigned int), the input with any of the letters of its deltas
// (after the last '-'; all octets when there is no '-' or it is the first one) changed to the other case decodes to
// the same result, length and code points (each into an array of exactly that capacity holding any values). The
// octets before the last '-' are code points, not digits: they keep their case.
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets, the same with any letters of the deltas in the other case, any capacity
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *input = any_bytes(len);
	unsigned char *other = copy_of(input, len);
	unsigned int cap = nondet_u32();
	unsigned int *out1 = any_uints(cap);
	unsigned int *out2 = any_uints(cap);
	if (input == NULL || other == NULL || out1 == NULL || out2 == NULL)
		return 0;
	size_t literal = last_delimiter(input, len);
	for (size_t i = literal > 0 ? literal + 1 : 0; i < len; i++)
		if (nondet_u8() == 0) {
			if (other[i] >= 'a' && other[i] <= 'z')
				other[i] = other[i] - 32;
			else if (other[i] >= 'A' && other[i] <= 'Z')
				other[i] = other[i] + 32;
		}
	unsigned int count1 = cap, count2 = cap;
	int r1 = ossl_punycode_decode((const char *) input, len, out1, &count1);
	int r2 = ossl_punycode_decode((const char *) other, len, out2, &count2);
	// Check. RFC 3492 5: "A decoder MUST recognize the letters in both uppercase and lowercase forms (including
	// mixtures of both forms)."
	gp_assert(r1 == r2 && count1 == count2);
	if (r1 == 1)
		gp_assert(uints_eq(out1, out2, count1));
	return 0;
}
