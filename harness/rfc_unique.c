// Law rfc_unique: One sequence of code points has one Punycode form, up to the case of its digits. RFC 3492 6.2:
// "there is only one encoded string that can represent a given sequence of integers. ... If the decoder fails on
// these errors as shown above, then it cannot produce the same output for two distinct inputs." For any two inputs
// (any octets, any lengths the allocator provides) and any capacity (any unsigned int), each decoded into an array of
// exactly that many elements holding any values: when ossl_punycode_decode returns 1 for both, with the same code
// points, the inputs are the same octets, except that a letter of the deltas (after the last '-'; all octets when
// there is no '-') may be in the other case (rfc_digit_case).
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any two octet strings, any capacity, any initial contents of the arrays
	size_t len1 = upto(PTRDIFF_MAX);
	unsigned char *input1 = any_bytes(len1);
	size_t len2 = upto(PTRDIFF_MAX);
	unsigned char *input2 = any_bytes(len2);
	unsigned int cap = nondet_u32();
	unsigned int *out1 = any_uints(cap);
	unsigned int *out2 = any_uints(cap);
	if (input1 == NULL || input2 == NULL || out1 == NULL || out2 == NULL)
		return 0;
	unsigned int count1 = cap, count2 = cap;
	int r1 = ossl_punycode_decode((const char *) input1, len1, out1, &count1);
	int r2 = ossl_punycode_decode((const char *) input2, len2, out2, &count2);
	if (r1 != 1 || r2 != 1 || count1 != count2 || !uints_eq(out1, out2, count1))
		return 0;
	// Check: the same octets, but for the case of letters among the deltas
	gp_assert(len1 == len2);
	size_t literal = last_delimiter(input1, len1);
	for (size_t i = 0; i < len1; i++)
		if (input1[i] != input2[i]) {
			unsigned char lower = input1[i] | 32;   // the letter in lowercase, if input1[i] is a letter
			gp_assert(i > literal || literal == 0);
			gp_assert(lower >= 'a' && lower <= 'z' && (input2[i] | 32) == lower);
		}
	return 0;
}
