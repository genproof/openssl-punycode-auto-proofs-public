// Law rfc_basic_first: The octets before the last delimiter are the basic code points of the output, in order (RFC
// 3492 3.1). For any input (any octets, any length the allocator provides) and any capacity (any unsigned int), with
// an array of exactly that many elements holding any values: if an octet before the last '-' is not basic (0x80 or
// more), ossl_punycode_decode returns 0; when it returns 1, the code points of the output below 0x80, in order, are
// exactly the octets before the last '-' (none when there is no '-'), and all its other code points are inserted
// ones (0x80 or more: the decoder's n starts at initial_n = 0x80 and only grows).
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets, any capacity, any initial contents of the array
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *input = any_bytes(len);
	unsigned int cap = nondet_u32();
	unsigned int *out = any_uints(cap);
	if (input == NULL || out == NULL)
		return 0;
	size_t literal = last_delimiter(input, len);       // the number of octets before the last '-'
	unsigned int count = cap;
	int r = ossl_punycode_decode((const char *) input, len, out, &count);
	// Check. RFC 3492 6.2: "consume all code points before the last delimiter (if there is one) and copy them to
	// output, fail on any non-basic code point"
	for (size_t i = 0; i < literal; i++)
		if (input[i] >= 0x80)
			gp_assert(r == 0);
	// Check. RFC 3492 3.1: "All basic code points appearing in the extended string are represented literally at the
	// beginning of the basic string, in their original order, followed by a delimiter if (and only if) the number of
	// basic code points is nonzero."
	if (r == 1) {
		size_t next = 0;                            // the literal octets seen so far
		for (unsigned int j = 0; j < count; j++)
			if (out[j] < 0x80) {
				gp_assert(next < literal && out[j] == input[next]);
				next++;
			}
		gp_assert(next == literal);
	}
	return 0;
}
