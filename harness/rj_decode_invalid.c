// Law rj_decode_invalid: ossl_punycode_decode fails where RFC 3492 6.2 says to fail on an octet. For any input (any
// octets, any length the allocator provides) and any capacity (any unsigned int), with an array of exactly that many
// elements holding any values: it returns 0, with *pout_length unchanged, when an octet before the last '-' is not
// basic (0x80 or more), or when an octet of the deltas (after the last '-'; all octets when there is no '-' or it is
// the first one) is neither a letter nor a digit, the octets that have a digit-value (RFC 3492 5).
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any octets, any capacity, any initial contents of the array
	size_t len = upto(PTRDIFF_MAX);
	unsigned char *input = any_bytes(len);
	unsigned int cap = nondet_u32();
	unsigned int *out = any_uints(cap);
	if (input == NULL || out == NULL)
		return 0;
	// RFC 3492 6.2: "consume all code points before the last delimiter (if there is one) and copy them to output,
	// fail on any non-basic code point; if more than zero code points were consumed then consume one more (which will
	// be the last delimiter)", then for the deltas: "let digit = the code point's digit-value, fail if it has none"
	size_t literal = last_delimiter(input, len);
	size_t deltas = literal > 0 ? literal + 1 : 0;      // where the deltas start
	int invalid = 0;
	for (size_t i = 0; i < len; i++) {
		unsigned char c = input[i];
		int digit = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9');
		if ((i < literal && c >= 0x80) || (i >= deltas && !digit))
			invalid = 1;
	}
	unsigned int count = cap;
	int r = ossl_punycode_decode((const char *) input, len, out, &count);
	// Check
	if (invalid)
		gp_assert(r == 0 && count == cap);
	return 0;
}
