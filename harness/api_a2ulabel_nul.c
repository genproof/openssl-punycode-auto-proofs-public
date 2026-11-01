// Law api_a2ulabel_nul: When ossl_a2ulabel succeeds, its output is a string within the buffer: "The output buffer is
// NUL-terminated." For any string (any octets up to its NUL, any length the allocator provides) and any outlen, with
// an object of exactly outlen octets holding any values: when the result is 1, the buffer holds a NUL, and every octet
// after the first NUL keeps its value. (With 0, "the output buffer is too small", it may hold none: a write that
// does not fit is skipped, and the NUL is the last write.)
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any string, any outlen and outlen octets
	size_t len = upto(PTRDIFF_MAX - 1);
	unsigned char *in = any_bytes(len + 1);
	size_t outlen = nondet_size();
	unsigned char *out = any_bytes(outlen);
	unsigned char *saved = copy_of(out, outlen);
	if (in == NULL || out == NULL || saved == NULL)
		return 0;
	in[len] = 0;
	int r = ossl_a2ulabel((const char *) in, (char *) out, outlen);
	// Check. ossl_punycode_decode.pod: "ossl_a2ulabel() decodes NUL-terminated hostname from PUNYCODE to UTF-8, using
	// a provided buffer for output. The output buffer is NUL-terminated."
	if (r == 1) {
		size_t end = 0;                                 // the first NUL
		while (end < outlen && out[end] != 0)
			end++;
		gp_assert(end < outlen && bytes_eq(out + end + 1, saved + end + 1, outlen - end - 1));
	}
	return 0;
}
