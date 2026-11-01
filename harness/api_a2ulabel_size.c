// Law api_a2ulabel_size: The result 0 says exactly that the output does not fit. For any string (any octets up to its
// NUL, any length the allocator provides) that ossl_a2ulabel converts (result 1) into some object of any size, writing
// size octets up to and with the first NUL: into an object of any other outlen >= 1 octets holding any values, it
// returns 1 and writes the same size octets when outlen >= size, and 0 when outlen < size (when the allocation of its
// WPACKET record fails in neither call).
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any string, a first buffer of any size, a second one of any outlen >= 1
	size_t len = upto(PTRDIFF_MAX - 1);
	unsigned char *in = any_bytes(len + 1);
	size_t biglen = nondet_size();
	unsigned char *big = any_bytes(biglen);
	size_t outlen = nondet_size();
	unsigned char *out = any_bytes(outlen);
	if (in == NULL || big == NULL || out == NULL || outlen == 0)
		return 0;
	in[len] = 0;
	ossl_shim_zalloc_failed = 0;
	int r1 = ossl_a2ulabel((const char *) in, (char *) big, biglen);
	int r = ossl_a2ulabel((const char *) in, (char *) out, outlen);
	if (ossl_shim_zalloc_failed || r1 != 1)
		return 0;
	size_t size = 0;                                    // the octets written, up to and with the first NUL
	while (size < biglen && big[size] != 0)
		size++;
	size++;
	// Check. ossl_punycode_decode.pod: "ossl_a2ulabel() returns 1 on success, 0 if the output buffer is too small"
	if (outlen >= size)
		gp_assert(r == 1 && bytes_eq(out, big, size));
	else
		gp_assert(r == 0);
	return 0;
}
