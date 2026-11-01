// Law api_a2ulabel_copy: A name with no label that starts with the ACE prefix is copied as it is. For any string (any
// octets up to its NUL, any length the allocator provides) none of whose labels (the parts between '.') starts with
// "xn--" in any case, and any outlen >= 1, with an object of exactly outlen octets holding any values: when outlen is
// more than the string's length, ossl_a2ulabel returns 1, writes the string and its NUL, and leaves the later octets
// unchanged; else it returns 0. (When the allocation of its WPACKET record fails, it returns -1.)
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any string, any outlen >= 1 and any outlen octets
	size_t len = upto(PTRDIFF_MAX - 1);
	unsigned char *in = any_bytes(len + 1);
	size_t outlen = upto(PTRDIFF_MAX);
	unsigned char *out = any_bytes(outlen);
	unsigned char *saved = copy_of(out, outlen);
	if (in == NULL || out == NULL || saved == NULL || outlen == 0)
		return 0;
	in[len] = 0;
	size_t n = 0;                                       // the string's length
	while (in[n] != 0)
		n++;
	for (size_t i = 0; i + 3 < n; i++)                  // no label starts with x, n, -, - in any case
		if (i == 0 || in[i - 1] == '.')
			gp_assume(!((in[i] == 'x' || in[i] == 'X') && (in[i + 1] == 'n' || in[i + 1] == 'N') &&
			            in[i + 2] == '-' && in[i + 3] == '-'));
	ossl_shim_zalloc_failed = 0;
	int r = ossl_a2ulabel((const char *) in, (char *) out, outlen);
	// Check. crypto/punycode.c: "Domain name has some parts consisting of ASCII chars joined with dot. ... If it does
	// not start with xn--, it becomes U-label as is."
	if (ossl_shim_zalloc_failed)
		gp_assert(r == -1);
	else if (outlen > n)
		gp_assert(r == 1 && bytes_eq(out, in, n + 1) && bytes_eq(out + n + 1, saved + n + 1, outlen - n - 1));
	else
		gp_assert(r == 0);
	return 0;
}
