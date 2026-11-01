// Law rfc_ace_any_case: ossl_a2ulabel recognizes the ACE prefix in any case. RFC 3490 5: "The ToASCII and ToUnicode
// operations MUST recognize the ACE prefix in a case-insensitive manner. The ACE prefix for IDNA is "xn--" or any
// capitalization thereof." For any capitalization P of "xn--", any string s (any octets up to its NUL, any length the
// allocator provides) and any outlen, with two objects of exactly outlen octets holding the same arbitrary values:
// ossl_a2ulabel of P followed by s returns what it returns for "xn--" followed by s, and leaves the same octets in its
// buffer (when the allocation of its WPACKET record fails in neither call or in both). False on unpatched OpenSSL,
// which recognizes "xn--" only, fixed by patch D1.
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any capitalization of "xn--", any string after it, any outlen and outlen octets
	size_t len = upto(PTRDIFF_MAX - 5);
	unsigned char *any_case = any_bytes(len + 5);       // P, s, NUL
	size_t outlen = nondet_size();
	unsigned char *out1 = any_bytes(outlen);
	unsigned char *out2 = copy_of(out1, outlen);
	if (any_case == NULL || out1 == NULL || out2 == NULL)
		return 0;
	any_case[0] = nondet_u8() == 0 ? 'X' : 'x';
	any_case[1] = nondet_u8() == 0 ? 'N' : 'n';
	any_case[2] = '-';
	any_case[3] = '-';
	any_case[len + 4] = 0;
	unsigned char *lower = copy_of(any_case, len + 5);  // "xn--", s, NUL
	if (lower == NULL)
		return 0;
	lower[0] = 'x';
	lower[1] = 'n';
	ossl_shim_zalloc_failed = 0;
	int r1 = ossl_a2ulabel((const char *) any_case, (char *) out1, outlen);
	int failed1 = ossl_shim_zalloc_failed;
	ossl_shim_zalloc_failed = 0;
	int r2 = ossl_a2ulabel((const char *) lower, (char *) out2, outlen);
	if (failed1 != ossl_shim_zalloc_failed)
		return 0;
	// Check
	gp_assert(r1 == r2 && bytes_eq(out1, out2, outlen));
	return 0;
}
