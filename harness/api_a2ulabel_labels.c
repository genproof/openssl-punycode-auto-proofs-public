// Law api_a2ulabel_labels: The labels of a name are converted one by one. For any two strings s1 and s2 (any octets
// up to their NUL, any lengths the allocator provides) and any outlen1, outlen2 >= 1, with objects of exactly those
// sizes holding any values: if ossl_a2ulabel returns 1 for s1 into outlen1 octets and 1 for s2 into outlen2 octets, it
// returns 1 for s1 '.' s2 into outlen1 + outlen2 octets and writes the output of s1, a '.', and the output of s2 with
// its NUL; if it returns -1 for s1 or for s2, it returns -1 for s1 '.' s2 (when the allocation of its WPACKET record
// fails in none of the three calls).
#include "laws_common.h"

int main(void) {
	// Choose the inputs: any two strings, the name s1 '.' s2, any outlen1 and outlen2 >= 1 and as many octets
	size_t len1 = upto(PTRDIFF_MAX - 2), len2 = upto(PTRDIFF_MAX - 2 - len1);
	unsigned char *s1 = any_bytes(len1 + 1), *s2 = any_bytes(len2 + 1), *name = malloc(len1 + len2 + 2);
	size_t outlen1 = upto(PTRDIFF_MAX), outlen2 = upto(PTRDIFF_MAX - outlen1);
	unsigned char *out1 = any_bytes(outlen1), *out2 = any_bytes(outlen2), *out = any_bytes(outlen1 + outlen2);
	if (s1 == NULL || s2 == NULL || name == NULL || out1 == NULL || out2 == NULL || out == NULL)
		return 0;
	if (outlen1 == 0 || outlen2 == 0)
		return 0;
	s1[len1] = 0;
	s2[len2] = 0;
	size_t n1 = 0, n2 = 0;                              // the strings' lengths
	for (; s1[n1] != 0; n1++)
		name[n1] = s1[n1];
	name[n1] = '.';
	for (; s2[n2] != 0; n2++)
		name[n1 + 1 + n2] = s2[n2];
	name[n1 + 1 + n2] = 0;
	ossl_shim_zalloc_failed = 0;
	int r1 = ossl_a2ulabel((const char *) s1, (char *) out1, outlen1);
	int r2 = ossl_a2ulabel((const char *) s2, (char *) out2, outlen2);
	int r = ossl_a2ulabel((const char *) name, (char *) out, outlen1 + outlen2);
	if (ossl_shim_zalloc_failed)
		return 0;
	// Check. crypto/punycode.c: "Domain name has some parts consisting of ASCII chars joined with dot."
	if (r1 == -1 || r2 == -1)
		gp_assert(r == -1);
	if (r1 == 1 && r2 == 1) {
		size_t u1 = 0, u2 = 0;                          // the lengths of the two outputs
		while (u1 < outlen1 && out1[u1] != 0)
			u1++;
		while (u2 < outlen2 && out2[u2] != 0)
			u2++;
		gp_assert(r == 1 && bytes_eq(out, out1, u1) && out[u1] == '.' && bytes_eq(out + u1 + 1, out2, u2 + 1));
	}
	return 0;
}
