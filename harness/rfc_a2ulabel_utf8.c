// Law rfc_a2ulabel_utf8: A label with the ACE prefix becomes the UTF-8 form of its Punycode decoding. For any octets s
// without '.' and NUL (any length the allocator provides), decoded by ossl_punycode_decode into at most 512 code
// points (ossl_a2ulabel's label buffer, LABEL_BUF_SIZE), and any outlen >= 1, with an object of exactly outlen octets
// holding any values: ossl_a2ulabel of "xn--" followed by s returns -1 when that decoding fails or gives a code point
// above 0x10FFFF; else it returns 1, writes the UTF-8 form of the code points (RFC 3629, which excludes the surrogates
// U+D800..U+DFFF: they get three octets like their neighbours) and a NUL, and leaves the later octets unchanged when
// they fit in outlen octets, and returns 0 when they do not (when the allocation of its WPACKET record succeeds).
#include "laws_common.h"

static size_t utf8(unsigned int c, unsigned char *o) {   // RFC 3629 3: the octets of a code point c <= 0x10FFFF
	if (c < 0x80) {
		o[0] = c;
		return 1;
	}
	if (c < 0x800) {
		o[0] = 0xC0 | c >> 6;
		o[1] = 0x80 | (c & 0x3F);
		return 2;
	}
	if (c < 0x10000) {
		o[0] = 0xE0 | c >> 12;
		o[1] = 0x80 | (c >> 6 & 0x3F);
		o[2] = 0x80 | (c & 0x3F);
		return 3;
	}
	o[0] = 0xF0 | c >> 18;
	o[1] = 0x80 | (c >> 12 & 0x3F);
	o[2] = 0x80 | (c >> 6 & 0x3F);
	o[3] = 0x80 | (c & 0x3F);
	return 4;
}

int main(void) {
	// Choose the inputs: "xn--" and any octets but '.' and NUL, any outlen >= 1 and outlen octets
	size_t len = upto(PTRDIFF_MAX - 5);
	unsigned char *label = any_bytes(len + 5);          // "xn--", s, NUL
	unsigned int *cps = malloc(512 * sizeof(unsigned int));
	size_t outlen = upto(PTRDIFF_MAX);
	unsigned char *out = any_bytes(outlen), *saved = copy_of(out, outlen), *want = malloc(4 * 512 + 1);
	if (label == NULL || cps == NULL || out == NULL || saved == NULL || want == NULL || outlen == 0)
		return 0;
	label[0] = 'x';
	label[1] = 'n';
	label[2] = '-';
	label[3] = '-';
	label[len + 4] = 0;
	for (size_t i = 4; i < len + 4; i++)
		gp_assume(label[i] != '.' && label[i] != 0);
	// The decoding of s, and its UTF-8 form with a NUL in want[0..size)
	unsigned int count = 512;
	int valid = ossl_punycode_decode((const char *) label + 4, len, cps, &count) == 1;
	size_t size = 0;
	for (unsigned int j = 0; valid && j < count; j++)
		if (cps[j] > 0x10FFFF)
			valid = 0;
		else
			size = size + utf8(cps[j], want + size);
	want[size] = 0;
	size++;
	ossl_shim_zalloc_failed = 0;
	int r = ossl_a2ulabel((const char *) label, (char *) out, outlen);
	// Check. crypto/punycode.c: "If it does not start with xn--, it becomes U-label as is. Otherwise we try to decode it."
	if (ossl_shim_zalloc_failed)
		gp_assert(r == -1);
	else if (!valid)
		gp_assert(r == -1);
	else if (size <= outlen)
		gp_assert(r == 1 && bytes_eq(out, want, size) && bytes_eq(out + size, saved + size, outlen - size));
	else
		gp_assert(r == 0);
	return 0;
}
