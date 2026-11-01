// Law a2ulabel: ossl_a2ulabel is the documented A-label to U-label conversion, exactly, and never writes outside
// its buffer.  For ANY string in (any octets up to its NUL, of any length) and ANY outlen (any size_t), with out
// either NULL or a buffer of exactly outlen octets holding any values, and with the allocation of the WPACKET's
// sub-packet record (CRYPTO_zalloc) succeeding or failing: no undefined behaviour, and
//  - out == NULL, outlen == 0, or the allocation failed: the result is -1 and nothing is written (the documented
//    "another error"; ossl_assert is a plain test in a release build);
//  - otherwise the result and the output are those of the reference conversion (puny_ref.h pr_a2ulabel): the
//    labels of in (split at every '.'), each label that starts with the ACE prefix "xn--" in any case (RFC 5890
//    2.3.1: "case independent"; false upstream, which tests the lowercase prefix only,
//    fixed by patch D1) decoded by the RFC 3492 reference into at most 512 code points and
//    written in UTF-8 (RFC 3629; surrogates as three octets), every other label copied, the labels joined by
//    '.', then a NUL; result -1 at the first label that does not decode or the first code point above 0x10FFFF
//    (the output so far stays, no NUL), else 0 ("the output buffer is too small") when some write did not fit,
//    else 1;
//  - the output is OpenSSL's static WPACKET's: octets [0, written) are the writes that fitted, in order (a write
//    that does not fit in the room left is skipped whole, and later writes that fit are still done), and every
//    other octet of the buffer keeps its value: nothing is written at or past out + outlen (CVE-2022-3786 and
//    CVE-2022-3602 were overruns of this buffer in the caller nc_email_eai);
//  - the input is unchanged, and the sub-packet record is released (no CRYPTO_zalloc block is left).
#include "common.h"

int main(void)
{
	size_t n = nondet_size();
	gp_assume(n < (size_t) -1);
	unsigned char *in = malloc(n + 1);
	unsigned char *snap = malloc(n + 1);
	unsigned int *cps = malloc(PR_LABEL_CAP * sizeof(unsigned int));
	if (in == NULL || snap == NULL || cps == NULL)
		return 0;
	nondet_bytes(in, n);
	in[n] = 0;
	copy_bytes(snap, in, n + 1);
	size_t sl = 0;                  // the string: the octets before the first NUL
	while (snap[sl] != 0)
		sl++;
	size_t outlen = nondet_size();
	uint8_t mode = nondet_u8();     // bit 0: pass out = NULL; bit 1: the allocation fails
	unsigned char *out = NULL;
	unsigned char *want = NULL;
	if ((mode & 1) == 0) {
		out = malloc(outlen);
		want = malloc(outlen);
		if (out == NULL || want == NULL)
			return 0;
		nondet_bytes(out, outlen);
		copy_bytes(want, out, outlen);
	}
	ossl_shim_fail_next = (mode & 2) != 0;
	ossl_shim_zalloc_failed = 0;
	ossl_shim_live = 0;

	int r = ossl_a2ulabel((const char *) in, (char *) out, outlen);

	if (out == NULL || outlen == 0 || ossl_shim_zalloc_failed != 0) {
		gp_assert(r == -1);
	} else {
		struct pr_sink k;
		k.buf = want;
		k.cap = outlen;
		k.len = 0;
		k.short_ = 0;
		gp_assert(r == pr_a2ulabel(snap, sl, &k, cps));
	}
	if (out != NULL)
		gp_assert(same_bytes(out, want, outlen));
	gp_assert(same_bytes(in, snap, n + 1));
	gp_assert(ossl_shim_live == 0);
	return 0;
}
