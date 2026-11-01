// Shared by the openssl-punycode laws: the prototypes of the code under test (include/crypto/punycode.h), the
// shim's test knob and counters (patch/shim/ossl_shim.c), the reference model (puny_ref.h) and small helpers.
//
// A harness draws every input from quickproof.h (nondet_*, pick), restricts it with gp_assume, and states each
// property with gp_assert (undefined behaviour when it fails).  Buffers have exactly the size the claim allows
// (no slack octet or element: a slack one would hide an overrun by one).
#ifndef OSSL_PUNYCODE_HARNESS_COMMON_H
#define OSSL_PUNYCODE_HARNESS_COMMON_H
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "puny_ref.h"

// The code under test (include/crypto/punycode.h of openssl-3.6.5).
int ossl_punycode_decode(const char *pEncoded, const size_t enc_len, unsigned int *pDecoded, unsigned int *pout_length);
int ossl_a2ulabel(const char *in, char *out, size_t outlen);

// patch/shim/ossl_shim.c: nonzero makes the next CRYPTO_zalloc fail; set to 1 when CRYPTO_zalloc returns NULL; the
// blocks CRYPTO_zalloc returned and CRYPTO_free did not release yet.
extern int ossl_shim_fail_next;
extern int ossl_shim_zalloc_failed;
extern long ossl_shim_live;

static void copy_bytes(unsigned char *d, const unsigned char *s, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		d[i] = s[i];
}

static int same_bytes(const unsigned char *a, const unsigned char *b, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}

static int same_uints(const unsigned int *a, const unsigned int *b, size_t n)
{
	size_t i;
	for (i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}

#endif
