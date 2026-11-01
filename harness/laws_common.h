// laws_common.h: trivial helpers shared by the short laws (each law includes it once). No models, no algorithms.
#include <stdint.h>
#include <stdlib.h>
#include "quickproof.h"
#include "crypto/punycode.h"                         // ossl_punycode_decode, ossl_a2ulabel
// OpenSSL's allocator in this build (patch/shim/ossl_shim.c): set to 1 when CRYPTO_zalloc fails (malloc may fail at
// any call in the theorems), and the number of its blocks not freed yet.
extern int ossl_shim_zalloc_failed;
extern long ossl_shim_live;
static size_t upto(size_t max) {                     // any value from 0 to max
	size_t value = nondet_size();
	return value < max ? value : max;
}
static unsigned char *any_bytes(size_t n) {          // a new object of n arbitrary bytes (NULL if malloc fails)
	unsigned char *bytes = malloc(n);
	if (bytes != NULL)
		nondet_bytes(bytes, n);
	return bytes;
}
static unsigned int *any_uints(size_t n) {           // a new array of n arbitrary unsigned ints (NULL if malloc fails)
	unsigned int *values = malloc(n * sizeof(unsigned int));
	for (size_t i = 0; values != NULL && i < n; i++)
		values[i] = nondet_u32();
	return values;
}
static unsigned char *copy_of(const unsigned char *source, size_t n) {   // a new object holding source[0..n-1]
	if (source == NULL)                                                   // (NULL if source is or malloc fails)
		return NULL;
	unsigned char *copy = malloc(n);
	for (size_t i = 0; copy != NULL && i < n; i++)
		copy[i] = source[i];
	return copy;
}
static int bytes_eq(const unsigned char *a, const unsigned char *b, size_t n) {   // a[0..n-1] == b[0..n-1]
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static int uints_eq(const unsigned int *a, const unsigned int *b, size_t n) {     // a[0..n-1] == b[0..n-1]
	for (size_t i = 0; i < n; i++)
		if (a[i] != b[i])
			return 0;
	return 1;
}
static size_t last_delimiter(const unsigned char *s, size_t n) {   // the position of the last '-', 0 if none
	size_t last = 0;
	for (size_t i = 0; i < n; i++)
		if (s[i] == '-')
			last = i;
	return last;
}
