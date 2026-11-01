/*
 * openssl-punycode: header shim for OpenSSL's include/internal/common.h (NOT upstream's file).
 *
 * crypto/punycode.c and the WPACKET functions need ossl_likely, ossl_assert and HAS_PREFIX, and the patched
 * crypto/punycode.c HAS_CASE_PREFIX (deviation D1).  Their definitions below are copied
 * verbatim from include/internal/common.h of openssl-3.6.5 (patch/extract.py --check compares them), in the
 * configuration of a release build: NDEBUG is defined (OpenSSL's Configure adds -DNDEBUG unless --debug), so
 * ossl_assert(x) is ossl_likely((x) != 0), a test that never aborts.  The headers upstream's file includes for
 * these files' needs: <stdlib.h>, <string.h> (strchr, strlen, strncmp, memcpy, memset), <limits.h>
 * (UINT_MAX; upstream gets it through internal/e_os.h), and openssl/e_os2.h (ossl_inline); and the prototype of
 * OPENSSL_strncasecmp (include/openssl/crypto.h.in, verbatim; patch/shim/ossl_shim.c defines it).
 * patch/PATCH.md, "The header shim".
 */
#ifndef OSSL_SHIM_INTERNAL_COMMON_H
#define OSSL_SHIM_INTERNAL_COMMON_H

#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <openssl/e_os2.h>

#ifndef NDEBUG
#error "the verified configuration is a release build (-DNDEBUG): ossl_assert never aborts"
#endif

#if defined(__GNUC__) || defined(__clang__)
#define ossl_likely(x) __builtin_expect(!!(x), 1)
#define ossl_unlikely(x) __builtin_expect(!!(x), 0)
#else
#define ossl_likely(x) (x)
#define ossl_unlikely(x) (x)
#endif

#ifdef NDEBUG
#define ossl_assert(x) ossl_likely((x) != 0)
#endif

int OPENSSL_strncasecmp(const char *s1, const char *s2, size_t n);

/* Check if |pre|, which must be a string literal, is a prefix of |str| */
#define HAS_PREFIX(str, pre) (strncmp(str, pre "", sizeof(pre) - 1) == 0)
/* Check if the string literal |p| is a case-insensitive prefix of |s| */
#define HAS_CASE_PREFIX(s, p) (OPENSSL_strncasecmp(s, p "", sizeof(p) - 1) == 0)

#endif
