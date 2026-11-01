/*
 * openssl-punycode: header shim for OpenSSL's include/openssl/e_os2.h (NOT upstream's file).
 *
 * crypto/punycode.c needs only `ossl_inline` from it.  The definition is upstream's for a C99 compiler
 * (include/openssl/e_os2.h: `#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L` -> `inline`), which is
 * what gcc and CompCert's clightgen are.  patch/PATCH.md, "The header shim".
 */
#ifndef OSSL_SHIM_OPENSSL_E_OS2_H
#define OSSL_SHIM_OPENSSL_E_OS2_H

#include <stddef.h>
#include <stdint.h>

#define ossl_inline inline

#endif
