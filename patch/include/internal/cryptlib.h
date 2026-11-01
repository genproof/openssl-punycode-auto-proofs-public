/*
 * openssl-punycode: header shim for OpenSSL's include/internal/cryptlib.h (NOT upstream's file), as
 * included by patch/units/packet_ext.c (the verbatim WPACKET functions of crypto/packet.c).
 *
 * Those functions need the allocation macros OPENSSL_zalloc and OPENSSL_free (include/openssl/crypto.h.in, verbatim)
 * and SIZE_MAX.  OPENSSL_FILE and OPENSSL_LINE are those of a build configured with no-filenames (OpenSSL's
 * include/openssl/macros.h: `#define OPENSSL_FILE ""` and `#define OPENSSL_LINE 0` under OPENSSL_NO_FILENAMES): the
 * allocator's file and line arguments only feed its debugging hooks and error messages.  CRYPTO_zalloc and
 * CRYPTO_free are patch/shim/ossl_shim.c's (OpenSSL's default allocator, crypto/mem.c, in plain C).
 * patch/PATCH.md, "The header shim".
 */
#ifndef OSSL_SHIM_INTERNAL_CRYPTLIB_H
#define OSSL_SHIM_INTERNAL_CRYPTLIB_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include "internal/common.h"

#define OPENSSL_FILE ""
#define OPENSSL_LINE 0

void *CRYPTO_zalloc(size_t num, const char *file, int line);
void CRYPTO_free(void *ptr, const char *file, int line);

#define OPENSSL_zalloc(num) \
    CRYPTO_zalloc(num, OPENSSL_FILE, OPENSSL_LINE)
#define OPENSSL_free(addr) \
    CRYPTO_free(addr, OPENSSL_FILE, OPENSSL_LINE)

#endif
