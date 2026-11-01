/*
 * openssl-punycode: the rest of the program, in plain C (NOT upstream code).
 *
 * A unit of quickproof.conf (src/shim): it is verified together with crypto/punycode.c and patch/units/packet_ext.c,
 * so nothing here is trusted (the only externals left are malloc/free and the harness environment of quickproof.h).
 * The same file is linked in native and interpreter runs.  patch/PATCH.md, section "The shim unit".
 *
 *   CRYPTO_zalloc   OpenSSL's default allocator (crypto/mem.c: CRYPTO_zalloc = CRYPTO_malloc + memset; CRYPTO_malloc
 *                   returns NULL for 0 octets, else malloc's result; the allocation hooks are not installed and the
 *                   failure report (ossl_report_alloc_err) is left out: it only pushes an error-stack entry), plus
 *                   the knob and counters below.
 *   CRYPTO_free     crypto/mem.c: free(), plus the counter below.  free(NULL) is a no-op, so the NULL test changes
 *                   nothing.
 *   strlen, strchr, strncmp   the C library's, in plain C (ossl_a2ulabel; HAS_PREFIX is strncmp).
 *   OPENSSL_strncasecmp       OpenSSL's (crypto/o_str.c, with ossl_tolower of crypto/ctype.c for an ASCII platform:
 *                   'A'..'Z' to 'a'..'z', everything else unchanged), for HAS_CASE_PREFIX in the patched
 *                   ossl_a2ulabel (deviation D1).
 *   BUF_MEM_grow    crypto/buffer/buffer.c is not under test: WPACKET_reserve_bytes calls it only for a WPACKET
 *                   over a growable BUF_MEM, and the only WPACKET here (ossl_a2ulabel's) is static.  This trapping
 *                   definition only lets the units link; reaching it is a failure (a null store: SIGSEGV
 *                   natively, undefined behaviour in the theorems, so a proof shows the path is never taken).
 *
 * Test knob and counters (globals the harnesses read and write; in the theorems malloc may fail at every call
 * anyway, so the knob adds no behaviour that a proof does not already cover):
 *   ossl_shim_fail_next      nonzero: the next CRYPTO_zalloc fails (returns NULL without calling malloc) and the
 *                            knob goes back to 0.  Native malloc never fails; this is how native and interpreter
 *                            runs reach the allocation-failure path of WPACKET_init_static_len;
 *   ossl_shim_zalloc_failed  set to 1 whenever CRYPTO_zalloc returns NULL (a law resets it before the call it
 *                            watches): the law can then state the documented outcome (-1);
 *   ossl_shim_live           blocks returned by CRYPTO_zalloc and not yet passed to CRYPTO_free: a law checks that
 *                            ossl_a2ulabel releases what it allocates (WPACKET_cleanup).
 */
#include <stddef.h>
#include <string.h>
#include "internal/packet.h"

extern void *malloc(size_t n);
extern void free(void *p);

int ossl_shim_fail_next;
int ossl_shim_zalloc_failed;
long ossl_shim_live;

void *CRYPTO_zalloc(size_t num, const char *file, int line)
{
    void *ret;

    (void)file;
    (void)line;
    if (num == 0) {
        ossl_shim_zalloc_failed = 1;
        return NULL;
    }
    if (ossl_shim_fail_next != 0) {
        ossl_shim_fail_next = 0;
        ret = NULL;
    } else {
        ret = malloc(num);
    }
    if (ret == NULL) {
        ossl_shim_zalloc_failed = 1;
        return NULL;
    }
    memset(ret, 0, num);
    ossl_shim_live++;
    return ret;
}

void CRYPTO_free(void *str, const char *file, int line)
{
    (void)file;
    (void)line;
    if (str != NULL) {
        ossl_shim_live--;
        free(str);
    }
}

size_t strlen(const char *s)
{
    size_t n = 0;

    while (s[n] != '\0')
        n++;
    return n;
}

char *strchr(const char *s, int c)
{
    size_t i = 0;
    char ch = (char)c;

    for (;;) {
        if (s[i] == ch)
            return (char *)(s + i);
        if (s[i] == '\0')
            return NULL;
        i++;
    }
}

int strncmp(const char *s1, const char *s2, size_t n)
{
    size_t i;
    unsigned char c1, c2;

    for (i = 0; i != n; i++) {
        c1 = (unsigned char)s1[i];
        c2 = (unsigned char)s2[i];
        if (c1 != c2)
            return c1 < c2 ? -1 : 1;
        if (c1 == 0)
            return 0;
    }
    return 0;
}

/* crypto/ctype.c ossl_tolower on an ASCII platform (ossl_toascii is the identity there). */
static int shim_tolower(int c)
{
    return (c >= 'A' && c <= 'Z') ? c ^ 0x20 : c;
}

/* crypto/o_str.c, with the assignment taken out of the condition. */
int OPENSSL_strncasecmp(const char *s1, const char *s2, size_t n)
{
    int t;
    size_t i;

    for (i = 0; i < n; i++) {
        t = shim_tolower(s1[i]) - shim_tolower(s2[i]);
        if (t != 0)
            return t;
        if (s1[i] == '\0')
            return 0;
    }
    return 0;
}

size_t BUF_MEM_grow(BUF_MEM *str, size_t len)
{
    volatile int *p = NULL; /* not part of the code under test: reaching it is a failure */

    (void)str;
    (void)len;
    *p = 0;
    return 0;
}
