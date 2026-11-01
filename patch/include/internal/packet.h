/*
 * openssl-punycode: header shim for OpenSSL's include/internal/packet.h (NOT upstream's file).
 *
 * Only the WPACKET part that crypto/punycode.c and patch/units/packet_ext.c use, copied from openssl-3.6.5:
 * struct buf_mem_st (include/openssl/buffer.h) and BUF_MEM (include/openssl/types.h), struct wpacket_sub and
 * struct wpacket_st, the prototypes of the WPACKET functions under test and the macro WPACKET_put_bytes_u8, all
 * verbatim (patch/extract.py --check compares them) except ONE change:
 *   - `unsigned int endfirst : 1;` is a plain `unsigned int endfirst;` (VST 2.15 has no bit-fields).  The WPACKET
 *     code stores only 0 and 1 in it (`pkt->endfirst = 0;` / `= 1;`) and only tests it for zero, so every stored
 *     value fits the bit-field and every read gives the value stored; the field is read and written by name, so
 *     the layout change is not observable (patch/difftest.sh also checks it against the real header).
 * BUF_MEM_grow is declared for WPACKET_reserve_bytes's growable-buffer path, which a static WPACKET (the only kind
 * ossl_a2ulabel makes) never takes; patch/shim/ossl_shim.c defines it as a trap.  patch/PATCH.md.
 */
#ifndef OSSL_SHIM_INTERNAL_PACKET_H
#define OSSL_SHIM_INTERNAL_PACKET_H

#include <string.h>
#include <openssl/e_os2.h>

struct buf_mem_st {
    size_t length; /* current number of bytes */
    char *data;
    size_t max; /* size of buffer */
    unsigned long flags;
};
typedef struct buf_mem_st BUF_MEM;

size_t BUF_MEM_grow(BUF_MEM *str, size_t len);

typedef struct wpacket_sub WPACKET_SUB;
struct wpacket_sub {
    /* The parent WPACKET_SUB if we have one or NULL otherwise */
    WPACKET_SUB *parent;

    /*
     * Offset into the buffer where the length of this WPACKET goes. We use an
     * offset in case the buffer grows and gets reallocated.
     */
    size_t packet_len;

    /* Number of bytes in the packet_len or 0 if we don't write the length */
    size_t lenbytes;

    /* Number of bytes written to the buf prior to this packet starting */
    size_t pwritten;

    /* Flags for this sub-packet */
    unsigned int flags;
};

typedef struct wpacket_st WPACKET;
struct wpacket_st {
    /* The buffer where we store the output data */
    BUF_MEM *buf;

    /* Fixed sized buffer which can be used as an alternative to buf */
    unsigned char *staticbuf;

    /*
     * Offset into the buffer where we are currently writing. We use an offset
     * in case the buffer grows and gets reallocated.
     */
    size_t curr;

    /* Number of bytes written so far */
    size_t written;

    /* Maximum number of bytes we will allow to be written to this WPACKET */
    size_t maxsize;

    /* Our sub-packets (always at least one if not finished) */
    WPACKET_SUB *subs;

    /* Writing from the end first? */
    unsigned int endfirst; /* quickproof: unsigned int endfirst : 1; (VST has no bit-fields) */
};

int WPACKET_init_static_len(WPACKET *pkt, unsigned char *buf, size_t len,
    size_t lenbytes);

int WPACKET_allocate_bytes(WPACKET *pkt, size_t len,
    unsigned char **allocbytes);

int WPACKET_reserve_bytes(WPACKET *pkt, size_t len, unsigned char **allocbytes);

int WPACKET_put_bytes__(WPACKET *pkt, uint64_t val, size_t bytes);

#define WPACKET_put_bytes_u8(pkt, val) \
    WPACKET_put_bytes__((pkt), (val), 1)

int WPACKET_memcpy(WPACKET *pkt, const void *src, size_t len);

unsigned char *WPACKET_get_curr(WPACKET *pkt);

void WPACKET_cleanup(WPACKET *pkt);

#endif
