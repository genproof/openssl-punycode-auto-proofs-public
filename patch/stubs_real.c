/* patch/stubs_real.c: for patch/difftest.sh's build R only (upstream's whole crypto/packet.c with OpenSSL's real
 * headers).  packet.c's QUIC functions call these two encoders of include/internal/quic_vlint.h; ossl_a2ulabel
 * never reaches them.  Trapping definitions, so that the build links; reaching one is a failure. */
#include <stdint.h>
#include <stdlib.h>

void ossl_quic_vlint_encode_n(uint8_t *buf, uint64_t v, int n)
{
    (void)buf; (void)v; (void)n;
    abort();
}

void ossl_quic_vlint_encode(uint8_t *buf, uint64_t v)
{
    (void)buf; (void)v;
    abort();
}
