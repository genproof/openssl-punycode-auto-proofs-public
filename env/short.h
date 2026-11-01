// Value distributions of the short laws (env/<law>.c; untrusted: they only steer native and interpreter runs, the
// theorems quantify over every value).  Each env file defines env_setup(), which queues the values of one run in the
// order the harness draws them: sizes (nondet_size), byte strings (nondet_bytes: the next queued string, cut or
// padded with random octets to the length asked), 32-bit values (nondet_u32) and 8-bit values (nondet_u8).  A draw
// past its queue is random (small sizes).  The generators of env/gen.h build Punycode-ish strings, host names and
// output sizes aimed at the boundaries, with the reference of harness/puny_ref.h.
#ifndef OSSL_PUNYCODE_ENV_SHORT_H
#define OSSL_PUNYCODE_ENV_SHORT_H
#include "gen.h"

#define ENV_ROOM (EG_SMALL ? 1500 : 12000)
#define ENV_Q 8
#define ENV_QU (EG_SMALL ? 2000 : 70000)

static void env_setup(void);
static int env_ready;
static size_t env_sz[ENV_Q], env_nsz, env_isz;
static unsigned char env_str[ENV_Q][4 * ENV_ROOM + 64];
static size_t env_len[ENV_Q], env_nstr, env_istr;
static uint32_t env_u32[ENV_QU];
static size_t env_nu32, env_iu32;
static uint8_t env_u8[ENV_QU];
static size_t env_nu8, env_iu8;

static void env_init(void)
{
	if (!env_ready) {
		env_ready = 1;
		env_setup();
	}
}
static void q_size(size_t v) { if (env_nsz < ENV_Q) env_sz[env_nsz++] = v; }
static unsigned char *q_str(size_t n)    // queue a string of n octets (filled by the caller); returns it
{
	if (env_nstr >= ENV_Q)
		return env_str[ENV_Q - 1];
	if (n > sizeof env_str[0])
		n = sizeof env_str[0];
	env_len[env_nstr] = n;
	return env_str[env_nstr++];
}
static void q_u32(uint32_t v) { if (env_nu32 < ENV_QU) env_u32[env_nu32++] = v; }
static void q_u8(uint8_t v) { if (env_nu8 < ENV_QU) env_u8[env_nu8++] = v; }
// Sometimes (1 in 16) the next CRYPTO_zalloc fails (patch/shim/ossl_shim.c's knob): natively malloc never fails, and
// the laws state what ossl_a2ulabel does when its allocation fails.
extern int ossl_shim_fail_next;
static void env_alloc_failure(void) { ossl_shim_fail_next = eg_r(16) == 0; }

size_t nondet_size(void)
{
	env_init();
	return env_isz < env_nsz ? env_sz[env_isz++] : eg_r(64);
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	size_t j = 0;
	env_init();
	if (env_istr < env_nstr) {
		for (; j < n && j < env_len[env_istr]; j++)
			buf[j] = env_str[env_istr][j];
		env_istr++;
	}
	for (; j < n; j++)
		buf[j] = (uint8_t) quickproof_rnd();
}

uint32_t nondet_u32(void)
{
	env_init();
	return env_iu32 < env_nu32 ? env_u32[env_iu32++] : (uint32_t) quickproof_rnd();
}

uint8_t nondet_u8(void)
{
	env_init();
	return env_iu8 < env_nu8 ? env_u8[env_iu8++] : (uint8_t) quickproof_rnd();
}

// A Punycode-ish string (env/gen.h eg_puny) queued as the next string; its length.
static size_t q_puny(void)
{
	unsigned char *s = q_str(ENV_ROOM);
	size_t n = eg_puny(s, ENV_ROOM);
	env_len[env_nstr - 1] = n;
	return n;
}

// The capacity for decoding s[0..n), aimed at the boundaries (env/gen.h eg_cap).
static unsigned int env_scratch[ENV_ROOM + 1];
static uint32_t env_cap(const unsigned char *s, size_t n)
{
	return eg_cap(s, n, env_scratch, ENV_ROOM);
}

// A host name (env/gen.h eg_host) queued as the next string, with room for the harness's NUL; its length.
static size_t q_host(void)
{
	unsigned char *s = q_str(ENV_ROOM + 1);
	size_t n = eg_host(s, ENV_ROOM);
	env_len[env_nstr - 1] = n;
	return n;
}

// The output size for ossl_a2ulabel on s[0..n) aimed at the boundaries (env/gen.h eg_outlen).
static unsigned char env_out[4 * ENV_ROOM + 64];
static unsigned int env_cps[PR_LABEL_CAP];
static size_t env_outlen(const unsigned char *s, size_t n)
{
	return eg_outlen(s, n, env_out, sizeof env_out, env_cps);
}

// What the reference conversion needs for s[0..n) (its output with the NUL), or 0 when it fails.
static size_t env_need(const unsigned char *s, size_t n)
{
	struct pr_sink k;
	size_t sl = 0;
	while (sl < n && s[sl] != 0)
		sl++;
	k.buf = env_out;
	k.cap = sizeof env_out;
	k.len = 0;
	k.short_ = 0;
	return pr_a2ulabel(s, sl, &k, env_cps) == 1 ? k.len : 0;
}

#endif
