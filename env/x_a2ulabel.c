// Value distributions of law a2ulabel (env/a2ulabel.c; untrusted, steers native and interpreter runs only).  Draws
// in the harness's order: nondet_size = the string length (env/gen.h eg_host: labels joined by '.', each "xn--" + a
// Punycode-ish string, "XN--"/"Xn--" + one, "xn--" alone, "xn-", plain LDH labels, octets >= 0x80, empty labels;
// sometimes a NUL inside, which ends the string); its nondet_bytes gets it; the second nondet_size is outlen,
// aimed at the boundaries (eg_outlen: the size the reference conversion needs with its NUL, one less, one more,
// 0..2, less than the first label, any); nondet_u8 is the mode (rarely out = NULL, rarely a failing allocation);
// the output buffer's nondet_bytes is random.
#include "env/gen.h"

#define ENV_ROOM (EG_SMALL ? 1500 : 12000)
static unsigned char env_s[ENV_ROOM];
static size_t env_n;
static int env_step;
static unsigned int env_cps[PR_LABEL_CAP];
static unsigned char env_out[4 * ENV_ROOM + 64];

size_t nondet_size(void)
{
	if (env_step == 0) {
		env_n = eg_host(env_s, ENV_ROOM);
		env_step = 1;
		return env_n;
	}
	env_step = 3;
	return eg_outlen(env_s, env_n, env_out, sizeof env_out, env_cps);
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	size_t j;
	if (env_step == 1 && n == env_n) {
		for (j = 0; j < n; j++)
			buf[j] = env_s[j];
		env_step = 2;
		return;
	}
	for (j = 0; j < n; j++)
		buf[j] = (uint8_t) quickproof_rnd();
}

uint8_t nondet_u8(void)
{
	uint8_t m = 0;
	if (eg_r(30) == 0)
		m |= 1;
	if (eg_r(30) == 0)
		m |= 2;
	return m;
}

uint32_t nondet_u32(void)
{
	return (uint32_t) quickproof_rnd();
}
