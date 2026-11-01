// Value distributions of law roundtrip (env/roundtrip.c; untrusted, steers native and interpreter runs only).
// nondet_size = m (mostly small, sometimes up to 512, sometimes exactly 512); then each 4-octet nondet_bytes is a
// code point of a sequence the env drew at once (env/gen.h: basic, 2-, 3-, 4-octet, surrogates, edges, '.' and NUL
// sometimes; shapes: all equal, alternating, descending, large deltas), always at most 0x10FFFF (the harness assumes
// it; a failing assume would only stall the interpreter).
#include "env/gen.h"

static unsigned int env_cps[PR_LABEL_CAP];
static size_t env_m, env_i;

size_t nondet_size(void)
{
	size_t k = eg_r(10), j;
	env_m = k < 6 ? eg_r(12) : k < 8 ? eg_r(EG_SMALL ? 100 : PR_LABEL_CAP + 1) : k == 8 ? PR_LABEL_CAP : eg_r(3);
	eg_cps(env_cps, env_m, 0);
	for (j = 0; j < env_m; j++) {
		if (env_cps[j] > 0x10FFFF)
			env_cps[j] = 0x10FFFF;
		if (eg_r(200) == 0)
			env_cps[j] = eg_r(2) ? '.' : 0;
	}
	env_i = 0;
	return env_m;
}

void nondet_bytes(uint8_t *buf, size_t n)
{
	size_t j;
	if (n == 4 && env_i < env_m) {
		eg_put32(buf, env_cps[env_i++]);
		return;
	}
	for (j = 0; j < n; j++)
		buf[j] = (uint8_t) quickproof_rnd();
}

uint8_t nondet_u8(void)
{
	return (uint8_t) quickproof_rnd();
}

uint32_t nondet_u32(void)
{
	return (uint32_t) quickproof_rnd();
}
