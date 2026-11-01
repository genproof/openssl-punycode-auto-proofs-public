// Value distributions of law decode (env/decode.c; untrusted, steers native and interpreter runs only).  Draws in
// the harness's order: nondet_size = the input length (the env builds a Punycode-ish string, env/gen.h eg_puny,
// and returns its length); the nondet_bytes of that length gets it; the first 4-octet nondet_bytes is cap, aimed
// at the boundaries (eg_cap: the number of code points the reference decodes, one less, one more, the number of
// basic code points, 0..2, any); later 4-octet draws (the output array's initial values) are random.
#include "env/gen.h"

#define ENV_ROOM (EG_SMALL ? 1200 : 8192)
static unsigned char env_s[ENV_ROOM];
static size_t env_n;
static int env_step;
static unsigned int env_scratch[ENV_ROOM + 1];

size_t nondet_size(void)
{
	env_n = eg_puny(env_s, ENV_ROOM);
	env_step = 1;
	return env_n;
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
	if (env_step == 2 && n == 4) {
		eg_put32(buf, eg_cap(env_s, env_n, env_scratch, ENV_ROOM));
		env_step = 3;
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
