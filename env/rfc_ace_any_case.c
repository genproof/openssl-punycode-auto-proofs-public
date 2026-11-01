/* env/rfc_ace_any_case.c: the draws of harness/rfc_ace_any_case.c (env/short.h): s = a Punycode-ish string, sometimes
   followed by more labels (env/gen.h eg_host), queued after four placeholder octets for the prefix; outlen aimed at
   the boundaries of the conversion of "xn--" s; each case choice 0 or 1 with probability 1/2. */
#include "env/short.h"
static void env_setup(void)
{
	env_alloc_failure();
	unsigned char *p = q_str(ENV_ROOM + 5);
	size_t n = eg_puny(p + 4, ENV_ROOM / 2), j;
	for (j = 0; j < n; j++)
		if (p[4 + j] == 0 || p[4 + j] == '.')
			p[4 + j] = 'a';
	if (eg_r(4) == 0) {
		p[4 + n] = '.';
		n += 1 + eg_host(p + 5 + n, ENV_ROOM / 2 - 8);
	}
	p[0] = 'x';
	p[1] = 'n';
	p[2] = '-';
	p[3] = '-';
	env_len[0] = n + 4;
	q_size(n);
	q_size(env_outlen(p, n + 4));
	q_u8((uint8_t) eg_r(2));
	q_u8((uint8_t) eg_r(2));
}
