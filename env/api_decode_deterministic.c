/* env/api_decode_deterministic.c: the draws of harness/api_decode_deterministic.c (env/short.h): the input (a
   Punycode-ish string) and a few more octets after it (digits, '-', anything), the capacity aimed at the
   boundaries, random initial contents. */
#include "env/short.h"
static void env_setup(void)
{
	size_t n = q_puny(), more = eg_r(4) == 0 ? 0 : 1 + eg_r(12), j;
	q_size(n);
	q_size(more);
	for (j = 0; j < more; j++)
		env_str[0][n + j] = eg_r(3) == 0 ? '-' : (unsigned char) eg_alnum[eg_r(sizeof eg_alnum - 1)];
	env_len[0] = n + more;
	q_u32(env_cap(env_str[0], n));
}
