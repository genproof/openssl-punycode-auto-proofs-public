/* env/rj_a2ulabel_any.c: the draws of harness/rj_a2ulabel_any.c (env/short.h): a host name (env/gen.h eg_host), the
   output size aimed at the boundaries, out = NULL rarely, random initial contents. */
#include "env/short.h"
static void env_setup(void)
{
	env_alloc_failure();
	size_t n = q_host();
	q_size(n);
	q_size(env_outlen(env_str[0], n));
	q_u8(eg_r(30) == 0 ? 0 : 1);
}
