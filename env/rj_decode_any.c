/* env/rj_decode_any.c: the draws of harness/rj_decode_any.c (env/short.h): the input (a Punycode-ish string), the
   capacity aimed at the boundaries, random initial contents. */
#include "env/short.h"
static void env_setup(void)
{
	size_t n = q_puny();
	q_size(n);
	q_u32(env_cap(env_str[0], n));
}
