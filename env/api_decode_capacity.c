/* env/api_decode_capacity.c: the draws of harness/api_decode_capacity.c (env/short.h): the input (a Punycode-ish
   string, mostly valid), the capacity aimed at the boundaries, random initial contents. */
#include "env/short.h"
static void env_setup(void)
{
	size_t n = q_puny();
	q_size(n);
	q_u32(env_cap(env_str[0], n));
}
