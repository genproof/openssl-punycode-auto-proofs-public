/* env/rfc_digit_case.c: the draws of harness/rfc_digit_case.c (env/short.h): the input (a Punycode-ish string), the
   capacity aimed at the boundaries, random initial contents; each letter of the deltas changes case with
   probability 1/2 (nondet_u8() == 0). */
#include "env/short.h"
static void env_setup(void)
{
	size_t n = q_puny(), j;
	q_size(n);
	q_u32(env_cap(env_str[0], n));
	for (j = 0; j < n && j < ENV_QU; j++)
		q_u8((uint8_t) eg_r(2));
}
