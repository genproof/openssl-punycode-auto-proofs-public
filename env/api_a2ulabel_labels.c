/* env/api_a2ulabel_labels.c: the draws of harness/api_a2ulabel_labels.c (env/short.h): two host names (env/gen.h
   eg_host), and for each an output size: mostly what the reference conversion needs, sometimes aimed at the
   boundaries; random initial contents. */
#include "env/short.h"
static size_t env_size_for(const unsigned char *s, size_t n)
{
	size_t need = env_need(s, n);
	return need > 0 && eg_r(3) ? need + eg_r(3) : env_outlen(s, n);
}
static void env_setup(void)
{
	env_alloc_failure();
	size_t n1 = q_host(), n2 = q_host();
	q_size(n1);
	q_size(n2);
	q_size(env_size_for(env_str[0], n1));
	q_size(env_size_for(env_str[1], n2));
}
