/* env/rfc_a2ulabel_utf8.c: the draws of harness/rfc_a2ulabel_utf8.c (env/short.h): s = a Punycode-ish string with
   no '.' or NUL (env/gen.h eg_puny), queued after four placeholder octets for "xn--"; outlen aimed at the boundaries
   of the conversion of "xn--" s; random initial contents. */
#include "env/short.h"
static void env_setup(void)
{
	env_alloc_failure();
	unsigned char *p = q_str(ENV_ROOM + 5);
	size_t n = eg_puny(p + 4, ENV_ROOM), j;
	for (j = 0; j < n; j++)
		if (p[4 + j] == 0 || p[4 + j] == '.')
			p[4 + j] = 'b';
	p[0] = 'x';
	p[1] = 'n';
	p[2] = '-';
	p[3] = '-';
	env_len[0] = n + 4;
	q_size(n);
	q_size(env_outlen(p, n + 4));
}
