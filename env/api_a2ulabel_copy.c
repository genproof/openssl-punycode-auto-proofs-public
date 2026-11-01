/* env/api_a2ulabel_copy.c: the draws of harness/api_a2ulabel_copy.c (env/short.h): a host name none of whose labels
   starts with "xn--" in any case (env/gen.h eg_host, with such prefixes broken: "xn--" -> "xn-x"), sometimes with a NUL
   inside; outlen the string's length plus 1, the length, plus 2, 1..3, or anything up to twice it. */
#include "env/short.h"
static void env_setup(void)
{
	env_alloc_failure();
	size_t n = q_host(), j, sl = 0, k = eg_r(8);
	unsigned char *s = env_str[0];
	for (j = 0; j + 3 < n; j++)
		if ((j == 0 || s[j - 1] == '.') && (s[j] | 32) == 'x' && (s[j + 1] | 32) == 'n' && s[j + 2] == '-' &&
		    s[j + 3] == '-')
			s[j + 3] = (unsigned char) (eg_r(2) ? 'x' : 0xC3);
	while (sl < n && s[sl] != 0)
		sl++;
	q_size(n);
	q_size(k < 3 ? sl + 1 : k == 3 ? sl : k == 4 ? sl + 2 : k == 5 ? 1 + eg_r(3) : eg_r(2 * sl + 2));
}
