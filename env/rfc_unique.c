/* env/rfc_unique.c: the draws of harness/rfc_unique.c (env/short.h): input1 a Punycode-ish string; input2 mostly the
   reference encoding of what input1 decodes to (puny_ref.h pr_encode: the canonical form), sometimes with letters
   of the deltas in the other case, sometimes mutated (one octet); a large capacity mostly, random contents. */
#include "env/short.h"
static unsigned int env_dec[ENV_ROOM + 1];
static void env_setup(void)
{
	size_t n1 = q_puny(), n2 = 0, j, k = eg_r(6);
	struct pr_dec d;
	q_size(n1);
	unsigned char *s2 = q_str(ENV_ROOM);
	pr_decode(env_str[0], n1, env_dec, ENV_ROOM, &d);
	if (d.ok && k < 5) {
		if (!pr_encode(env_dec, d.count, s2, ENV_ROOM, &n2))
			n2 = 0;
		if (k >= 2)
			for (j = 0; j < n2; j++)
				if (((s2[j] | 32) >= 'a' && (s2[j] | 32) <= 'z') && eg_r(2))
					s2[j] ^= 32;
		if (k == 4)
			n2 = eg_mutate(s2, n2, ENV_ROOM);
	} else {
		n2 = eg_puny(s2, ENV_ROOM);
	}
	env_len[1] = n2;
	q_size(n2);
	q_u32(eg_r(4) == 0 ? env_cap(env_str[0], n1) : (uint32_t) (d.ok ? d.count + eg_r(3) : eg_r(40)));
}
