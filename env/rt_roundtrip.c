/* env/rt_roundtrip.c: the draws of harness/rt_roundtrip.c (env/short.h): m code points (env/gen.h eg_cps, any 32-bit
   values sometimes; mostly short, sometimes long; sometimes the shapes that reach the bound: k code points 0x80 and
   one more of about 0x80 + 2^32 / (k + 1)), the room for the encoding (what the reference encoder needs, one less,
   more, small), random initial contents of the output array. */
#include "env/short.h"
static unsigned int env_cp[ENV_QU / 2];
static void env_setup(void)
{
	size_t k = eg_r(10), m, j, need = 0, room;
	if (k < 5)
		m = eg_r(12);
	else if (k < 7)
		m = eg_r(EG_SMALL ? 100 : 2000);
	else
		m = 1 + eg_r(EG_SMALL ? 40 : 6000);
	if (m > ENV_QU / 2)
		m = ENV_QU / 2;
	eg_cps(env_cp, m, eg_r(3) == 0);
	if (k >= 8 && m >= 2) {                     // near the bound (largest - 127) * m = 2^32
		for (j = 0; j + 1 < m; j++)
			env_cp[j] = 0x80;
		unsigned long long big = 0x80 + (4294967296ull / m) + eg_r(5) - 2;
		env_cp[m - 1] = big > 0xFFFFFFFFu ? 0xFFFFFFFFu : (unsigned int) big;
	}
	if (k == 9 && eg_r(2)) {                     // the counterexamples of the unbounded claim
		m = (eg_r(2) || EG_SMALL) ? 3 : 4369;
		for (j = 0; j + 1 < m; j++)
			env_cp[j] = 0x80;
		env_cp[m - 1] = m == 3 ? 0x80 + 1431655765u : 0x80 + 983055;
	}
	static unsigned char enc[16 * (ENV_QU / 2) + 64];
	if (!pr_encode(env_cp, m, enc, sizeof enc, &need))
		need = sizeof enc;
	k = eg_r(8);
	room = k < 5 ? need : k == 5 ? (need > 0 ? need - 1 : 0) : k == 6 ? need + eg_r(100) : eg_r(need + 2);
	q_size(m);
	q_size(room);
	for (j = 0; j < m; j++)
		q_u32(env_cp[j]);
}
