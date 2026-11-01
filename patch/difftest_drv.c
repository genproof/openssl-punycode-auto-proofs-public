/* patch/difftest_drv.c: differential test of the quickproof patch and of the header shim (patch/PATCH.md).
 *
 * Linked with ONE build of the code under test (patch/difftest.sh builds several: upstream with OpenSSL's real
 * headers, upstream with the shim, the patched code with the shim; under gcc -O2, gcc ASan/UBSan and ccomp) and
 * with patch/shim/ossl_shim.c (CRYPTO_zalloc/CRYPTO_free and the allocation-failure knob).
 *
 * Usage: difftest_drv SEED N.  Draws N calls from SEED with the project's own generators (env/gen.h): half
 * ossl_punycode_decode on Punycode-ish strings (valid encodings of random code point sequences, mutated ones,
 * overflow digit runs, basic code points and non-basic octets, known vectors, random octets) with output bounds
 * at the boundaries, the array pre-filled with a pattern; half ossl_a2ulabel on host names (labels joined by '.',
 * "xn--"/"XN--" labels, LDH labels, high octets, empty labels, a NUL inside) with output sizes at the boundaries,
 * the buffer pre-filled with a pattern, out = NULL and a failing allocation now and then.  It prints one line per
 * call (result, *pout_length, an FNV-1a hash of the WHOLE output array or buffer, the shim's counters) to stdout,
 * so two builds agree exactly when their outputs are identical, and a summary to stderr.  An ossl_a2ulabel call on
 * a string with a label whose ACE prefix is not in lowercase ("XN--", "Xn--", "xN--") is tagged "A 1" and followed
 * by the same call on the string with those prefixes in lowercase ("N"): deviation D1
 * must make the patched code's "A 1" equal the unmodified code's "N", and change nothing else
 * (patch/difftest.sh checks it). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#ifdef __COMPCERT__
#undef __COMPCERT__ /* env/gen.h: the full-size generators also in the ccomp build */
#endif
#include "env/gen.h"

int ossl_punycode_decode(const char *pEncoded, const size_t enc_len, unsigned int *pDecoded, unsigned int *pout_length);
int ossl_a2ulabel(const char *in, char *out, size_t outlen);
extern int ossl_shim_fail_next;
extern int ossl_shim_zalloc_failed;
extern long ossl_shim_live;

static uint64_t rs;
uint64_t quickproof_rnd(void)
{
	rs ^= rs >> 12;
	rs ^= rs << 25;
	rs ^= rs >> 27;
	return rs * 2685821657736338717ULL;
}

static uint64_t fnv(const unsigned char *p, size_t n)
{
	uint64_t h = 1469598103934665603ULL;
	size_t i;
	for (i = 0; i < n; i++) {
		h ^= p[i];
		h *= 1099511628211ULL;
	}
	return h;
}

#define ROOM 12000
static unsigned char s[ROOM + 1];
static unsigned int scratch[ROOM + 1];
static unsigned char outscratch[4 * ROOM + 64];
static unsigned int cps[PR_LABEL_CAP];
static unsigned char norm[ROOM + 1];

int main(int argc, char **argv)
{
	unsigned long seed = argc > 1 ? strtoul(argv[1], NULL, 10) : 1;
	long N = argc > 2 ? atol(argv[2]) : 10000, c;
	long dec[2] = { 0, 0 }, a2u[3] = { 0, 0, 0 }, live_bad = 0, flagged = 0;
	rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0x100000001B3ULL);
	if (rs == 0)
		rs = 1;
	for (c = 0; c < N; c++) {
		if (quickproof_rnd() % 2 == 0) {
			size_t n = eg_puny(s, ROOM), j;
			uint32_t cap = eg_cap(s, n, scratch, ROOM);
			unsigned int *out = NULL;
			if (cap != 0 || quickproof_rnd() % 2)
				out = malloc(cap != 0 ? (size_t) cap * sizeof(unsigned int) : 1);
			for (j = 0; j < cap; j++)
				out[j] = 0xA5A5A5A5u ^ (unsigned int) j;
			unsigned int olen = cap;
			char *in = malloc(n + 1);
			memcpy(in, s, n);
			int r = ossl_punycode_decode(in, n, out, &olen);
			printf("D %d %u %u %016llx\n", r, cap, olen,
			       (unsigned long long) (out ? fnv((unsigned char *) out, (size_t) cap * sizeof(unsigned int)) : 0));
			dec[r == 1]++;
			if (memcmp(in, s, n) != 0) {
				fprintf(stderr, "input changed\n");
				return 1;
			}
			free(in);
			free(out);
		} else {
			size_t n = eg_host(s, ROOM), j;
			s[n] = 0;
			size_t outlen = eg_outlen(s, n, outscratch, sizeof outscratch, cps);
			int null_out = quickproof_rnd() % 40 == 0;
			int fail = quickproof_rnd() % 40 == 0;
			/* norm: s with the ACE prefix of every label in lowercase ("XN--" -> "xn--"): deviation D1 makes
			   ossl_a2ulabel behave on s as the unmodified code does on norm (deviation D1) */
			memcpy(norm, s, n + 1);
			int flag = 0;
			for (j = 0; j + 3 < n; j++) {
				if ((j == 0 || s[j - 1] == '.') && (s[j] == 'x' || s[j] == 'X') && (s[j + 1] == 'n' || s[j + 1] == 'N')
				    && s[j + 2] == '-' && s[j + 3] == '-') {
					if (s[j] != 'x' || s[j + 1] != 'n')
						flag = 1;
					norm[j] = 'x';
					norm[j + 1] = 'n';
				}
			}
			int pass;
			for (pass = 0; pass < (flag ? 2 : 1); pass++) {
				const unsigned char *src = pass == 0 ? s : norm;
				unsigned char *out = NULL;
				if (!null_out) {
					out = malloc(outlen != 0 ? outlen : 1);
					memset(out, 0x5A, outlen);
				}
				ossl_shim_fail_next = fail;
				ossl_shim_zalloc_failed = 0;
				ossl_shim_live = 0;
				char *in = malloc(n + 1);
				memcpy(in, src, n + 1);
				int r = ossl_a2ulabel(in, (char *) out, outlen);
				printf("%s %d %zu %d %ld %016llx\n", pass == 0 ? (flag ? "A 1" : "A 0") : "N", r, outlen,
				       ossl_shim_zalloc_failed, ossl_shim_live, (unsigned long long) (out ? fnv(out, outlen) : 0));
				if (pass == 0)
					a2u[r + 1]++;
				if (ossl_shim_live != 0)
					live_bad++;
				if (memcmp(in, src, n + 1) != 0) {
					fprintf(stderr, "input changed\n");
					return 1;
				}
				free(in);
				free(out);
			}
			flagged += flag;
		}
	}
	fprintf(stderr, "%ld calls: decode ok/fail %ld/%ld, a2ulabel 1/0/-1 %ld/%ld/%ld (%ld with an ACE prefix not in "
	        "lowercase), leaked %ld\n", N, dec[1], dec[0], a2u[2], a2u[1], a2u[0], flagged, live_bad);
	return live_bad != 0;
}
