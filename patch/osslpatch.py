#!/usr/bin/env python3
"""patch/osslpatch.py [--no-fix]: the quickproof patch of OpenSSL's crypto/punycode.c.  Run at the tree root by tools/qp
(project.conf PATCH).  patch/PATCH.md explains every edit; each changed line carries a `quickproof:`
comment that gives the original.

Idiom edits only (no behaviour change):
  I1  ossl_a2ulabel: the two `goto end` become `break` out of the label loop (the second one with a test after the
      inner loop of code points), and the final NUL is written only when no failure broke the loop (result != -1);
      VST has no rule for goto;
  I2  ossl_punycode_decode: the memmove that opens a slot in the unsigned int output array becomes a loop of typed
      element copies (backwards, the same values); VST would otherwise need a lemma relating the octet copies of
      the framework's memmove to the unsigned int cells of the array.
Deviation (--no-fix leaves it out; it fixes a bug):
  D1  ossl_a2ulabel: a label is an A-label when it starts with the ACE prefix "xn--" in any case (RFC 5890 2.3.1:
      'begin with the prefix "xn--" (case independent)'; RFC 3490 section 5): HAS_PREFIX becomes upstream's own
      HAS_CASE_PREFIX (OPENSSL_strncasecmp, crypto/o_str.c), so "XN--", "Xn--" and "xN--" labels are decoded too.
patch/units/packet_ext.c (the WPACKET functions of crypto/packet.c) is not edited.
"""
import re
import sys

PUNY = 'crypto/punycode.c'
FIX = '--no-fix' not in sys.argv[1:]


def replace(src, old, new, what):
    n = src.count(old)
    if n != 1:
        sys.exit('osslpatch.py: %s: expected 1 occurrence, found %d' % (what, n))
    return src.replace(old, new)


def main():
    s = open(PUNY).read()

    # I2: ossl_punycode_decode, the memmove of the unsigned int array
    s = replace(s, '''        memmove(pDecoded + i + 1, pDecoded + i,
            (written_out - i) * sizeof(*pDecoded));
''', '''        { /* quickproof: memmove(pDecoded + i + 1, pDecoded + i, (written_out - i) * sizeof(*pDecoded)); */
            unsigned int gp_j; /* quickproof: typed element copies, backwards (I2) */

            for (gp_j = written_out; gp_j > i; gp_j--) /* quickproof: (I2) */
                pDecoded[gp_j] = pDecoded[gp_j - 1]; /* quickproof: (I2) */
        } /* quickproof: (I2) */
''', 'I2 memmove')

    # I1: ossl_a2ulabel, the two `goto end`
    s = replace(s, '''            if (ossl_punycode_decode(inptr + 4, delta - 4, buf, &bufsize) <= 0) {
                result = -1;
                goto end;
            }
''', '''            if (ossl_punycode_decode(inptr + 4, delta - 4, buf, &bufsize) <= 0) {
                result = -1;
                break; /* quickproof: goto end; (I1) */
            }
''', 'I1 first goto')
    s = replace(s, '''                if (utfsize == 0) {
                    result = -1;
                    goto end;
                }

                if (!WPACKET_memcpy(&pkt, seed, utfsize))
                    result = 0;
            }
''', '''                if (utfsize == 0) {
                    result = -1;
                    break; /* quickproof: goto end; (I1, with the test after this loop) */
                }

                if (!WPACKET_memcpy(&pkt, seed, utfsize))
                    result = 0;
            }
            if (result == -1) /* quickproof: (I1) the goto end of the loop above */
                break; /* quickproof: (I1) */
''', 'I1 second goto')
    s = replace(s, '''    if (!WPACKET_put_bytes_u8(&pkt, '\\0'))
        result = 0;
end:
    WPACKET_cleanup(&pkt);
''', '''    if (result != -1 && !WPACKET_put_bytes_u8(&pkt, '\\0')) /* quickproof: if (!WPACKET_put_bytes_u8(&pkt, '\\0')) (I1) */
        result = 0;
    /* quickproof: end: (I1, the label is gone) */
    WPACKET_cleanup(&pkt);
''', 'I1 label')
    if FIX:
        # D1: ossl_a2ulabel, the ACE prefix in any case
        s = replace(s, '''        if (!HAS_PREFIX(inptr, "xn--")) {
''', '''        if (!HAS_CASE_PREFIX(inptr, "xn--")) { /* quickproof: if (!HAS_PREFIX(inptr, "xn--")) { (D1) */
''', 'D1 ACE prefix')
    if re.search(r'\bgoto\b', re.sub(r'/\*.*?\*/', '', s, flags=re.S)):
        sys.exit('osslpatch.py: a goto is left in %s' % PUNY)
    open(PUNY, 'w').write(s)


if __name__ == '__main__':
    main()
