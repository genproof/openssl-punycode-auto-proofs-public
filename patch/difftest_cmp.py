#!/usr/bin/env python3
"""patch/difftest_cmp.py O_OUT P_OUT: compare the driver outputs (patch/difftest_drv.c) of the unmodified code (O) and
of the whole patch (P).  Every line must be identical, except that on a call tagged "A 1" (an ossl_a2ulabel call on
a string with an ACE prefix not in lowercase) P's line must equal O's following "N" line (the same call on the
string with those prefixes in lowercase): deviation D1.  Prints a summary; exit 1 on
an unexpected difference."""
import sys

o = open(sys.argv[1]).read().split('\n')
p = open(sys.argv[2]).read().split('\n')
if len(o) != len(p):
    print('different numbers of lines: %d, %d' % (len(o), len(p)))
    sys.exit(1)
flagged = changed = 0
i = 0
while i < len(o):
    if o[i].startswith('A 1 '):
        if i + 1 >= len(o) or not o[i + 1].startswith('N ') or not p[i + 1].startswith('N '):
            print('line %d: "A 1" without its "N" line' % (i + 1))
            sys.exit(1)
        flagged += 1
        if p[i][4:] != o[i + 1][2:] or p[i + 1] != o[i + 1]:
            print('line %d: the patched call is not the unmodified call on the lowercase-prefix string:\n  O %s\n  O %s\n  P %s'
                  % (i + 1, o[i], o[i + 1], p[i]))
            sys.exit(1)
        if p[i] != o[i]:
            changed += 1
        i += 2
        continue
    if o[i] != p[i]:
        print('line %d differs:\n  O %s\n  P %s' % (i + 1, o[i], p[i]))
        sys.exit(1)
    i += 1
print('identical except %d calls with an ACE prefix not in lowercase, each = the call on the lowercase-prefix string '
      '(%d of them changed by D1)' % (flagged, changed))
