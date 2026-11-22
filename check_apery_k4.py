#!/usr/bin/env python3
"""Compare brute-force Apery data for k = 4 (output of `./apery 4 nmin nmax`, lines
"n F g type PF...") with Theorem 5.1 and Table A.5.  For each n, the predicted (F, g, PF) come from
Lemma 2.1 applied to the class parameters of Table A.1 whenever these satisfy the hypotheses at n,
and otherwise to the parameters produced by Rodseth's algorithm (the individual certificates
behind Table A.5).  Usage: python3 check_apery_k4.py apery_k4.txt [more files]"""
import os, sys
from fractions import Fraction as Fr
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from table_k4 import TABLE
from rod import rodseth_data


def hyp(l, h, w, y, A, B, C):
    return (l >= 1 and h >= 1 and 0 <= w < l and 0 <= y < h and l*h - w*y == A
            and (l*B - y*C) % A == 0 and (h*C - w*B) % A == 0 and l*B > y*C and h*C > w*B)


def lemma(l, h, w, y, A, B, C):
    F1 = (l-1)*B + (h-y-1)*C - A; F2 = (l-w-1)*B + (h-1)*C - A
    S2 = l*h*((l-1)*B + (h-1)*C) - w*y*((2*l-w-1)*B + (2*h-y-1)*C)
    pf = sorted({F1, F2}) if (w >= 1 and y >= 1) else [max(F1, F2)]
    return max(F1, F2), (S2 - A*(A-1)) // (2*A), pf


rows = []
for fn in sys.argv[1:]:
    for line in open(fn):
        t = line.split()
        if len(t) >= 4:
            rows.append((int(t[0]), int(t[1]), int(t[2]), int(t[3]), sorted(int(v) for v in t[4:])))
by_class = 0
for N, F, g, tp, pf in sorted(rows):
    A, B, C = N**4, (N+1)**4, (N+2)**4
    vals = [sum(Fr(c) * N**i for i, c in enumerate(p)) for p in TABLE[N % 40]]
    if all(v.denominator == 1 for v in vals) and hyp(*[int(v) for v in vals], A, B, C):
        pred = lemma(*[int(v) for v in vals], A, B, C); by_class += 1
    else:
        d = rodseth_data(A, B, C)
        assert hyp(d['sv'], d['pv1'], d['sv1'], d['pv'], A, B, C), N
        pred = lemma(d['sv'], d['pv1'], d['sv1'], d['pv'], A, B, C)
    assert pred == (F, g, pf) and tp == len(pf), (N, pred, (F, g, pf))
print(f'brute force agrees with Theorem 5.1 / Table A.5 for all {len(rows)} values of n '
      f'({min(r[0] for r in rows)}..{max(r[0] for r in rows)}); class certificates used for {by_class}')
