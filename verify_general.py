#!/usr/bin/env python3
"""
Computational illustrations of the general-k results of the paper
  "The order of growth of the Frobenius number of three consecutive k-th powers".

(1) Proposition 3.1: for 2 <= k <= KMAX the module of polynomial relations
      P(x)(x+p)^k + Z(x)(x+q)^k = 0 (mod x^k)
    has no nonzero element of degree < floor(k/2), contains V1 of degree floor(k/2)
    and V2 of degree ceil(k/2) with det(V1,V2) = kappa x^k, kappa != 0.
    Checked for (p,q) = (1,2) (consecutive powers) and for several other shifts.
    (The proposition is proved in the paper for all k and all 0 < p < q; this is only a
    sanity check.)
(2) Theorem 1.1: ranges of F(S_n^k)/n^{e_k}, e_k = k + ceil(k/2), for n in a window.
(3) Corollary 1.3: for n >= 2^(k+1) the Apery set is a proper L-shape (w,y >= 1),
    certified by Lemma 2.1, hence S_n^k is not symmetric and has type 2.
"""
import sys
import sympy as sp
from rod import rodseth_data

x = sp.symbols('x')


def relation_space(k, d, p=1, q=2):
    ps = sp.symbols('p0:%d' % (d + 1)); zs = sp.symbols('z0:%d' % (d + 1))
    P = sum(ps[i] * x**i for i in range(d + 1)); Z = sum(zs[i] * x**i for i in range(d + 1))
    e = sp.expand(P * (x + p)**k + Z * (x + q)**k)
    eqs = [e.coeff(x, i) for i in range(k)]
    A, _ = sp.linear_eq_to_matrix(eqs, list(ps) + list(zs))
    basis = []
    for v in A.nullspace():
        den = sp.ilcm(*[sp.fraction(t)[1] for t in v])
        v = [t * den for t in v]
        basis.append((sp.expand(sum(v[i] * x**i for i in range(d + 1))),
                      sp.expand(sum(v[d + 1 + i] * x**i for i in range(d + 1)))))
    return basis


def check_prop31(KMAX, p=1, q=2, verbose=True):
    print('Proposition 3.1 check for (p,q) = (%d,%d)' % (p, q))
    for k in range(2, KMAX + 1):
        d1, d2 = k // 2, (k + 1) // 2
        low = relation_space(k, d1 - 1, p, q) if d1 >= 1 else []
        B1 = relation_space(k, d1, p, q)
        B2 = relation_space(k, d2, p, q)
        assert len(low) == 0, k
        V1 = B1[0]
        det = None
        for V2 in B2:
            dd = sp.expand(V1[0] * V2[1] - V1[1] * V2[0])
            if dd != 0:
                det = dd; break
        kappa = sp.Poly(det, x).LC()
        assert sp.expand(det - kappa * x**k) == 0
        # Example 3.2: dimension 1 (odd k) or 2 (even k) in degree <= d1
        assert len(B1) == (2 if k % 2 == 0 else 1), (k, p, q, len(B1))
        if verbose:
            print(f'  k={k:2d}: no relation of degree <= {d1-1}; dim(deg<={d1})={len(B1)}, '
                  f'dim(deg<={d2})={len(B2)}; det(V1,V2) = {kappa} * x^{k}')
    if not verbose:
        print(f'  all k <= {KMAX}: normality, dimensions and det(V1,V2) = kappa x^k confirmed')


def growth(KMAX, n0, n1):
    print('Theorem 1.1: F(S_n^k)/n^e_k for %d <= n <= %d' % (n0, n1))
    for k in range(2, KMAX + 1):
        e = k + (k + 1) // 2
        rs = [rodseth_data(n**k, (n + 1)**k, (n + 2)**k)['F'] / n**e for n in range(n0, n1 + 1)]
        print(f'  k={k:2d}  e_k={e:2d}  min={min(rs):.4f}  max={max(rs):.4f}')


def certificate_numeric(l, h, w, y, A, B, C):
    return (l >= 1 and h >= 1 and 0 <= w < l and 0 <= y < h and l * h - w * y == A
            and (l * B - y * C) % A == 0 and (h * C - w * B) % A == 0
            and l * B > y * C and h * C > w * B)


def type_two(KMAX, span):
    print('Corollary 1.3: proper L-shape certificates for 2^(k+1) <= n < 2^(k+1)+%d' % span)
    for k in range(2, KMAX + 1):
        sym = []
        for n in range(2, 2**(k + 1) + span):
            A, B, C = n**k, (n + 1)**k, (n + 2)**k
            d = rodseth_data(A, B, C)
            l, h, w, y = d['sv'], d['pv1'], d['sv1'], d['pv']
            ok = certificate_numeric(l, h, w, y, A, B, C) and w >= 1 and y >= 1
            if n >= 2**(k + 1):
                assert ok, (k, n)
            elif not ok:
                sym.append(n)
        print(f'  k={k}: all certified; n < 2^(k+1) without a proper L-shape certificate: {sym}')


if __name__ == '__main__':
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    check_prop31(KMAX)
    for (p, q) in [(1, 3), (2, 3), (2, 5), (3, 4), (4, 9)]:
        check_prop31(min(KMAX, 10), p, q, verbose=False)
    growth(min(KMAX, 10), 200, 4000)
    type_two(min(KMAX, 7), 3000)
    print('DONE')
