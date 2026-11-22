#!/usr/bin/env python3
"""Numerical check of the explicit constants in the proofs of Section 4 (Proposition 4.1,
Theorem 1.2 and Theorem 4.2), for S = <n^k, (n+p)^k, (n+q)^k> with 0 < p < q.

For each (p, q) and k, integral relations V1 (degree floor(k/2)) and V2 (degree ceil(k/2)) with
det(V1, V2) = kappa x^k are computed as in Proposition 3.1 (D = 1), and A = max(|V1|, |V2|),
where |V| is the largest sum of absolute values of the coefficients of an entry of V.  The proofs
give, for every n >= 1 with gcd(n, p, q) = 1 (Proposition 4.1):
  n^d1 / (2A) <= lambda_1^inf <= |V1| n^d1,      n^d2 / (2A) <= lambda_2^inf <= A n^d2,
and, for n >= 2 (Lemmas 2.3, 2.4 and the proof of Theorem 4.2, e = k + d2):
  n^e/(4A) - (3/2) n^k <= F < 4 A n^d2 ((n+p)^k + (n+q)^k),
  c_k n^e <= F <= C_k n^e   with  c_k = (12A)^(-e/d2),  C_k = 4A((1+p)^k + (1+q)^k).
In particular liminf F/n^e >= 1/(4A) and limsup F/n^e <= 8A.
For every n in the range we compute the exact sup-norm successive minima and the Frobenius number
and check all these inequalities.

Usage: python3 check_constants.py KMAX NMAX      (consecutive case (p, q) = (1, 2))
       python3 check_constants.py KMAX NMAX p q
"""
import sys, os, math
from math import gcd
from fractions import Fraction
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rod import rodseth_data

x = sp.symbols('x')


def relation_space(k, d, p, q):
    ps = sp.symbols('p0:%d' % (d + 1)); zs = sp.symbols('z0:%d' % (d + 1))
    P = sum(ps[i] * x**i for i in range(d + 1)); Z = sum(zs[i] * x**i for i in range(d + 1))
    e = sp.expand(P * (x + p)**k + Z * (x + q)**k)
    M, _ = sp.linear_eq_to_matrix([e.coeff(x, i) for i in range(k)], list(ps) + list(zs))
    out = []
    for v in M.nullspace():
        den = sp.ilcm(*[sp.fraction(t)[1] for t in v]); v = [t * den for t in v]
        g = sp.igcd(*[int(t) for t in v]); v = [int(t) // g for t in v]
        out.append(([v[i] for i in range(d + 1)], [v[d + 1 + i] for i in range(d + 1)]))
    return out


def poly(c): return sum(ci * x**i for i, ci in enumerate(c))


def l1norm(V): return max(sum(abs(t) for t in V[0]), sum(abs(t) for t in V[1]))


def basis(k, p, q):
    d1, d2 = k // 2, (k + 1) // 2
    V1 = relation_space(k, d1, p, q)[0]
    for V in relation_space(k, d2, p, q):
        det = sp.expand(poly(V1[0]) * poly(V[1]) - poly(V[0]) * poly(V1[1]))
        if det != 0:
            kappa = sp.Poly(det, x).LC()
            assert sp.expand(det - kappa * x**k) == 0
            return V1, V, int(kappa)
    raise AssertionError('no V2')


def frob(a, b, c):
    """Frobenius number of <a,b,c> with gcd(a,b,c) = 1 (Rodseth + Johnson's reduction)."""
    a, b, c = sorted((a, b, c))
    for (u, v, w) in ((a, b, c), (a, c, b), (b, c, a)):
        if gcd(u, v) == 1:
            if w % u == 0 or w % v == 0:
                return u * v - u - v
            s0 = (w * pow(v, -1, u)) % u
            if s0 == 0:
                return u * v - u - v
            return rodseth_data(u, v, w)['F']
    d = gcd(a, b)                       # Johnson: F(a,b,c) = d F(a/d, b/d, c) + (d-1) c
    return d * frob(a // d, b // d, c) + (d - 1) * c


def frob_brute(a, b, c):
    """round-robin shortest paths in Z/a (Boecker-Liptak); for testing frob()"""
    INF = float('inf'); w = [INF] * a; w[0] = 0
    for g in (b, c):
        d = gcd(a, g)
        for r in range(d):
            # find the minimum on the cycle r, r+g, ...
            cyc = [(r + i * g) % a for i in range(a // d)]
            m = min(range(len(cyc)), key=lambda i: w[cyc[i]])
            n0 = w[cyc[m]]
            for i in range(1, len(cyc) + 1):
                j = cyc[(m + i) % len(cyc)]
                n0 = min(n0 + g, w[j]); w[j] = n0
    return max(w) - a


def minima(a, b, c):
    """exact sup-norm successive minima of {(i,j): a | i b + j c}, gcd(a,b,c) = 1"""
    g = gcd(a, b)
    u = (a // g, 0)
    i0 = (-c * pow(b // g, -1, a // g)) % (a // g) if a // g > 1 else 0
    v = (i0, g)
    def n2(z): return z[0] * z[0] + z[1] * z[1]
    if n2(u) > n2(v): u, v = v, u
    while True:                                   # Lagrange-Gauss reduction
        mu = round(Fraction(u[0] * v[0] + u[1] * v[1], n2(u)))
        v = (v[0] - mu * u[0], v[1] - mu * u[1])
        if n2(v) >= n2(u): break
        u, v = v, u
    vecs = []
    for s in range(-4, 5):
        for t in range(-4, 5):
            if (s, t) != (0, 0):
                z = (s * u[0] + t * v[0], s * u[1] + t * v[1])
                vecs.append((max(abs(z[0]), abs(z[1])), z))
    vecs.sort()
    lam1, z1 = vecs[0]
    lam2 = next(m for m, z in vecs if z[0] * z1[1] - z[1] * z1[0] != 0)
    return lam1, lam2


def main():
    KMAX, NMAX = int(sys.argv[1]), int(sys.argv[2])
    p, q = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (1, 2)
    assert 0 < p < q
    import random
    rnd = random.Random(1)
    for _ in range(300):                          # test frob() against brute force
        a = rnd.randint(2, 400); b = rnd.randint(a + 1, 900); c = rnd.randint(b + 1, 1500)
        if gcd(gcd(a, b), c) == 1:
            assert frob(a, b, c) == frob_brute(a, b, c), (a, b, c)
    print(f'(p,q)=({p},{q}): frob() agrees with brute force on random triples')
    for k in range(2, KMAX + 1):
        d1, d2 = k // 2, (k + 1) // 2
        e = k + d2
        V1, V2, kappa = basis(k, p, q)
        A1, A = l1norm(V1), max(l1norm(V1), l1norm(V2))
        ck = (12 * A) ** (-e / d2); Ck = 4 * A * ((1 + p)**k + (1 + q)**k)
        rmin, rmax, cnt = math.inf, 0.0, 0
        for n in range(1, NMAX + 1):
            if gcd(n, gcd(p, q)) != 1:
                continue
            a, b, c = n**k, (n + p)**k, (n + q)**k
            if a > 1:
                lam1, lam2 = minima(a, b, c)
                assert n**d1 <= 2 * A * lam1 and lam1 <= A1 * n**d1, (k, n, 'lambda1')
                assert n**d2 <= 2 * A * lam2 and lam2 <= A * n**d2, (k, n, 'lambda2')
            if n >= 2:
                F = frob(a, b, c)
                assert Fraction(n**e, 4 * A) - Fraction(3, 2) * n**k <= F < 4 * A * n**d2 * (b + c), (k, n)
                assert ck * n**e <= F <= Ck * n**e, (k, n)
                rmin = min(rmin, F / n**e); rmax = max(rmax, F / n**e); cnt += 1
        print(f'  k={k}: kappa={kappa}, A={A}; 1/(4A)={1/(4*A):.3g} <= liminf, limsup <= 8A={8*A}; '
              f'F/n^{e} in [{rmin:.4f}, {rmax:.4f}] for {cnt} values of n <= {NMAX}; '
              f'c_k={ck:.3g}, C_k={Ck}')
    print('ALL CONSTANT CHECKS PASSED')


if __name__ == '__main__':
    main()
