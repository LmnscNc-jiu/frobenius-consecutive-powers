#!/usr/bin/env python3
"""Independent soundness test of Lemma 2.1 (certificate criterion).

For random triples (a,b,c) with gcd(a,b,c) = 1 and small a, we enumerate EVERY integer tuple
(l,h,w,y) satisfying the hypotheses (i)-(iii) of Lemma 2.1 -- not only the one produced by
Rodseth's algorithm -- and check each conclusion of the lemma against a brute-force
computation of the Apery set (Dijkstra on residues modulo a):
  * omega(R) = Ap(S,a) as sets, and |R| = a,
  * F(S) = max(F1,F2) and the genus formula (2.3),
  * if w,y >= 1: PF(S) = {F1,F2} (computed by brute force from Ap(S,a)).
It also checks the box lemma (Lemma 2.3) and the covering lemma (Lemma 2.4) on the same triples,
and reports how many triples admit at least one certificate.  Usage: python3 test_certificate_lemma.py [TRIALS] [AMAX] [SEED]
"""
import sys, heapq, random
from math import gcd


def apery(a, gens):
    INF = float('inf'); dist = [INF] * a; dist[0] = 0; pq = [(0, 0)]
    while pq:
        d, r = heapq.heappop(pq)
        if d > dist[r]:
            continue
        for g in gens:
            nd = d + g; nr = nd % a
            if nd < dist[nr]:
                dist[nr] = nd; heapq.heappush(pq, (nd, nr))
    return dist


def brute_invariants(a, b, c):
    ap = apery(a, [b, c])
    F = max(ap) - a
    g = (sum(ap) - a * (a - 1) // 2) // a
    assert (sum(ap) - a * (a - 1) // 2) % a == 0
    apset = set(ap)
    pf = sorted(w - a for w in ap if all((w + s) not in apset for s in (b, c)))
    return ap, F, g, pf


def certificates(a, b, c):
    out = []
    for l in range(1, a + 1):
        for w in range(0, l):
            ymax = (l * b - 1) // c          # y*c < l*b
            for y in range(0, ymax + 1):
                num = a + w * y
                if num % l:
                    continue
                h = num // l
                if not (y < h):
                    continue
                if (l * b - y * c) % a or (h * c - w * b) % a:
                    continue
                if not (w * b < h * c):
                    continue
                out.append((l, h, w, y))
    return out


def reduced_basis(a, b, c):
    """a basis of the relation lattice {(i,j): a | i b + j c}, Lagrange-Gauss reduced"""
    from fractions import Fraction
    g = gcd(a, b)
    u = (a // g, 0)
    v = ((-c * pow(b // g, -1, a // g)) % (a // g) if a // g > 1 else 0, g)
    n2 = lambda z: z[0] * z[0] + z[1] * z[1]
    if n2(u) > n2(v): u, v = v, u
    while True:
        mu = round(Fraction(u[0] * v[0] + u[1] * v[1], n2(u)))
        v = (v[0] - mu * u[0], v[1] - mu * u[1])
        if n2(v) >= n2(u): break
        u, v = v, u
    return u, v


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    amax = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 12345)
    n_triples = n_certs = n_with_cert = n_pf = 0
    for _ in range(trials):
        a = random.randint(3, amax)
        b = random.randint(a + 1, 3 * a)
        c = random.randint(b + 1, 4 * a)
        if gcd(gcd(a, b), c) != 1:
            continue
        n_triples += 1
        ap, F, g, pf = brute_invariants(a, b, c)
        apset = set(ap)
        # Lemmas 2.3 and 2.4 (box lemma and covering lemma)
        u, v = reduced_basis(a, b, c)
        R = max(abs(u[0]), abs(u[1]), abs(v[0]), abs(v[1]))
        assert F < 4 * R * (b + c)                                 # Lemma 2.3
        X = (F + a) // b
        best = {}
        for i in range(X + 1):                                     # Lemma 2.4: every class meets [0,X]^2
            for j in range(X + 1):
                best.setdefault((i * b + j * c) % a, (i, j))
        assert len(best) == a
        r1 = best[((2 * X + 1) * b) % a]; r2 = best[((2 * X + 1) * c) % a]
        l1 = (2 * X + 1 - r1[0], -r1[1]); l2 = (-r2[0], 2 * X + 1 - r2[1])
        assert (l1[0] * b + l1[1] * c) % a == 0 and (l2[0] * b + l2[1] * c) % a == 0
        assert l1[0] * l2[1] - l2[0] * l1[1] > 0
        assert max(map(abs, l1 + l2)) <= 2 * X + 1
        certs = certificates(a, b, c)
        if certs:
            n_with_cert += 1
        for (l, h, w, y) in certs:
            n_certs += 1
            R = [(i, j) for i in range(l) for j in range(h) if not (i >= l - w and j >= h - y)]
            assert len(R) == a
            assert sorted(i * b + j * c for i, j in R) == sorted(ap), (a, b, c, l, h, w, y)
            F1 = (l - 1) * b + (h - y - 1) * c - a
            F2 = (l - w - 1) * b + (h - 1) * c - a
            assert max(F1, F2) == F
            S2 = (l * h * ((l - 1) * b + (h - 1) * c)
                  - w * y * ((2 * l - w - 1) * b + (2 * h - y - 1) * c))
            assert 2 * a * g == S2 - a * (a - 1), (a, b, c)
            if w >= 1 and y >= 1:
                n_pf += 1
                assert F1 != F2 and sorted([F1, F2]) == pf, (a, b, c, l, h, w, y, pf)
    print(f'triples tested: {n_triples}; triples admitting a certificate: {n_with_cert}; '
          f'certificates checked: {n_certs} (with w,y>=1: {n_pf}); all conclusions verified.')


if __name__ == '__main__':
    main()
