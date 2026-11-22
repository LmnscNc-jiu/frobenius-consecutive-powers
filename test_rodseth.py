#!/usr/bin/env python3
"""Sanity test: Rodseth's formula (rod.py) against a brute-force Apery-set computation
(Dijkstra on residues) for random triples, and for S_n^k with small n, k = 2, 3, 4."""
import heapq, random
from math import gcd
from rod import rodseth_data

def frob_brute(gens):
    a = min(gens); INF = float('inf'); dist = [INF] * a; dist[0] = 0; pq = [(0, 0)]
    while pq:
        d, r = heapq.heappop(pq)
        if d > dist[r]: continue
        for g in gens:
            nd = d + g; nr = nd % a
            if nd < dist[nr]: dist[nr] = nd; heapq.heappush(pq, (nd, nr))
    return max(dist) - a

random.seed(2026); tested = 0
for _ in range(4000):
    a1 = random.randint(2, 60); a2 = random.randint(a1 + 1, 150); a3 = random.randint(a2 + 1, 300)
    if gcd(a1, a2) != 1 or (a3 * pow(a2, -1, a1)) % a1 == 0: continue
    assert rodseth_data(a1, a2, a3)['F'] == frob_brute([a1, a2, a3]), (a1, a2, a3)
    tested += 1
for k, nmax in ((2, 30), (3, 20), (4, 9)):
    for n in range(2, nmax):
        g = [n**k, (n + 1)**k, (n + 2)**k]
        assert rodseth_data(*g)['F'] == frob_brute(g), (k, n)
print('OK: %d random triples and the families k=2,3,4 (small n) agree with brute force' % tested)
