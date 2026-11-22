"""Rodseth's algorithm (J. Reine Angew. Math. 301 (1978)) for the Frobenius number of <a1,a2,a3>.

Requires gcd(a1,a2) = 1 and a3 not congruent to 0 modulo a1 after the normalisation below.
With s_{-1}=a1, s_0 = a3 * a2^{-1} mod a1, the "negative" continued fraction
s_{i-1} = q_{i+1} s_i - s_{i+1}, and p_{-1}=0, p_0=1, p_{i+1}=q_{i+1} p_i - p_{i-1}, let v be the
index with r_{v+1} <= 0 < r_v, where r_i = (s_i a2 - p_i a3)/a1.  Then
   F = -a1 + a2 (s_v - 1) + a3 (p_{v+1} - 1) - min(a2 s_{v+1}, a3 p_v),
and (l,h,w,y) = (s_v, p_{v+1}, s_{v+1}, p_v) are the L-shape parameters of Lemma 2.1.
(Returned as keys sv, pv1, sv1, pv.)  Tested against brute force in test_rodseth.py.
"""
from math import gcd
def rodseth_data(a1,a2,a3):
    s0 = (a3*pow(a2,-1,a1)) % a1
    s=[a1,s0]; p=[0,1]; qs=[]
    while s[-1]!=0:
        q=-(-s[-2]//s[-1]); qs.append(q); s.append(q*s[-1]-s[-2]); p.append(q*p[-1]-p[-2])
    r=[s[j]*a2-p[j]*a3 for j in range(len(s))]
    for j in range(len(s)-1):
        if r[j]>0 and r[j+1]<=0: v=j;break
    F = -a1+a2*(s[v]-1)+a3*(p[v+1]-1)-min(a2*s[v+1],a3*p[v])
    return dict(F=F, v=v, s=s, p=p, q=qs, sv=s[v], sv1=s[v+1], pv=p[v], pv1=p[v+1])
def frob(a1,a2,a3): return rodseth_data(a1,a2,a3)['F']
