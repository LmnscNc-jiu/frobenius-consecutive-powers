#!/usr/bin/env bash
# Reproduces every computation reported in the paper. Run from this directory.
# Requirements: python3 (>= 3.9) with sympy; a C compiler. Total time: about 10 minutes on 4 cores.
set -euo pipefail
echo "== 1. Rodseth implementation vs brute force";            python3 test_rodseth.py
echo "== 2. Lemmas 2.1, 2.3, 2.4: exhaustive tests";          python3 test_certificate_lemma.py 4000 100 7
python3 test_certificate_lemma.py 400 300 8
echo "== 3. Theorem 5.1 (k = 4): certificate verification";  python3 verify_k4.py 20000 | tail -8
echo "== 4. Proposition 3.1, Table 2, Corollary 1.3 data";   python3 verify_general.py 16 | tail -45
echo "== 5. Explicit constants (Prop. 4.1, Thms 1.2, 4.2)";  python3 check_constants.py 7 3000
for pq in "1 3" "2 3" "4 9"; do python3 check_constants.py 4 300 $pq | tail -5; done
echo "== 6. Published formulas (LOS 2015, Fel 2016)";        python3 check_published.py 3000
echo "== 7. Brute-force Apery sets for k = 4, 2 <= n <= 60"; gcc -O2 -o apery apery.c && ./apery 4 2 60 > apery_k4.txt && python3 check_apery_k4.py apery_k4.txt
if [ -f ../manuscript/main.tex ]; then
  echo "== 8. Lean closed forms vs paper tables"; python3 check_lean_vs_paper.py ../manuscript/main.tex
  echo "== 9. Printed Tables A.1-A.5 vs output of verify_k4.py"; python3 make_tables_k4.py --check ../manuscript/main.tex
fi
echo "ALL DONE"
