# Supplementary material

Supplementary programs for **"The order of growth of the Frobenius number of three consecutive k-th powers"**.

## Requirements

- Python ≥ 3.9 with SymPy (tested with Python 3.13 and SymPy 1.14).
- A C compiler (tested with gcc).
- No other dependencies.

## Files

| File | What it does | Paper reference |
|---|---|---|
| `rod.py` | Rødseth's algorithm. Returns F(⟨a,b,c⟩) and the L-shape parameters (l,h,w,y). | Remark 2.2 |
| `test_rodseth.py` | Tests `rod.py` against brute force on random triples and on small members of the family. | — |
| `test_certificate_lemma.py` | Exhaustive soundness test of Lemma 2.1. For random triples it enumerates **every** (l,h,w,y) satisfying the hypotheses and compares all conclusions (Apéry set, F, genus, PF) with brute force. It also tests the box lemma and the covering lemma on the same triples. | Lemmas 2.1, 2.3, 2.4; Sect. 6 (iv) |
| `table_k4.py` | The parameters of Table A.1. | Table A.1 |
| `verify_k4.py` | Proof checker for Theorem 5.1, in exact arithmetic. It verifies (C1)–(C4) for all 40 classes, computes N_r and N'_r, and derives Tables A.2–A.4. It certifies each n < 280 individually with Lemma 2.1 and compares the closed form with Rødseth's algorithm for n ≤ NMAX. It writes `results_k4.json` and `table3_k4.tex`. | Theorem 5.1, Tables A.1–A.5 |
| `make_tables_k4.py` | Generates Tables A.1–A.5 from the output of `verify_k4.py`. With `--check ../manuscript/main.tex` it checks that the printed tables are identical to the generated ones. | Appendix A, Sect. 6 |
| `verify_general.py` | Checks Proposition 3.1 for (p,q) = (1,2), k ≤ 16, and for five other pairs (p,q), k ≤ 10. It produces Table 2 and checks the L-shape certificates behind Corollary 1.3 and Remark 4.6 for k ≤ 7. | Prop. 3.1, Example 3.2, Table 2, Cor. 1.3, Remark 4.6 |
| `check_constants.py` | Computes the constant A of Section 4 and checks all inequalities of Proposition 4.1 and Theorem 4.2, with the exact successive minima and Frobenius numbers. The default is (p,q) = (1,2); other shifts are given as extra arguments. | Prop. 4.1, Thm 4.2, Table 2 |
| `check_published.py` | Compares with the published formulas of Lepilov–O'Rourke–Swanson (k = 2, 3) and with Fel's minimal-relation matrices (k = 4). The data are transcribed in `los_formulas.json` and `fel_k4_matrices.json`. | Sect. 6 (i), (ii); Remark 5.2(3) |
| `apery.c` | Brute-force Apéry set (Böcker–Lipták round-robin). Prints n, F, g, type and PF. | Remark 5.2(1) |
| `apery_k4_n2_130.txt` | Output of `./apery 4 2 130`. Each line gives n, F, g, type and the pseudo-Frobenius numbers. Checked with `python3 check_apery_k4.py apery_k4_n2_130.txt`. | Remark 5.2(1) |
| `lean/` | Lean 4 + Mathlib formalization of all theorems and corollaries of the paper (Table 1 of the paper). See `lean/README.md` for the exact scope, what is not formalized, and build instructions. | Sect. 6 "Formal verification" |
| `check_lean_vs_paper.py` | Checks that the closed forms and the Table A.5 data used in `lean/` are exactly those printed in the paper (Tables A.3–A.5 and (2.2)). Usage: `python3 check_lean_vs_paper.py ../manuscript/main.tex`. | Sect. 6 |
| `check_apery_k4.py` | Compares the output of `apery.c` (k = 4) with Theorem 5.1 and Table A.5: Frobenius number, genus, type and pseudo-Frobenius numbers. | Remark 5.2(1), Sect. 6 (iii) |
| `CITATION.cff` | Citation metadata for the public repository (to be completed by the author). | — |

## Reproduction

Run everything:

```bash
bash run_all.sh
```

Or run each step separately. Each command is followed by the line it must print.

```bash
python3 test_certificate_lemma.py 4000 100 7
```

```text
triples tested: 3327; ... certificates checked: 3182 (with w,y>=1: 2309); all conclusions verified.
```

```bash
python3 make_tables_k4.py --check ../manuscript/main.tex
```

```text
ALL TABLES IDENTICAL
```

This step needs the files `results_k4.json` and `table3_k4.tex` written by `verify_k4.py` (next step), so run it after `verify_k4.py`.

```bash
python3 verify_k4.py 20000
```

```text
ALL CHECKS PASSED
```

`verify_k4.py` also prints the thresholds for each class.

```bash
python3 verify_general.py 16
```

```text
DONE
```

```bash
python3 check_constants.py 7 3000
```

```text
ALL CONSTANT CHECKS PASSED
```

```bash
python3 check_published.py 3000
```

```text
... disagreements: 0
```

`check_published.py` prints three such lines.

```bash
gcc -O2 -o apery apery.c
```

```bash
./apery 4 2 130 > apery_k4.txt
```

```bash
python3 check_apery_k4.py apery_k4.txt
```

```text
brute force agrees with Theorem 5.1 / Table A.5 for all 129 values of n (2..130); ...
```

`apery` needs about 8·n⁴ bytes of memory, so the run at n = 130 needs about 2.3 GB. `run_all.sh` runs only n ≤ 60, which is fast.

## Formal verification

```bash
cd lean
```

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake env lean AxiomCheck.lean
```

See `lean/README.md` for what is proved, the expected output, and Windows instructions.

## What is and is not a proof

- The proofs of Theorems 1.1, 1.2, 4.2 and Corollary 1.3 in the paper are purely mathematical and do not use any computation.
- The proof of Theorem 5.1 is computer-assisted. It consists of the identities and inequalities (C1)–(C4), which are listed in Tables A.1–A.2. They are checked by `verify_k4.py` in exact rational arithmetic, and each can also be confirmed by hand or with any computer algebra system.
- In addition, every theorem and corollary of the paper is machine-checked in Lean (`lean/`). The exceptions and differences are listed in Table 1 of the paper and in `lean/README.md`. Not machine-checked are the Euclidean form of Theorem 1.2 and the explicit values of the constants; the explicit constants are checked numerically by `check_constants.py`.
- `check_lean_vs_paper.py` and `make_tables_k4.py --check` confirm that the printed tables are exactly the data used by the programs and by the Lean statements.
- All other programs are independent consistency checks and are not part of any proof.
