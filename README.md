# Nonexistence Results of Lattice Tiling by Symmetric Limited Magnitude Error Balls

This repository contains the code and output in Appendix B of

> Ang Xiao, *On Lattice Tilings by Symmetric Limited Magnitude Error Balls:
> Q-Polynomials and Ideal Characterization*.

The code is runnable in Maple.

## Files

- `Codes/IdealMethodCode.txt` — Maple implementation of Theorems 1.1 and 1.2
  for arbitrary `t`, `k` and an odd prime `p` (Appendix A, Listing 1 of the paper).
- `Codes/ComputeAllResults.txt` — the loop over `2 <= t <= 10`, `1 <= k <= 10`
  and all primes `3 <= p <= 29` that produced the raw data of Appendix B.
- `Nonexistence Results of Lattice Tiling by Symmetric Limited Magnitude Error Balls.md`
  — the full raw output: for each triple `(t, k, p)` the residue classes `n`
  modulo `p^(2 + floor(log_p t))` excluded by Theorem 1.2. `N/A` means that no
  residue class was excluded for that triple.
- `results.csv` — the same data in machine-readable form.

## How to read the data

For a triple `(t, k, p)` with `2 <= t <= 10`, `1 <= k <= 10` and prime
`3 <= p <= 29`, every listed residue class `n` modulo `p^(2 + floor(log_p t))`
satisfies `p | |B(n, t, k, k)|`, `p^2 ∤ |B(n, t, k, k)|`, and passes the
ideal-membership test of Theorem 1.2; for such `n` no lattice tiling of
`Z^n` by `B(n, t, k, k)` exists. The entry `n = p^(2 + floor(log_p t))`
represents the residue class `0` modulo that period.

The percentage in Table 1 of the paper for a pair `(t, k)` is
`1 - prod_p (1 - |N2(p)| / p^(2 + floor(log_p t)))` over the nine primes
`3 <= p <= 29`, where `N2(p)` is the excluded set printed for `(t, k, p)`.
