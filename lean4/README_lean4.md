# Lean 4 formalization of "On Lattice Tilings by Symmetric Limited Magnitude Error Balls"

Formalization in Lean 4 + Mathlib of the paper  (Ang Xiao, *On Lattice Tilings by Symmetric Limited Magnitude Error Balls: Q-Polynomials and Ideal Characterization*). All statements proved in the paper, except those resting on the Maple computations, are formalized and machine-checked with no `sorry`.

## File ↔ paper correspondence

| File | Paper item(s) |
|---|---|
| `Def2_7_Defs.lean` | Definition 2.7 (Q-polynomial) and the basic definitions |
| `Lem2_1_3_TilingGroup.lean` | Lemmas 2.1–2.3 (`lem:tiling-group`, `lem:mto1`, `lem:powersumFF`) |
| `Lem2_4_5_Period.lean` | Lemmas 2.4–2.5 (`lem:cahen-chabert`, `lem:period`) |
| `Thm2_6_Kummer.lean` | Theorem 2.6 (`thm:kummer`) |
| `Bell.lean` | §2.1 complete Bell polynomials (auxiliary) |
| `DSeries.lean` | §2.1 the series $d_{2j}(q,k)$ (auxiliary) |
| `DClosed.lean` | closed forms of $d_0,d_2,d_4,d_6$ (after Theorem 1.1) |
| `Thm1_1_QFormula.lean` | Theorem 1.1 (`thm:main`) and its proof |
| `CLambda.lean` | `eq:defclambda` and the integrality of $c_\lambda$ |
| `Thm1_2_Ideal.lean` | Lemma 4.1 (`lem:conditionX`), Theorem 4.2 (`thm:conditionY`), Theorem 1.2 (`thm:ideal`) |
| `Thm1_6_7_Families.lean` | Corollary 5.1 (`cor:p=3`), Theorems 1.6 & 1.7 (`thm:keq4mod9`, `thm:keq8mod9`) |
| `Thm5_2_Asymptotic.lean` | Theorem 5.2 (`thm:asymptotic-ratio`) |
| `Ex4_3_6_Examples.lean` | Examples 4.3–4.6 (`ex:t6k1p5`, `ex:t3k2p5`, `ex:t4k3p11`, `ex:table-data`) and the general test |
| `Ex4_3_5_Formulas.lean` | explicit data of Examples 4.3–4.5 |
| `Cor1_3_5_Corollaries.lean` | Corollaries 1.3–1.5 (`cor:t6k1`, `cor:t3k2`, `cor:t4k3`) |
| `Compute.lean` | fast computation of $c_\lambda$ (auxiliary) |
| `Main.lean` | entry point (Lean options) |
