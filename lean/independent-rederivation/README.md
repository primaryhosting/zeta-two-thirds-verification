# Independent re-derivation of the §3 linear-algebra core

These Lean 4 files are **our own independent re-derivation** of the self-contained
linear-algebra core of the paper’s method (§3), produced by the Aristotle theorem
prover and **kernel-verified by the AXLE cloud checker at Lean 4.32.0** — a *different*
toolchain than the original formalization (Lean 4.33.0‑rc2). They re-prove the method’s
algebraic heart from scratch, giving an independent second proof of it.

They are **not** a re-derivation of the whole theorem: the analytic number theory
(Weil’s explicit formula, Montgomery’s pair correlation, the tail/prime-side estimates)
is **not** re-proved here, and nothing in this folder is a proof of the two-thirds theorem
or of the Riemann Hypothesis. This is the *linear-algebra layer only* — the part that is
finite, self-contained, and independently checkable.

Each file is standalone (it imports Mathlib and defines what it needs) and was accepted
axiom-clean by AXLE. Provenance: Aristotle (Harmonic) → AXLE (`axle.axiommath.ai`), Lean 4.32.0.

| File | What it proves |
|---|---|
| `vonNeumann_trace_ineq.lean` | von Neumann’s trace inequality: `Re tr(AB) ≤ Σ μᵢνᵢ` for Hermitian `A,B` with eigenvalues in like (decreasing) order |
| `sylvester_hermitian_finrank.lean` | Sylvester’s law of inertia (the direction used): positive-definite on a subspace `W` ⇒ `dim W ≤ posIndex A` |
| `rank_trace_ineq.lean` | the rank–trace inequality (the paper’s new §3 ingredient), via von Neumann + the scalar bounds |
| `eigenvalue_cauchy_schwarz_count.lean` | the thresholded Cauchy–Schwarz count at the eigenvalue level |
| `sq_ge_linear.lean`, `sq_ge_linear_two.lean`, `integrality_shadow.lean` | the scalar shadows `(x−c/2)² ≥ 0`, `(x−c)² ≥ 0`, and Montgomery’s integrality step |
| `qf_add.lean`, `quadForm_eq_complex.lean`, `sum_doublyStochastic_mul_le.lean` | supporting quadratic-form / doubly-stochastic lemmas used by the above |

`weyl_posIndexAbove` (Weyl monotonicity) is part of the same layer but was not yet
AXLE-verified at the time of writing, so it is omitted here.

### Register

`RE-DERIVATION` — an independent second proof of published, already-verified lemmas.
The lemmas themselves are Anthropic’s in the original formalization; this is our own,
separately-checked reconstruction of the finite core. License: CC BY 4.0 (see repository root).
