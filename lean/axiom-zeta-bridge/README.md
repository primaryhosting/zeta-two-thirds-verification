# Riemann Labs bridge: Zeta23 → AxiomMath/ZetaZeros

This Lake package connects the independently replicated `Zeta23` formalization to Axiom Math's
`ZetaZeros` formalization of Lamzouri's simple-zero result.

## Verified result

The bridge proves against Mathlib's actual `riemannZeta` that:

- `ZetaZeros.nontrivialZeros T = Zeta23.zerosIn 0 T`;
- `ZetaZeros.zeroMultiplicity ρ = Zeta23.zeroMult ρ`;
- `ZetaZeros.zeroCount T = Zeta23.Ncount 0 T`.

It then converts Zeta23's proved dyadic Riemann–von Mangoldt theorem into Axiom's cumulative
normalization:

```text
Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  → cumulativeRiemannVonMangoldt_of_rvm
  → dyadicToCumulativeRvM
  → axiomRiemannVonMangoldt
```

The proof introduces an additive monotone scale, proves its exact dyadic increment, derives
bidirectional local RvM comparisons, and transfers both inequalities from `(T, 2T]` to `(0, T]`.
No RvM hypothesis or adapter parameter remains in the downstream density statements.

## Downstream endpoint

```text
axiomRiemannVonMangoldt
       + ZetaZeros.PairCorrelation
       ↓
simple_density_6725
  > 67.25% of nontrivial zeros are simple and on the critical line

distinct_density_83625
  > 83.625% of nontrivial zeros are distinct
```

The **only remaining analytic input** in this composition is
`ZetaZeros.PairCorrelation`, representing the Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh
pair-correlation theorem in Axiom's normalization.

This is not a proof of the Riemann Hypothesis. It is a verified interoperability result and a
reduction of Axiom's density theorem to one explicit pair-correlation obligation.

## Trust boundary

The bridge contains no `sorry` and introduces no project-specific axiom. CI performs:

```bash
lake build
lake env lean PrintAxioms.lean
```

and rejects unfinished Lean proofs. The audited bridge theorems use only the standard Lean/Mathlib
axiom boundary inherited from the verified upstream developments.

## Pinned sources

- Lean: `v4.34.0-rc2`
- Mathlib: `v4.34.0-rc2`
- `primaryhosting/zeta-23-lean`: `b7444066a79e7d0eb5840989426bc0a6b2a8120e`
- `AxiomMath/ZetaZeros`: `4bcaf70e544506c311d83a5a5b143a134b9fc5f7`

The Zeta23 pin contains only three Mathlib 4.34 API substitutions from `logDeriv_mul` to
`logDeriv_fun_mul`; no theorem statement, constant, normalization, or analytic argument changes.
The bridge uses Lean's legacy import boundary because Zeta23 predates the new `module` declaration
while ZetaZeros uses it.

## Build locally

```bash
cd lean/axiom-zeta-bridge
lake update
lake exe cache get
lake build
lake env lean PrintAxioms.lean
```
