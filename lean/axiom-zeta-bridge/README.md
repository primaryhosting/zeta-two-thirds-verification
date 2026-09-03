# Riemann Labs bridge: Zeta23 → AxiomMath/ZetaZeros

This Lake package connects the independently replicated `Zeta23` formalization to
Axiom Math's `ZetaZeros` formalization of Lamzouri's simple-zero result.

## What this slice proves

`RiemannLabs/Bridge/Counts.lean` proves against Mathlib's actual `riemannZeta` that:

- `ZetaZeros.nontrivialZeros T = Zeta23.zerosIn 0 T`;
- `ZetaZeros.zeroMultiplicity ρ = Zeta23.zeroMult ρ`;
- `ZetaZeros.zeroCount T = Zeta23.Ncount 0 T`.

`RiemannLabs/Bridge/ZetaZerosRvM.lean` then proves that Axiom's
`ZetaZeros.RiemannVonMangoldt` hypothesis is exactly the cumulative normalized RvM statement in
Zeta23's vocabulary. It also names the remaining analytic adapter as
`DyadicToCumulativeRvM` rather than hiding it.

`RiemannLabs/Bridge/Downstream.lean` verifies the final composition:

```text
Zeta23's unconditional dyadic RvM
       + DyadicToCumulativeRvM
       + Axiom's PairCorrelation
       ↓
67.25% simple and on the critical line
83.625% distinct
```

## Exact remaining obligations

1. Prove the finite/dyadic summation theorem
   `RiemannLabs.Bridge.DyadicToCumulativeRvM` from Zeta23's `RiemannVonMangoldt` package.
2. Formalize the Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh pair-correlation input represented
   by `ZetaZeros.PairCorrelation`.

No Riemann Hypothesis claim is made. No unproved declaration or project-specific axiom is introduced.
The parameter `hTransfer : DyadicToCumulativeRvM` remains visible in every theorem that uses it.

## Pinned sources

- Lean: `v4.34.0-rc2`
- Mathlib: `v4.34.0-rc2`
- `primaryhosting/zeta-23-lean`: `b7444066a79e7d0eb5840989426bc0a6b2a8120e`
  from branch `compat/lean-4.34`; this changes only three pointwise `logDeriv` rewrite names required
  by Mathlib's 4.34 function-operation API.
- `AxiomMath/ZetaZeros`: `4bcaf70e544506c311d83a5a5b143a134b9fc5f7`

The root package deliberately pins the newer Mathlib revision used by `ZetaZeros`; CI therefore also
acts as the forward-compatibility test for the imported Zeta23 modules. The bridge itself uses
Lean's legacy import boundary because Zeta23 predates the new `module` declaration while ZetaZeros
uses it.

## Build and audit

```bash
cd lean/axiom-zeta-bridge
lake update
lake exe cache get
lake build
lake env lean PrintAxioms.lean
```

The GitHub workflow fails if the package does not build or if a Lean source file contains `sorry`.
It caches compiled Zeta23 and ZetaZeros artifacts between iterations and cancels superseded runs.
