/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
import RiemannLabs.Bridge.RvMCumulative
import ZetaZeros.Main

noncomputable section

namespace RiemannLabs.Bridge

/-- The Lamzouri 67.25% result; pair correlation is now the only remaining analytic input. -/
theorem simple_density_6725 (hPC : ZetaZeros.PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.6725 < (ZetaZeros.simpleOnLineCount T : ℝ) / (ZetaZeros.zeroCount T : ℝ) :=
  ZetaZeros.simple_proportion_d4 axiomRiemannVonMangoldt hPC

/-- The corresponding 83.625% lower bound for distinct nontrivial zeros. -/
theorem distinct_density_83625 (hPC : ZetaZeros.PairCorrelation) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      0.83625 < (ZetaZeros.distinctZeroCount T : ℝ) / (ZetaZeros.zeroCount T : ℝ) :=
  ZetaZeros.distinct_proportion_d5 axiomRiemannVonMangoldt hPC

end RiemannLabs.Bridge
