/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
module

public import RiemannLabs.Bridge.Counts
public import Zeta23.GammaFacts.Complete
public import Zeta23.RvM.Statement
public import ZetaZeros.Defs

noncomputable section

namespace RiemannLabs.Bridge

/-- The cumulative Riemann--von Mangoldt statement in Zeta23's counting vocabulary. -/
def CumulativeRiemannVonMangoldt : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    |(Zeta23.Ncount 0 T : ℝ) /
        (T / (2 * Real.pi) * Real.log T) - 1| < ε

/-- After identifying the counts, Axiom's RvM hypothesis is exactly the cumulative Zeta23 form. -/
theorem cumulativeRiemannVonMangoldt_iff_axiom :
    CumulativeRiemannVonMangoldt ↔ ZetaZeros.RiemannVonMangoldt := by
  unfold CumulativeRiemannVonMangoldt ZetaZeros.RiemannVonMangoldt
  simpa only [zeroCount_eq_Ncount]

/--
The one remaining RvM adapter obligation: convert Zeta23's proved dyadic/local-count package into
its cumulative normalized asymptotic. Keeping this as a named proposition makes the trust boundary
machine-visible and prevents an analytic summation step from being smuggled in as an axiom.
-/
def DyadicToCumulativeRvM : Prop :=
  Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig → CumulativeRiemannVonMangoldt

/-- Zeta23's unconditional RvM theorem closes Axiom's RvM input once the summation adapter is supplied. -/
theorem axiomRiemannVonMangoldt_of_dyadicTransfer
    (hTransfer : DyadicToCumulativeRvM) : ZetaZeros.RiemannVonMangoldt := by
  apply cumulativeRiemannVonMangoldt_iff_axiom.mp
  exact hTransfer (Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts)

end RiemannLabs.Bridge
