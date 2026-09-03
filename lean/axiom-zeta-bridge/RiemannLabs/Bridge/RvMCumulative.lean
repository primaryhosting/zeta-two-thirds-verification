/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
import RiemannLabs.Bridge.RvMLocal
import RiemannLabs.Bridge.ZetaZerosRvM

open Filter Topology

noncomputable section

namespace RiemannLabs.Bridge

/-- The multiplicity-weighted zeta-zero count, regarded as a real-valued interval function. -/
noncomputable def countWindow (a b : ℝ) : ℝ :=
  (Zeta23.Ncount a b : ℝ)

/-- Real-valued zero counts inherit exact interval additivity. -/
theorem countWindow_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    countWindow a c = countWindow a b + countWindow b c := by
  unfold countWindow
  exact_mod_cast Zeta23.Ncount_add hab hbc

/-- Real-valued zero counts are nonnegative. -/
theorem countWindow_nonneg (a b : ℝ) : 0 ≤ countWindow a b := by
  unfold countWindow
  positivity

/-- Transfer the local RvM lower bound to cumulative zero counts. -/
theorem cumulative_count_ge_scale
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ε) * scaleWindow 0 T ≤ countWindow 0 T := by
  exact dyadicTransfer
    (f := countWindow) (g := scaleWindow) (c := 1)
    (fun a b c hab hbc => countWindow_add hab hbc)
    (fun a b c hab hbc => scaleWindow_add hab hbc)
    countWindow_nonneg scaleWindow_nonneg scaleWindow_zero_tendsto_atTop
    (by
      intro ε hε
      simpa [countWindow] using local_count_ge_scale hR ε hε)

/-- Cumulative zero counts diverge, as a consequence of their cumulative scale lower bound. -/
theorem cumulative_count_tendsto_atTop
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    Tendsto (fun T => countWindow 0 T) atTop atTop := by
  obtain ⟨T₀, hT₀⟩ := cumulative_count_ge_scale hR (1 / 2) (by norm_num)
  have hbound : ∀ᶠ T : ℝ in atTop,
      (1 / 2 : ℝ) * scaleWindow 0 T ≤ countWindow 0 T :=
    Filter.eventually_atTop.2 ⟨T₀, by simpa using hT₀⟩
  exact tendsto_atTop_mono' _ hbound
    (scaleWindow_zero_tendsto_atTop.const_mul_atTop (by norm_num))

/-- Transfer the local reverse RvM inequality to cumulative zero counts. -/
theorem cumulative_scale_ge_count
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ε) * countWindow 0 T ≤ scaleWindow 0 T := by
  exact dyadicTransfer
    (f := scaleWindow) (g := countWindow) (c := 1)
    (fun a b c hab hbc => scaleWindow_add hab hbc)
    (fun a b c hab hbc => countWindow_add hab hbc)
    scaleWindow_nonneg countWindow_nonneg (cumulative_count_tendsto_atTop hR)
    (by
      intro ε hε
      simpa [countWindow] using local_scale_ge_count hR ε hε)

/-- Zeta23's dyadic RvM package implies Axiom's cumulative normalized RvM statement. -/
theorem cumulativeRiemannVonMangoldt_of_rvm
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    CumulativeRiemannVonMangoldt := by
  intro ε hε
  let δ : ℝ := min (1 / 4) (ε / 4)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  have hδquarter : δ ≤ 1 / 4 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδε : δ ≤ ε / 4 := by
    dsimp [δ]
    exact min_le_right _ _
  have hδltε : δ < ε := by nlinarith
  have h2δltε : 2 * δ < ε := by nlinarith
  obtain ⟨T₁, hlower⟩ := cumulative_count_ge_scale hR δ hδpos
  obtain ⟨T₂, hupper⟩ := cumulative_scale_ge_count hR δ hδpos
  refine ⟨max 2 (max T₁ T₂), ?_⟩
  intro T hT
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hTrest : max T₁ T₂ ≤ T := (le_max_right _ _).trans hT
  have hT₁ : T₁ ≤ T := (le_max_left _ _).trans hTrest
  have hT₂ : T₂ ≤ T := (le_max_right _ _).trans hTrest
  have hT1 : 1 < T := by linarith
  have hs : 0 < scaleWindow 0 T := by
    rw [scaleWindow_zero_eq hT1]
    exact mul_pos (div_pos (by linarith) (by positivity)) (Real.log_pos hT1)
  have hn : 0 ≤ countWindow 0 T := countWindow_nonneg _ _
  have hlower := hlower T hT₁
  have hupper := hupper T hT₂
  have hhalfcoef : (1 / 2 : ℝ) ≤ 1 - δ := by nlinarith
  have hhalf : (1 / 2 : ℝ) * countWindow 0 T ≤ scaleWindow 0 T :=
    (mul_le_mul_of_nonneg_right hhalfcoef hn).trans hupper
  have hn2s : countWindow 0 T ≤ 2 * scaleWindow 0 T := by nlinarith
  have hlowerDiff : scaleWindow 0 T - countWindow 0 T ≤ δ * scaleWindow 0 T := by
    linarith
  have hupperDiff0 : countWindow 0 T - scaleWindow 0 T ≤ δ * countWindow 0 T := by
    linarith
  have hδn : δ * countWindow 0 T ≤ δ * (2 * scaleWindow 0 T) :=
    mul_le_mul_of_nonneg_left hn2s hδpos.le
  have hupperDiff :
      countWindow 0 T - scaleWindow 0 T ≤ 2 * δ * scaleWindow 0 T := by
    calc
      countWindow 0 T - scaleWindow 0 T ≤ δ * countWindow 0 T := hupperDiff0
      _ ≤ δ * (2 * scaleWindow 0 T) := hδn
      _ = 2 * δ * scaleWindow 0 T := by ring
  have hδslt : δ * scaleWindow 0 T < ε * scaleWindow 0 T :=
    mul_lt_mul_of_pos_right hδltε hs
  have h2δslt : 2 * δ * scaleWindow 0 T < ε * scaleWindow 0 T :=
    mul_lt_mul_of_pos_right h2δltε hs
  have habs :
      |countWindow 0 T - scaleWindow 0 T| < ε * scaleWindow 0 T := by
    rw [abs_lt]
    constructor
    · linarith
    · exact hupperDiff.lt_trans h2δslt
  rw [← scaleWindow_zero_eq hT1]
  change |countWindow 0 T / scaleWindow 0 T - 1| < ε
  have hratio :
      countWindow 0 T / scaleWindow 0 T - 1 =
        (countWindow 0 T - scaleWindow 0 T) / scaleWindow 0 T := by
    field_simp [hs.ne']
  rw [hratio, abs_div, abs_of_pos hs]
  exact (div_lt_iff₀ hs).2 habs

/-- The completed dyadic-to-cumulative adapter promised by the bridge interface. -/
theorem dyadicToCumulativeRvM : DyadicToCumulativeRvM :=
  fun hR => cumulativeRiemannVonMangoldt_of_rvm hR

/-- Axiom's Riemann--von Mangoldt input is now discharged by Zeta23. -/
theorem axiomRiemannVonMangoldt : ZetaZeros.RiemannVonMangoldt :=
  axiomRiemannVonMangoldt_of_dyadicTransfer dyadicToCumulativeRvM

end RiemannLabs.Bridge
