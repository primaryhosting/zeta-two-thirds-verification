/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
import Zeta23.RvM.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Topology

noncomputable section

namespace RiemannLabs.Bridge

/-- A globally monotone extension of Axiom's cumulative scale `(T / 2π) log T`. -/
noncomputable def cumulativeScale (T : ℝ) : ℝ :=
  if T ≤ 1 then 0 else T / (2 * Real.pi) * Real.log T

@[simp]
theorem cumulativeScale_zero : cumulativeScale 0 = 0 := by
  simp [cumulativeScale]

/-- Above height one, the monotone extension is exactly Axiom's normalizing scale. -/
theorem cumulativeScale_of_one_lt {T : ℝ} (hT : 1 < T) :
    cumulativeScale T = T / (2 * Real.pi) * Real.log T := by
  simp [cumulativeScale, not_le.mpr hT]

/-- The cumulative scale is nonnegative at every real argument. -/
theorem cumulativeScale_nonneg (T : ℝ) : 0 ≤ cumulativeScale T := by
  by_cases hT : T ≤ 1
  · simp [cumulativeScale, hT]
  · have hT1 : 1 < T := lt_of_not_ge hT
    rw [cumulativeScale_of_one_lt hT1]
    exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (Real.log_nonneg hT1.le)

/-- The truncated scale is monotone on the whole real line. -/
theorem cumulativeScale_monotone : Monotone cumulativeScale := by
  intro a b hab
  by_cases hb : b ≤ 1
  · have ha : a ≤ 1 := hab.trans hb
    simp [cumulativeScale, ha, hb]
  · have hb1 : 1 < b := lt_of_not_ge hb
    by_cases ha : a ≤ 1
    · rw [cumulativeScale]
      simp only [if_pos ha, if_neg hb]
      exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (Real.log_nonneg hb1.le)
    · have ha1 : 1 < a := lt_of_not_ge ha
      rw [cumulativeScale_of_one_lt ha1, cumulativeScale_of_one_lt hb1]
      have hdiv : a / (2 * Real.pi) ≤ b / (2 * Real.pi) :=
        div_le_div_of_nonneg_right hab (by positivity)
      have hloga : 0 ≤ Real.log a := Real.log_nonneg ha1.le
      have hlogab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
      exact mul_le_mul hdiv hlogab hloga (div_nonneg (by linarith) (by positivity))

/-- The interval increment of the cumulative scale, made nonnegative outside ordered intervals. -/
noncomputable def scaleWindow (a b : ℝ) : ℝ :=
  max 0 (cumulativeScale b - cumulativeScale a)

/-- Scale windows are nonnegative without an ordering assumption. -/
theorem scaleWindow_nonneg (a b : ℝ) : 0 ≤ scaleWindow a b := by
  exact le_max_left _ _

/-- On an ordered interval, the scale window is the exact difference of endpoints. -/
theorem scaleWindow_eq_sub {a b : ℝ} (hab : a ≤ b) :
    scaleWindow a b = cumulativeScale b - cumulativeScale a := by
  rw [scaleWindow, max_eq_right]
  exact sub_nonneg.mpr (cumulativeScale_monotone hab)

/-- Scale windows are additive on adjacent ordered intervals. -/
theorem scaleWindow_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    scaleWindow a c = scaleWindow a b + scaleWindow b c := by
  rw [scaleWindow_eq_sub (hab.trans hbc), scaleWindow_eq_sub hab, scaleWindow_eq_sub hbc]
  ring

/-- From zero to a large height, the scale window is exactly Axiom's denominator. -/
theorem scaleWindow_zero_eq {T : ℝ} (hT : 1 < T) :
    scaleWindow 0 T = T / (2 * Real.pi) * Real.log T := by
  rw [scaleWindow_eq_sub (by linarith), cumulativeScale_zero, cumulativeScale_of_one_lt hT]
  ring

/-- The cumulative scale diverges. -/
theorem cumulativeScale_tendsto_atTop :
    Tendsto cumulativeScale atTop atTop := by
  have hdiv : Tendsto (fun T : ℝ => T / (2 * Real.pi)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hprod : Tendsto (fun T : ℝ => T / (2 * Real.pi) * Real.log T) atTop atTop :=
    hdiv.atTop_mul_atTop₀ Real.tendsto_log_atTop
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (cumulativeScale_of_one_lt hT).symm

/-- Consequently, the ordered scale window from zero also diverges. -/
theorem scaleWindow_zero_tendsto_atTop :
    Tendsto (fun T : ℝ => scaleWindow 0 T) atTop atTop := by
  apply cumulativeScale_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [scaleWindow_eq_sub (by linarith), cumulativeScale_zero]
  ring

/-- Exact large-height formula for the dyadic scale increment. -/
theorem scaleWindow_dyadic {T : ℝ} (hT : 1 < T) :
    scaleWindow T (2 * T) =
      T / (2 * Real.pi) * (Real.log T + 2 * Real.log 2) := by
  rw [scaleWindow_eq_sub (by nlinarith), cumulativeScale_of_one_lt hT,
    cumulativeScale_of_one_lt (by nlinarith : 1 < 2 * T)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : T ≠ 0)]
  ring

/-- The dyadic scale differs from Zeta23's RvM main term by only a linear correction. -/
theorem scaleWindow_sub_rvmMain {T : ℝ} (hT : 1 < T) :
    scaleWindow T (2 * T) - T / (2 * Real.pi) * Zeta23.ell1 T =
      T / (2 * Real.pi) * (Real.log (2 * Real.pi) + 1) := by
  rw [scaleWindow_dyadic hT]
  unfold Zeta23.ell1 Zeta23.l
  rw [Real.log_div (by linarith : T ≠ 0) (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  ring

end RiemannLabs.Bridge
