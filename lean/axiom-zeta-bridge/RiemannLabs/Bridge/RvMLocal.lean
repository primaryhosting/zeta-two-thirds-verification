/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
import RiemannLabs.Bridge.DyadicTransfer
import Zeta23.RvM.Statement

open Filter Topology

noncomputable section

namespace RiemannLabs.Bridge

/-- The dyadic main term appearing in Zeta23's Riemann--von Mangoldt package. -/
noncomputable def rvmMain (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Zeta23.ell1 T

/-- The leading `T log T` part is bounded above by the exact additive scale window. -/
theorem dyadicBase_le_scale {T : ℝ} (hT : 1 < T) :
    T / (2 * Real.pi) * Real.log T ≤ scaleWindow T (2 * T) := by
  rw [scaleWindow_dyadic hT]
  apply mul_le_mul_of_nonneg_left
  · have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · positivity

/--
The dyadic zeta-zero count differs from the additive scale window by an arbitrarily small
relative error. This is the local analytic input consumed by the abstract dyadic transfer.
-/
theorem local_rvm_abs_sub_scale
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₁ : ℝ, ∀ T ≥ T₁,
      |(Zeta23.Ncount T (2 * T) : ℝ) - scaleWindow T (2 * T)|
        ≤ ε * scaleWindow T (2 * T) := by
  obtain ⟨C, T₀, hmain⟩ := hR.main
  let K : ℝ := Real.log (2 * Real.pi) + 1
  have h2pi : 1 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hKpos : 0 < K := by
    dsimp [K]
    linarith [Real.log_pos h2pi]
  refine ⟨max T₀
      (max 2
        (max (4 * Real.pi * |C| / ε)
          (Real.exp (2 * K / ε)))), ?_⟩
  intro T hT
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hTrest :
      max 2 (max (4 * Real.pi * |C| / ε) (Real.exp (2 * K / ε))) ≤ T :=
    (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hTrest
  have hTbounds :
      max (4 * Real.pi * |C| / ε) (Real.exp (2 * K / ε)) ≤ T :=
    (le_max_right _ _).trans hTrest
  have hTC : 4 * Real.pi * |C| / ε ≤ T := (le_max_left _ _).trans hTbounds
  have hTexp : Real.exp (2 * K / ε) ≤ T := (le_max_right _ _).trans hTbounds
  have hT1 : 1 < T := by linarith
  have hTpos : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1.le
  have hmainT :
      |(Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T| ≤ C * Real.log T := by
    simpa [rvmMain] using hmain T hT₀
  have hmainAbs :
      |(Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T| ≤ |C| * Real.log T :=
    hmainT.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
  have hscaleMain :
      scaleWindow T (2 * T) - rvmMain T = T / (2 * Real.pi) * K := by
    simpa [rvmMain, K] using scaleWindow_sub_rvmMain hT1
  have hscaleMainNonneg : 0 ≤ scaleWindow T (2 * T) - rvmMain T := by
    rw [hscaleMain]
    exact mul_nonneg (div_nonneg hTpos.le (by positivity)) hKpos.le
  have habsMainScale :
      |rvmMain T - scaleWindow T (2 * T)| =
        scaleWindow T (2 * T) - rvmMain T := by
    rw [abs_sub_comm, abs_of_nonneg hscaleMainNonneg]
  have hCcoef : |C| ≤ ε / 2 * (T / (2 * Real.pi)) := by
    calc
      |C| = (ε / (4 * Real.pi)) * (4 * Real.pi * |C| / ε) := by
        field_simp [hε.ne', Real.pi_ne_zero]
      _ ≤ (ε / (4 * Real.pi)) * T :=
        mul_le_mul_of_nonneg_left hTC (by positivity)
      _ = ε / 2 * (T / (2 * Real.pi)) := by ring
  have hCsmall :
      |C| * Real.log T ≤ ε / 2 * scaleWindow T (2 * T) := by
    calc
      |C| * Real.log T ≤
          (ε / 2 * (T / (2 * Real.pi))) * Real.log T :=
        mul_le_mul_of_nonneg_right hCcoef hlog0
      _ = ε / 2 * (T / (2 * Real.pi) * Real.log T) := by ring
      _ ≤ ε / 2 * scaleWindow T (2 * T) :=
        mul_le_mul_of_nonneg_left (dyadicBase_le_scale hT1) (by positivity)
  have hlogK : 2 * K / ε ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    exact hTexp
  have hKcoef : K ≤ ε / 2 * Real.log T := by
    calc
      K = ε / 2 * (2 * K / ε) := by field_simp [hε.ne']
      _ ≤ ε / 2 * Real.log T :=
        mul_le_mul_of_nonneg_left hlogK (by positivity)
  have hKsmall :
      scaleWindow T (2 * T) - rvmMain T ≤
        ε / 2 * scaleWindow T (2 * T) := by
    rw [hscaleMain]
    calc
      T / (2 * Real.pi) * K ≤
          T / (2 * Real.pi) * (ε / 2 * Real.log T) :=
        mul_le_mul_of_nonneg_left hKcoef (by positivity)
      _ = ε / 2 * (T / (2 * Real.pi) * Real.log T) := by ring
      _ ≤ ε / 2 * scaleWindow T (2 * T) :=
        mul_le_mul_of_nonneg_left (dyadicBase_le_scale hT1) (by positivity)
  have htriangle :
      |(Zeta23.Ncount T (2 * T) : ℝ) - scaleWindow T (2 * T)| ≤
        |(Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T| +
          |rvmMain T - scaleWindow T (2 * T)| := by
    calc
      |(Zeta23.Ncount T (2 * T) : ℝ) - scaleWindow T (2 * T)| =
          |((Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T) +
            (rvmMain T - scaleWindow T (2 * T))| := by ring
      _ ≤ |(Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T| +
          |rvmMain T - scaleWindow T (2 * T)| := abs_add _ _
  calc
    |(Zeta23.Ncount T (2 * T) : ℝ) - scaleWindow T (2 * T)|
        ≤ |(Zeta23.Ncount T (2 * T) : ℝ) - rvmMain T| +
          |rvmMain T - scaleWindow T (2 * T)| := htriangle
    _ ≤ |C| * Real.log T + (scaleWindow T (2 * T) - rvmMain T) :=
      add_le_add hmainAbs habsMainScale.le
    _ ≤ ε / 2 * scaleWindow T (2 * T) +
        ε / 2 * scaleWindow T (2 * T) := add_le_add hCsmall hKsmall
    _ = ε * scaleWindow T (2 * T) := by ring

/-- Eventual dyadic lower bound of the zero count by the additive scale. -/
theorem local_count_ge_scale
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∀ ε > 0, ∃ T₁ : ℝ, ∀ T ≥ T₁,
      (1 - ε) * scaleWindow T (2 * T) ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := local_rvm_abs_sub_scale hR ε hε
  refine ⟨T₁, fun T hT => ?_⟩
  have hlo := (abs_le.mp (hT₁ T hT)).1
  linarith

/-- Eventual dyadic lower bound of the additive scale by the zero count. -/
theorem local_scale_ge_count
    (hR : Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig) :
    ∀ ε > 0, ∃ T₁ : ℝ, ∀ T ≥ T₁,
      (1 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ scaleWindow T (2 * T) := by
  intro ε hε
  by_cases hlarge : 1 ≤ ε
  · refine ⟨0, fun T _ => ?_⟩
    have hN : 0 ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by positivity
    have hs := scaleWindow_nonneg T (2 * T)
    nlinarith
  · have hε1 : ε < 1 := lt_of_not_ge hlarge
    obtain ⟨T₁, hT₁⟩ := local_rvm_abs_sub_scale hR (ε / 2) (by positivity)
    refine ⟨T₁, fun T hT => ?_⟩
    have hup := (abs_le.mp (hT₁ T hT)).2
    have hN : 0 ≤ (Zeta23.Ncount T (2 * T) : ℝ) := by positivity
    have hs : 0 ≤ scaleWindow T (2 * T) := scaleWindow_nonneg _ _
    have hcountUpper :
        (Zeta23.Ncount T (2 * T) : ℝ) ≤
          (1 + ε / 2) * scaleWindow T (2 * T) := by
      linarith
    have hfactor : 0 ≤ 1 - ε := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcountUpper hfactor
    have hcoef : (1 - ε) * (1 + ε / 2) ≤ 1 := by nlinarith
    have hscale := mul_le_mul_of_nonneg_right hcoef hs
    calc
      (1 - ε) * (Zeta23.Ncount T (2 * T) : ℝ)
          ≤ (1 - ε) * ((1 + ε / 2) * scaleWindow T (2 * T)) := hmul
      _ = ((1 - ε) * (1 + ε / 2)) * scaleWindow T (2 * T) := by ring
      _ ≤ 1 * scaleWindow T (2 * T) := hscale
      _ = scaleWindow T (2 * T) := one_mul _

end RiemannLabs.Bridge
