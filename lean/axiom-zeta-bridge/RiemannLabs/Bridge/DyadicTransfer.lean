/-
Copyright (c) 2026 Anthropic, PBC.
Adapted by Riemann Labs from `Zeta23/Assembly.lean` under the Apache 2.0 license.
-/
import RiemannLabs.Bridge.RvMScale
import Mathlib.Algebra.Order.Archimedean.Basic

open Filter Topology

noncomputable section

namespace RiemannLabs.Bridge

/--
Transfer an eventual lower bound on every dyadic interval `(t, 2t]` to the corresponding
cumulative lower bound on `(0, T]`. The two interval functions need only be additive,
nonnegative, and the comparison denominator must diverge cumulatively.
-/
theorem dyadicTransfer {f g : ℝ → ℝ → ℝ} {c : ℝ}
    (hf_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → f a c = f a b + f b c)
    (hg_add : ∀ a b c : ℝ, a ≤ b → b ≤ c → g a c = g a b + g b c)
    (hf_nn : ∀ a b, 0 ≤ f a b) (hg_nn : ∀ a b, 0 ≤ g a b)
    (hg_top : Tendsto (fun T => g 0 T) atTop atTop)
    (h : ∀ ε > 0, ∃ T₁, ∀ t ≥ T₁, (c - ε) * g t (2 * t) ≤ f t (2 * t)) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * g 0 T ≤ f 0 T := by
  intro ε hε
  by_cases hc : c - ε / 2 < 0
  · refine ⟨0, fun T _ => ?_⟩
    have := hg_nn 0 T
    have := hf_nn 0 T
    nlinarith
  have hc : 0 ≤ c - ε / 2 := not_lt.mp hc
  obtain ⟨T₁', hT₁'⟩ := h (ε / 2) (by linarith)
  set T₁ := max T₁' 1 with hT₁def
  have hT₁ : ∀ t ≥ T₁, (c - ε / 2) * g t (2 * t) ≤ f t (2 * t) :=
    fun t ht => hT₁' t ((le_max_left _ _).trans ht)
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hg_mono : ∀ a b b', a ≤ b → b ≤ b' → g a b ≤ g a b' := by
    intro a b b' hab hbb'
    rw [hg_add a b b' hab hbb']
    linarith [hg_nn b b']
  have key : ∀ n : ℕ, ∀ t ≥ T₁, (c - ε / 2) * g t (2 ^ n * t) ≤ f t (2 ^ n * t) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have hf0 : f t t = 0 := by
        have := hf_add t t t le_rfl le_rfl
        linarith
      have hg0 : g t t = 0 := by
        have := hg_add t t t le_rfl le_rfl
        linarith
      simp [hf0, hg0]
    | succ n ih =>
      intro t ht
      have ht0 : 0 ≤ t := hT₁pos.le.trans ht
      have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hmid : t ≤ 2 ^ n * t := by nlinarith
      have hmid' : 2 ^ n * t ≤ 2 ^ (n + 1) * t := by
        rw [pow_succ]
        nlinarith
      rw [hf_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid',
        hg_add t (2 ^ n * t) (2 ^ (n + 1) * t) hmid hmid']
      have hstep := hT₁ (2 ^ n * t) (ht.trans hmid)
      have e : 2 * (2 ^ n * t) = 2 ^ (n + 1) * t := by
        rw [pow_succ]
        ring
      rw [e] at hstep
      have := ih t ht
      linarith
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (hg_top.eventually_ge_atTop ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hTT₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 ≤ T := hT₁pos.le.trans hTT₁
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := T / T₁)
    ((one_le_div hT₁pos).2 hTT₁) one_lt_two
  set t := T / 2 ^ n with htdef
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have htT₁ : T₁ ≤ t := by
    rw [htdef, le_div_iff₀ h2n]
    rw [le_div_iff₀ hT₁pos] at hn1
    linarith
  have ht2T₁ : t ≤ 2 * T₁ := by
    rw [htdef, div_le_iff₀ h2n]
    rw [div_lt_iff₀ hT₁pos, pow_succ] at hn2
    linarith
  have hTt : 2 ^ n * t = T := by
    rw [htdef]
    field_simp
  have ht0 : 0 ≤ t := hT₁pos.le.trans htT₁
  have htT : t ≤ T := by
    rw [← hTt]
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := n) (by norm_num)]
  have hk := key n t htT₁
  rw [hTt] at hk
  have hf0T : f t T ≤ f 0 T := by
    rw [hf_add 0 t T ht0 htT]
    linarith [hf_nn 0 t]
  have hgsplit : g t T = g 0 T - g 0 t := by
    rw [hg_add 0 t T ht0 htT]
    ring
  have hg0t : g 0 t ≤ g 0 (2 * T₁) := hg_mono 0 t (2 * T₁) ht0 ht2T₁
  have hbig : (c - ε / 2) * g 0 (2 * T₁) * (2 / ε) ≤ g 0 T :=
    hT₂ T ((le_max_right _ _).trans hT)
  have hbig' : (c - ε / 2) * g 0 (2 * T₁) ≤ ε / 2 * g 0 T := by
    have hmul := mul_le_mul_of_nonneg_left hbig (by linarith : 0 ≤ ε / 2)
    calc
      (c - ε / 2) * g 0 (2 * T₁) =
          ε / 2 * ((c - ε / 2) * g 0 (2 * T₁) * (2 / ε)) := by
            field_simp
      _ ≤ ε / 2 * g 0 T := hmul
  calc
    (c - ε) * g 0 T = (c - ε / 2) * g 0 T - ε / 2 * g 0 T := by ring
    _ ≤ (c - ε / 2) * g 0 T - (c - ε / 2) * g 0 (2 * T₁) := by linarith
    _ ≤ (c - ε / 2) * (g 0 T - g 0 t) := by nlinarith
    _ = (c - ε / 2) * g t T := by rw [hgsplit]
    _ ≤ f t T := hk
    _ ≤ f 0 T := hf0T

end RiemannLabs.Bridge
