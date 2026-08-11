import Mathlib

/-!
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- Thresholded Cauchy–Schwarz count at the eigenvalue level (Lemma 3.3).

If `θ ≥ 0` and the total sum of the `d` eigenvalues exceeds `θ * d`, then the excess
`(∑ ev) - θ * d` squared is bounded by `n * ∑ (ev i)^2`, where `n` is the number of
eigenvalues exceeding `θ`. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * d < ∑ i, ev i) :
    ((∑ i, ev i) - theta * d) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  classical
  subst hs hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  -- Rewrite the excess as a sum of `ev i - theta`.
  have hexcess : (∑ i, ev i) - theta * d = ∑ i, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- Split the sum over `s` and its complement.
  have hsplit : ∑ i, (ev i - theta) =
      (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ Finset.univ \ s, (ev i - theta) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    congr 1
    simp [Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  have hcompl : ∑ i ∈ Finset.univ \ s, (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    simp only [Finset.mem_sdiff, hsdef, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hi
    linarith [hi]
  -- Hence the excess is at most the sum over `s`, which is at most `∑_{i∈s} ev i`.
  have hle : (∑ i, ev i) - theta * d ≤ ∑ i ∈ s, ev i := by
    have h1 : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
      apply Finset.sum_le_sum
      intro i _
      linarith
    rw [hexcess, hsplit]
    linarith
  have hpos : 0 < (∑ i, ev i) - theta * d := by linarith
  -- Square both sides, then apply Cauchy-Schwarz on `s`.
  have hsq : ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hpos) hle 2
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  calc ((∑ i, ev i) - theta * d) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := hsq
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 := hcs
    _ ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg _)

end Zeta23Redux.LinAlg

