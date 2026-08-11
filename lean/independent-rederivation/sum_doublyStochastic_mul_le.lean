import Mathlib

/-!
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace Zeta23Redux.LinAlg

variable {d : ℕ}

/-- A bilinear form against a doubly stochastic matrix is bounded by the "sorted" pairing,
when both weight vectors are listed in the same (decreasing) order.

This is the Birkhoff + rearrangement step of von Neumann's trace inequality. -/
theorem sum_doublyStochastic_mul_le {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin d)) {mu nu : Fin d → ℝ}
    (hmu : Antitone mu) (hnu : Antitone nu) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hw2⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hmono : Monovary mu nu := fun i j h =>
    hmu (le_of_lt (lt_of_not_ge (fun hij => absurd (hnu hij) (not_le.2 h))))
  have hperm : ∀ σ : Equiv.Perm (Fin d),
      ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) = ∑ i, mu i * nu (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have expand : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j) := by
    rw [← hw2]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm (γ := Equiv.Perm (Fin d))]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  rw [expand]
  calc ∑ σ : Equiv.Perm (Fin d), w σ * ∑ i, ∑ j, (σ.permMatrix ℝ) i j * (mu i * nu j)
      ≤ ∑ _σ : Equiv.Perm (Fin d), w _σ * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun σ _ => ?_
        rw [hperm σ]
        exact mul_le_mul_of_nonneg_left hmono.sum_mul_comp_perm_le_sum_mul (hw0 σ)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- The trace of `Dₐ W D_b W*` (with `Dₐ`, `D_b` real diagonal matrices) expressed through the
entrywise squared moduli of `W`. -/
theorem trace_diag_conj (W : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d → ℝ) :
    Matrix.trace (diagonal (fun i => (a i : ℂ)) * W * diagonal (fun j => (b j : ℂ)) * star W)
      = ((∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero, Finset.sum_ite_eq,
    RCLike.star_def]
  linear_combination ((a i : ℂ) * (b j : ℂ)) * (Complex.mul_conj (W i j))

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
theorem normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  obtain ⟨h1, h2⟩ := hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h : (W * star W) i i = (1 : Matrix (Fin d) (Fin d) ℂ) i i := by rw [h2]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq, Complex.mul_conj] at h
    exact_mod_cast (by exact_mod_cast h : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = 1)
  · have h : (star W * W) j j = (1 : Matrix (Fin d) (Fin d) ℂ) j j := by rw [h1]
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, RCLike.star_def, Matrix.one_apply_eq,
      ← Complex.normSq_eq_conj_mul_self] at h
    exact_mod_cast (by exact_mod_cast h : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = 1)

/-- Simultaneous diagonalisation step: the trace of a product of two Hermitian matrices is the
trace of `Dₐ W D_b W*`, where `W` is the unitary relating the two eigenbases. -/
theorem trace_mul_eq_trace_diag_conj {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) = Matrix.trace
      (diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))
        * (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
            * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))
        * diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ))
        * star (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
            * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))) := by
  conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_mul, star_star, Function.comp_def,
    mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]
  rfl

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in the same (decreasing) order, then
`Re (tr (A * B)) ≤ ∑ i, mu i * nu i`. -/
theorem vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {mu nu : Fin d → ℝ}
    (hmu : ∃ σ : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ σ)
    (hnu : ∃ τ : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ τ)
    (hmu' : Antitone mu) (hnu' : Antitone nu) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, rfl⟩ := hmu
  obtain ⟨τ, rfl⟩ := hnu
  set a := hA.eigenvalues
  set b := hB.eigenvalues
  set W : Matrix (Fin d) (Fin d) ℂ :=
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
      * (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hWu : W ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
    mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  -- the trace is the real number `∑ i, ∑ j, |W i j|² * (a i * b j)`
  have htrace : (Matrix.trace (A * B)).re
      = ∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j) := by
    rw [trace_mul_eq_trace_diag_conj hA hB, trace_diag_conj W a b, Complex.ofReal_re]
  -- the doubly stochastic matrix obtained from `W`, reindexed by the two sorting permutations
  have hS0 : (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) :=
    normSq_mem_doublyStochastic hWu
  rw [mem_doublyStochastic_iff_sum] at hS0
  obtain ⟨hn, hr, hc⟩ := hS0
  have hS : (Matrix.of fun i j => Complex.normSq (W (σ i) (τ j)))
      ∈ doublyStochastic ℝ (Fin d) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => hn (σ i) (τ j), fun i => ?_, fun j => ?_⟩
    · simpa using (Equiv.sum_comp τ (fun j => Complex.normSq (W (σ i) j))).trans (hr (σ i))
    · simpa using (Equiv.sum_comp σ (fun i => Complex.normSq (W i (τ j)))).trans (hc (τ j))
  have hreindex : ∑ i, ∑ j, Complex.normSq (W i j) * (a i * b j)
      = ∑ i, ∑ j, Complex.normSq (W (σ i) (τ j)) * ((a ∘ σ) i * (b ∘ τ) j) := by
    rw [← Equiv.sum_comp σ (fun i => ∑ j, Complex.normSq (W i j) * (a i * b j))]
    exact Finset.sum_congr rfl fun i _ =>
      (Equiv.sum_comp τ (fun j => Complex.normSq (W (σ i) j) * (a (σ i) * b j))).symm
  rw [htrace, hreindex]
  exact sum_doublyStochastic_mul_le hS hmu' hnu'

/-- Any finite tuple of reals admits a decreasing rearrangement; in particular the hypotheses of
`vonNeumann_trace_ineq` are satisfiable (applied to the eigenvalue tuples). -/
theorem exists_antitone_perm (f : Fin d → ℝ) : ∃ σ : Equiv.Perm (Fin d), Antitone (f ∘ σ) := by
  refine ⟨Tuple.sort fun i => -f i, fun i j hij => ?_⟩
  simpa using Tuple.monotone_sort (fun i => -f i) hij

/-- Von Neumann's trace inequality, stated with the decreasing rearrangements of the eigenvalues
produced explicitly. -/
theorem exists_vonNeumann_trace_ineq {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ mu nu : Fin d → ℝ, (∃ σ : Equiv.Perm (Fin d), mu = hA.eigenvalues ∘ σ) ∧
      (∃ τ : Equiv.Perm (Fin d), nu = hB.eigenvalues ∘ τ) ∧ Antitone mu ∧ Antitone nu ∧
      (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨σ, hσ⟩ := exists_antitone_perm hA.eigenvalues
  obtain ⟨τ, hτ⟩ := exists_antitone_perm hB.eigenvalues
  exact ⟨hA.eigenvalues ∘ σ, hB.eigenvalues ∘ τ, ⟨σ, rfl⟩, ⟨τ, rfl⟩, hσ, hτ,
    vonNeumann_trace_ineq hA hB ⟨σ, rfl⟩ ⟨τ, rfl⟩ hσ hτ⟩

end Zeta23Redux.LinAlg

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

