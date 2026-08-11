/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive
eigenvalues (counted with multiplicity, i.e. as a cardinality of indices). -/
noncomputable def posIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The spectral theorem in the form `A = U * diagonal μ * Uᴴ`. -/
lemma spectral_conjTranspose {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose] using h

/-- Diagonalisation of the Hermitian quadratic form: if `A = U * diagonal μ * Uᴴ` then
`Re (star x ⬝ᵥ A *ᵥ x) = ∑ i, μ i * ‖(Uᴴ *ᵥ x) i‖²`. -/
lemma re_quadraticForm_eq_sum {d : ℕ} (U A : Matrix (Fin d) (Fin d) ℂ) (μ : Fin d → ℝ)
    (hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ μ) * Uᴴ) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, μ i * Complex.normSq ((Uᴴ *ᵥ x) i) := by
  subst hspec
  have h1 : star x ⬝ᵥ (U * Matrix.diagonal (RCLike.ofReal ∘ μ) * Uᴴ) *ᵥ x
      = star (Uᴴ *ᵥ x) ⬝ᵥ (Matrix.diagonal (RCLike.ofReal ∘ μ) *ᵥ (Uᴴ *ᵥ x)) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply,
    RCLike.star_def, Function.comp_apply, Complex.normSq_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.mul_im]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((RCLike.ofReal (μ i) : ℂ)).re = μ i := rfl
  have h3 : ((RCLike.ofReal (μ i) : ℂ)).im = 0 := rfl
  rw [h2, h3]
  ring

/-- **Sylvester's law of inertia** (Hermitian case, the "pull-back does not increase the
positive index" direction).  If the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` associated to a
Hermitian complex matrix `A` is positive definite on a subspace `W`, then the dimension of `W`
is at most the number of strictly positive eigenvalues of `A`. -/
theorem sylvester_hermitian_finrank {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  classical
  set μ : Fin d → ℝ := hA.eigenvalues with hμ
  set S : Finset (Fin d) := Finset.univ.filter fun i => 0 < μ i with hS
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ μ) * Uᴴ := spectral_conjTranspose hA
  -- the linear map sending `x ∈ W` to the coordinates of `Uᴴ *ᵥ x` indexed by `S`
  set f : W →ₗ[ℂ] ({i // i ∈ S} → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun i : {i // i ∈ S} => (i : Fin d))).comp
      ((Uᴴ).mulVecLin.comp W.subtype) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ hker
    have hzero : ∀ i ∈ S, (Uᴴ *ᵥ x) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.mp hker) ⟨i, hi⟩
      simpa [hf, LinearMap.funLeft_apply] using this
    have hle : (star x ⬝ᵥ A *ᵥ x).re ≤ 0 := by
      rw [re_quadraticForm_eq_sum U A μ hspec x]
      refine Finset.sum_nonpos fun i _ => ?_
      by_cases hi : i ∈ S
      · rw [hzero i hi]
        simp
      · have hμi : μ i ≤ 0 := by
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
          exact hi
        have hn : 0 ≤ Complex.normSq ((Uᴴ *ᵥ x) i) := Complex.normSq_nonneg _
        nlinarith
    have hx0 : x = 0 := by
      by_contra hne
      exact absurd hle (not_le.mpr (hW x hx hne))
    exact Submodule.mk_eq_zero _ _ |>.mpr hx0
  have h1 : Module.finrank ℂ W ≤ Module.finrank ℂ ({i // i ∈ S} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank ℂ ({i // i ∈ S} → ℂ) = S.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rw [h2] at h1
  simpa [posIndex, hS, hμ] using h1

end Zeta23Redux.LinAlg

