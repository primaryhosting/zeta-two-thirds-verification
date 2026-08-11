import Mathlib
/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. over the index set of the matrix). -/
noncomputable def posIndex (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => 0 < hA.eigenvalues i).card

/-- The coordinate of a vector `x` along the `i`-th eigenvector of a Hermitian matrix. -/
noncomputable def eigCoord (hA : A.IsHermitian) (x : Fin d → ℂ) (i : Fin d) : ℂ :=
  star (⇑(hA.eigenvectorBasis i) : Fin d → ℂ) ⬝ᵥ x

/-- Diagonalization of the Hermitian quadratic form in eigenvector coordinates. -/
lemma quadForm_eq_complex (hA : A.IsHermitian) (x : Fin d → ℂ) :
    star x ⬝ᵥ A *ᵥ x = ((∑ i, hA.eigenvalues i * ‖eigCoord hA x i‖ ^ 2 : ℝ) : ℂ) := by
  have hinner : star x ⬝ᵥ A *ᵥ x
      = inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin d)) (WithLp.toLp 2 (A *ᵥ x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct_comm]
  have hY : ∀ i : Fin d, inner ℂ (hA.eigenvectorBasis i)
      (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ (Fin d))
      = (hA.eigenvalues i : ℂ) * eigCoord hA x i := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, dotProduct_mulVec,
      show star (⇑(hA.eigenvectorBasis i) : Fin d → ℂ)
          ᵥ* A = star (A *ᵥ (⇑(hA.eigenvectorBasis i) : Fin d → ℂ)) by rw [star_mulVec, hA.eq],
      hA.mulVec_eigenvectorBasis]
    simp [eigCoord, star_smul, smul_dotProduct]
  have hX : ∀ i : Fin d, inner ℂ (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin d))
      (hA.eigenvectorBasis i) = starRingEnd ℂ (eigCoord hA x i) := by
    intro i
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [eigCoord, star_dotProduct, dotProduct_comm]
  rw [hinner, ← (hA.eigenvectorBasis).sum_inner_mul_inner]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hX, hY]
  have h : (starRingEnd ℂ) (eigCoord hA x i) * eigCoord hA x i
      = ((‖eigCoord hA x i‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq _
  linear_combination (hA.eigenvalues i : ℂ) * h

/-- Diagonalization of the Hermitian quadratic form in eigenvector coordinates (real part). -/
lemma quadForm_eq (hA : A.IsHermitian) (x : Fin d → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).re = ∑ i, hA.eigenvalues i * ‖eigCoord hA x i‖ ^ 2 := by
  rw [quadForm_eq_complex hA x, Complex.ofReal_re]

/-- If all the coordinates of `x` along positive eigenvectors vanish, then the quadratic form
is nonpositive at `x`. -/
lemma quadForm_nonpos_of_eigCoord_eq_zero (hA : A.IsHermitian) (x : Fin d → ℂ)
    (hx : ∀ i, 0 < hA.eigenvalues i → eigCoord hA x i = 0) :
    (star x ⬝ᵥ A *ᵥ x).re ≤ 0 := by
  rw [quadForm_eq hA x]
  refine Finset.sum_nonpos fun i _ => ?_
  rcases lt_or_ge 0 (hA.eigenvalues i) with h | h
  · simp [hx i h]
  · exact mul_nonpos_of_nonpos_of_nonneg h (by positivity)

/-- The eigenvector coordinates along the positive eigenvalues, as a linear map. -/
noncomputable def posCoordMap (hA : A.IsHermitian) :
    (Fin d → ℂ) →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) where
  toFun x i := eigCoord hA x i
  map_add' x y := by
    funext i
    simp [eigCoord, dotProduct_add]
  map_smul' c x := by
    funext i
    simp [eigCoord, dotProduct_smul]

/-- **Sylvester's law of inertia** (Hermitian version, the inequality direction used in the
paper): if the Hermitian form `x ↦ Re (star x ⬝ᵥ A *ᵥ x)` is positive definite on a subspace
`W`, then `finrank W ≤ posIndex A`. -/
theorem sylvester_hermitian_finrank (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  set T : W →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    (posCoordMap hA).comp W.subtype with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : ∀ i, 0 < hA.eigenvalues i → eigCoord hA (x : Fin d → ℂ) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      simpa [hT, posCoordMap] using this
    by_contra hne
    have hxne : (x : Fin d → ℂ) ≠ 0 := by
      simpa [Submodule.coe_eq_zero] using hne
    exact absurd (quadForm_nonpos_of_eigCoord_eq_zero hA _ hx0)
      (not_le.mpr (hW _ x.2 hxne))
  have hle : Module.finrank ℂ W
      ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  calc Module.finrank ℂ W
      ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) := hle
    _ = Fintype.card {i : Fin d // 0 < hA.eigenvalues i} := by
        simp
    _ = posIndex hA := by
        rw [Fintype.card_subtype]
        rfl

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

