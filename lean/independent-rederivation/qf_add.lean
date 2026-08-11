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

/-
# Weyl Pos Index Above
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.weyl_posIndexAbove
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

open Matrix Finset Module

variable {d : ℕ}

/-- The quadratic form `x ↦ Re ⟪x, M x⟫` associated with a matrix `M`, on `EuclideanSpace ℂ (Fin d)`.
-/
noncomputable def qf (M : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) : ℝ :=
  RCLike.re (inner ℂ x (Matrix.toLpLin 2 2 M x))

lemma qf_add (M N : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf, map_add]

/-- `‖x‖ ^ 2` expressed via the coordinates of `x` in an orthonormal basis. -/
lemma norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (x : EuclideanSpace ℂ (Fin d)) : ‖x‖ ^ 2 = ∑ j, ‖b.repr x j‖ ^ 2 := by
  rw [← b.repr.norm_map x, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

section

variable {M : Matrix (Fin d) (Fin d) ℂ}

lemma toLpLin_eigenvectorBasis (hM : M.IsHermitian) (j : Fin d) :
    Matrix.toLpLin 2 2 M (hM.eigenvectorBasis j)
      = ((hM.eigenvalues j : ℂ)) • hM.eigenvectorBasis j := by
  rw [Matrix.toLpLin_apply, hM.mulVec_eigenvectorBasis]
  ext i
  simp [Complex.real_smul]

lemma repr_toLpLin (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) (j : Fin d) :
    hM.eigenvectorBasis.repr (Matrix.toLpLin 2 2 M x) j
      = (hM.eigenvalues j : ℂ) * hM.eigenvectorBasis.repr x j := by
  have hsym := Matrix.isHermitian_iff_isSymmetric.1 hM
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have h1 : (inner ℂ (hM.eigenvectorBasis j) (Matrix.toLpLin 2 2 M x) : ℂ)
      = inner ℂ (Matrix.toLpLin 2 2 M (hM.eigenvectorBasis j)) x := (hsym _ _).symm
  rw [h1, toLpLin_eigenvectorBasis hM j, inner_smul_left]
  simp

/-- Diagonalization of the quadratic form of a Hermitian matrix in its eigenbasis. -/
lemma qf_eq_sum (hM : M.IsHermitian) (x : EuclideanSpace ℂ (Fin d)) :
    qf M x = ∑ j, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 := by
  rw [qf, ← hM.eigenvectorBasis.repr.inner_map_map x (Matrix.toLpLin 2 2 M x), PiLp.inner_apply,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [repr_toLpLin hM x j]
  simp only [RCLike.inner_apply]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

/-- If all eigenvalues of a Hermitian matrix are at most `c`, its quadratic form is bounded by
`c * ‖x‖ ^ 2`. -/
lemma qf_le_of_eigenvalues_le (hM : M.IsHermitian) {c : ℝ} (hc : ∀ j, hM.eigenvalues j ≤ c)
    (x : EuclideanSpace ℂ (Fin d)) : qf M x ≤ c * ‖x‖ ^ 2 := by
  rw [qf_eq_sum hM, norm_sq_eq_sum_repr hM.eigenvectorBasis x, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => by
    exact mul_le_mul_of_nonneg_right (hc j) (by positivity)

/-- The span of the eigenvectors of `M` indexed by a finite set `s`. -/
noncomputable def eigSpan (hM : M.IsHermitian) (s : Finset (Fin d)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  Submodule.span ℂ (Set.range fun j : {x // x ∈ s} => hM.eigenvectorBasis j)

lemma finrank_eigSpan (hM : M.IsHermitian) (s : Finset (Fin d)) :
    finrank ℂ (eigSpan hM s) = s.card := by
  have hli : LinearIndependent ℂ (fun j : {x // x ∈ s} => hM.eigenvectorBasis j) :=
    hM.eigenvectorBasis.orthonormal.linearIndependent.comp _ Subtype.val_injective
  rw [eigSpan, finrank_span_eq_card hli, Fintype.card_coe]

lemma repr_eq_zero_of_mem_eigSpan (hM : M.IsHermitian) {s : Finset (Fin d)}
    {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ eigSpan hM s) {j : Fin d} (hj : j ∉ s) :
    hM.eigenvectorBasis.repr x j = 0 := by
  have hle : eigSpan hM s ≤ LinearMap.ker
      ((EuclideanSpace.proj (𝕜 := ℂ) j).toLinearMap.comp
        (hM.eigenvectorBasis.repr.toLinearEquiv.toLinearMap)) := by
    rw [eigSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hij : (i : Fin d) ≠ j := fun h => hj (h ▸ i.2)
    simp [LinearMap.mem_ker, OrthonormalBasis.repr_self, EuclideanSpace.single_apply,
      Ne.symm hij]
  simpa using hle hx

/-- On the span of eigenvectors whose eigenvalues are at most `c`, the quadratic form is bounded
by `c * ‖x‖ ^ 2`. -/
lemma qf_le_of_mem_eigSpan (hM : M.IsHermitian) {s : Finset (Fin d)} {c : ℝ}
    (hc : ∀ j ∈ s, hM.eigenvalues j ≤ c) {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ eigSpan hM s) :
    qf M x ≤ c * ‖x‖ ^ 2 := by
  have hzero : ∀ j ∉ s, hM.eigenvectorBasis.repr x j = 0 := fun j hj =>
    repr_eq_zero_of_mem_eigSpan hM hx hj
  rw [qf_eq_sum hM, norm_sq_eq_sum_repr hM.eigenvectorBasis x, Finset.mul_sum]
  have h1 : ∑ j, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  have h2 : ∑ j, c * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, c * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  rw [h1, h2]
  exact Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hc j hj) (by positivity)

/-- On the span of eigenvectors whose eigenvalues are strictly above `θ`, the quadratic form is
strictly above `θ * ‖x‖ ^ 2` for nonzero vectors. -/
lemma qf_gt_of_mem_eigSpan (hM : M.IsHermitian) {s : Finset (Fin d)} {θ : ℝ}
    (hc : ∀ j ∈ s, θ < hM.eigenvalues j) {x : EuclideanSpace ℂ (Fin d)} (hx : x ∈ eigSpan hM s)
    (hx0 : x ≠ 0) : θ * ‖x‖ ^ 2 < qf M x := by
  have hzero : ∀ j ∉ s, hM.eigenvectorBasis.repr x j = 0 := fun j hj =>
    repr_eq_zero_of_mem_eigSpan hM hx hj
  rw [qf_eq_sum hM, norm_sq_eq_sum_repr hM.eigenvectorBasis x, Finset.mul_sum]
  have h1 : ∑ j, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, hM.eigenvalues j * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  have h2 : ∑ j, θ * ‖hM.eigenvectorBasis.repr x j‖ ^ 2
      = ∑ j ∈ s, θ * ‖hM.eigenvectorBasis.repr x j‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ s) (fun j _ hj => by simp [hzero j hj])).symm
  rw [h1, h2]
  -- there is a coordinate in `s` where `x` does not vanish
  obtain ⟨k, hk⟩ : ∃ k, hM.eigenvectorBasis.repr x k ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : hM.eigenvectorBasis.repr x = 0 := by ext j; simp [h j]
    exact hx0 (hM.eigenvectorBasis.repr.map_eq_zero_iff.mp hz)
  have hks : k ∈ s := by
    by_contra hks
    exact hk (hzero k hks)
  refine Finset.sum_lt_sum (fun j hj => mul_le_mul_of_nonneg_right (hc j hj).le (by positivity))
    ⟨k, hks, ?_⟩
  have : (0:ℝ) < ‖hM.eigenvectorBasis.repr x k‖ ^ 2 := by positivity
  exact mul_lt_mul_of_pos_right (hc k hks) this

end

/-- The number of eigenvalues of a Hermitian matrix that are strictly larger than `θ`. -/
noncomputable def posIndexAbove {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) (θ : ℝ) : ℕ :=
  {i | θ < hA.eigenvalues i}.toFinset.card

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) : ℕ :=
  posIndexAbove hA 0

/-- **Weyl monotonicity**: if all eigenvalues of the Hermitian perturbation `E` have absolute value
at most `θ`, then the number of eigenvalues of `A + E` strictly above `θ` is at most the number of
strictly positive eigenvalues of `A`. -/
theorem weyl_posIndexAbove {d : ℕ} {A E : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hE : E.IsHermitian) (θ : ℝ)
    (hEθ : ∀ i, |hE.eigenvalues i| ≤ θ) :
    posIndexAbove (hA.add hE) θ ≤ posIndex hA := by
  classical
  set hAE : (A + E).IsHermitian := hA.add hE
  set s : Finset (Fin d) := Finset.univ.filter (fun i => θ < hAE.eigenvalues i) with hs
  set t : Finset (Fin d) := Finset.univ.filter (fun i => ¬ (0 < hA.eigenvalues i)) with ht
  set V := eigSpan hAE s with hV
  set W := eigSpan hA t with hW
  -- the two eigenspaces meet trivially
  have hdisj : V ⊓ W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    obtain ⟨hxV, hxW⟩ := Submodule.mem_inf.mp hx
    have h1 : θ * ‖x‖ ^ 2 < qf (A + E) x :=
      qf_gt_of_mem_eigSpan hAE (fun j hj => (Finset.mem_filter.mp hj).2) hxV hx0
    have h2 : qf A x ≤ 0 * ‖x‖ ^ 2 :=
      qf_le_of_mem_eigSpan hA (fun j hj => not_lt.mp (Finset.mem_filter.mp hj).2) hxW
    have h3 : qf E x ≤ θ * ‖x‖ ^ 2 :=
      qf_le_of_eigenvalues_le hE (fun j => (abs_le.mp (hEθ j)).2) x
    rw [qf_add] at h1
    nlinarith [h1, h2, h3]
  -- hence the dimensions add up to at most `d`
  have hsum : finrank ℂ V + finrank ℂ W ≤ d := by
    have hkey := Submodule.finrank_sup_add_finrank_inf_eq V W
    have hle : finrank ℂ (V ⊔ W : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
        ≤ finrank ℂ (EuclideanSpace ℂ (Fin d)) := Submodule.finrank_le _
    rw [hdisj, finrank_bot, add_zero] at hkey
    rw [finrank_euclideanSpace_fin] at hle
    omega
  rw [hV, hW, finrank_eigSpan, finrank_eigSpan] at hsum
  have hcompl : (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card + t.card
      = d := by
    rw [ht, Finset.card_filter_add_card_filter_not]
    simp
  have hposIndex : posIndex hA = (Finset.univ.filter (fun i => 0 < hA.eigenvalues i)).card := by
    rw [posIndex, posIndexAbove, Set.toFinset_setOf]
  have hposAbove : posIndexAbove hAE θ = s.card := by
    rw [posIndexAbove, hs, Set.toFinset_setOf]
  rw [hposAbove, hposIndex]
  omega

end Zeta23Redux.LinAlg

