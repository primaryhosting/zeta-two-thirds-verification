/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
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

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/
lemma normSq_unitary_mem_doublyStochastic {W : Matrix n n ℂ}
    (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ n := by
  have h1 : W * star W = 1 := Unitary.mul_star_self_of_mem hW
  have h2 : star W * W = 1 := Unitary.star_mul_self_of_mem hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have hii := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at hii
    simp only [Matrix.star_apply, Matrix.one_apply_eq] at hii
    have h3 : ∑ j, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [← hii]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.mul_conj]
    exact_mod_cast h3
  · have hjj := congrFun (congrFun h2 j) j
    rw [Matrix.mul_apply] at hjj
    simp only [Matrix.star_apply, Matrix.one_apply_eq] at hjj
    have h3 : ∑ i, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [← hjj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    exact_mod_cast h3

/-- Rearrangement + Birkhoff: a bilinear form of two monovarying families against a doubly
stochastic matrix is bounded by the aligned sum. -/
lemma sum_bilinear_le_of_doublyStochastic {mu nu : n → ℝ} (h : Monovary mu nu)
    {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ i, ∑ j, S i j * (mu i * nu j) ≤ ∑ i, mu i * nu i := by
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hSij : ∀ i j, S i j = ∑ sg : Equiv.Perm n, (if sg i = j then w sg else 0) := by
    intro i j
    rw [← hw]
    simp [Matrix.sum_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∑ i, ∑ j, S i j * (mu i * nu j)
      = ∑ sg : Equiv.Perm n, w sg * ∑ i, mu i * nu (sg i) := by
    have step : ∀ i : n, ∑ j, S i j * (mu i * nu j)
        = ∑ sg : Equiv.Perm n, w sg * (mu i * nu (sg i)) := by
      intro i
      simp only [hSij, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun sg _ => ?_
      simp
    simp only [step]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun sg _ => by rw [Finset.mul_sum]
  rw [key]
  calc ∑ sg : Equiv.Perm n, w sg * ∑ i, mu i * nu (sg i)
      ≤ ∑ _sg : Equiv.Perm n, w _sg * ∑ i, mu i * nu i := by
        refine Finset.sum_le_sum fun sg _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hw0 sg)
        simpa [smul_eq_mul] using h.sum_smul_comp_perm_le_sum_smul (σ := sg)
    _ = ∑ i, mu i * nu i := by rw [← Finset.sum_mul, hw1, one_mul]

/-- Entrywise expansion of the trace of `Wᴴ Dₐ W D_b`. -/
lemma trace_star_diag_mul_diag (W : Matrix n n ℂ) (a b : n → ℝ) :
    Matrix.trace (star W * Matrix.diagonal (fun i => (a i : ℂ)) * W *
        Matrix.diagonal (fun j => (b j : ℂ)))
      = ∑ j, ∑ i, ((Complex.normSq (W i j) * (a i * b j) : ℝ) : ℂ) := by
  have h : star W * Matrix.diagonal (fun i => (a i : ℂ)) * W *
        Matrix.diagonal (fun j => (b j : ℂ))
      = (star W * Matrix.diagonal (fun i => (a i : ℂ))) *
        (W * Matrix.diagonal (fun j => (b j : ℂ))) := by
    simp [mul_assoc]
  rw [h, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.star_apply]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Reduction of the trace of a product of two diagonalised matrices. -/
lemma trace_conj_mul_conj (U V : Matrix n n ℂ) (a b : n → ℝ) :
    Matrix.trace ((U * Matrix.diagonal (fun i => (a i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun j => (b j : ℂ)) * star V))
      = Matrix.trace (star (star U * V) * Matrix.diagonal (fun i => (a i : ℂ)) * (star U * V) *
        Matrix.diagonal (fun j => (b j : ℂ))) := by
  set Da := Matrix.diagonal (fun i => (a i : ℂ))
  set Db := Matrix.diagonal (fun j => (b j : ℂ))
  have h1 : (U * Da * star U) * (V * Db * star V) = (U * Da * star U * V * Db) * star V := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.star_mul, star_star]
  simp [mul_assoc]

/--
**Von Neumann's trace inequality** for Hermitian complex matrices.

If `A` and `B` are Hermitian matrices of size `d`, and `mu`, `nu` are the eigenvalues of `A` and
`B` respectively (each an arbitrary rearrangement of the eigenvalue list), both listed in the same
monotone (decreasing) order, then `Re (tr (A * B)) ≤ ∑ i, mu i * nu i`.
-/
theorem vonNeumann_trace_ineq {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (mu nu : Fin d → ℝ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hmuA : ∃ sg : Equiv.Perm (Fin d), ∀ i, mu i = hA.eigenvalues (sg i))
    (hnuB : ∃ tu : Equiv.Perm (Fin d), ∀ i, nu i = hB.eigenvalues (tu i)) :
    (Matrix.trace (A * B)).re ≤ ∑ i, mu i * nu i := by
  obtain ⟨sg, hsg⟩ := hmuA
  obtain ⟨tu, htu⟩ := hnuB
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hUdef
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hVdef
  set W : Matrix (Fin d) (Fin d) ℂ := star U * V with hWdef
  have hWmem : W ∈ Matrix.unitaryGroup (Fin d) ℂ :=
    mul_mem (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  have hAeq : A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hBeq : B = V * Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have htr : Matrix.trace (A * B) = ∑ j, ∑ i,
      ((Complex.normSq (W i j) * (hA.eigenvalues i * hB.eigenvalues j) : ℝ) : ℂ) := by
    conv_lhs => rw [hAeq, hBeq]
    rw [trace_conj_mul_conj U V, ← hWdef]
    exact trace_star_diag_mul_diag W _ _
  have hre : (Matrix.trace (A * B)).re
      = ∑ i, ∑ j, Complex.normSq (W i j) * (hA.eigenvalues i * hB.eigenvalues j) := by
    rw [htr, Complex.re_sum]
    simp only [Complex.re_sum, Complex.ofReal_re]
    exact Finset.sum_comm
  set S : Matrix (Fin d) (Fin d) ℝ :=
    (Matrix.of fun i j => Complex.normSq (W i j)).reindex sg.symm tu.symm with hSdef
  have hSmem : S ∈ doublyStochastic ℝ (Fin d) :=
    reindex_mem_doublyStochastic (normSq_unitary_mem_doublyStochastic hWmem)
  have hSapply : ∀ i j, S i j = Complex.normSq (W (sg i) (tu j)) := fun i j => rfl
  have hreindex : (Matrix.trace (A * B)).re = ∑ i, ∑ j, S i j * (mu i * nu j) := by
    rw [hre]
    have hinner : ∀ i : Fin d,
        ∑ j, Complex.normSq (W i j) * (hA.eigenvalues i * hB.eigenvalues j)
          = ∑ j, Complex.normSq (W i (tu j)) * (hA.eigenvalues i * hB.eigenvalues (tu j)) :=
      fun i => (Equiv.sum_comp tu
        (fun j => Complex.normSq (W i j) * (hA.eigenvalues i * hB.eigenvalues j))).symm
    rw [Finset.sum_congr rfl fun i _ => hinner i]
    rw [← Equiv.sum_comp sg
      (fun i => ∑ j, Complex.normSq (W i (tu j)) * (hA.eigenvalues i * hB.eigenvalues (tu j)))]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hSapply, hsg i, htu j]
  have hmono : Monovary mu nu := by
    intro i j hij
    rcases le_or_gt i j with hle | hlt
    · exact absurd (hnu hle) (not_le.2 hij)
    · exact hmu hlt.le
  rw [hreindex]
  exact sum_bilinear_le_of_doublyStochastic hmono hSmem

/-- The eigenvalues of a Hermitian `d × d` matrix, listed in decreasing order. -/
noncomputable def sortedEigenvalues {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : Fin d → ℝ :=
  fun i => hA.eigenvalues₀ (finCongr (Fintype.card_fin d).symm i)

lemma sortedEigenvalues_antitone {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    Antitone (sortedEigenvalues hA) :=
  hA.eigenvalues₀_antitone.comp_monotone (fun _ _ hij => hij)

/-- `sortedEigenvalues hA` is a rearrangement of `hA.eigenvalues`. -/
lemma sortedEigenvalues_eq_comp_perm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    ∃ sg : Equiv.Perm (Fin d), ∀ i, sortedEigenvalues hA i = hA.eigenvalues (sg i) := by
  refine ⟨(finCongr (Fintype.card_fin d).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)), fun i => ?_⟩
  simp [sortedEigenvalues, Matrix.IsHermitian.eigenvalues]

/-- **Von Neumann's trace inequality**, stated with the eigenvalues of both matrices listed in
decreasing order. -/
theorem vonNeumann_trace_ineq_sorted {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).re ≤ ∑ i, sortedEigenvalues hA i * sortedEigenvalues hB i :=
  vonNeumann_trace_ineq hA hB _ _ (sortedEigenvalues_antitone hA) (sortedEigenvalues_antitone hB)
    (sortedEigenvalues_eq_comp_perm hA) (sortedEigenvalues_eq_comp_perm hB)

end Zeta23Redux.LinAlg

