import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/
noncomputable def rtrace (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (X.trace).re

/-- The squared Frobenius norm of a matrix, `Re (tr (Xᴴ X))`. -/
noncomputable def frobSq (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * X)).re

/-- The real Frobenius inner product `Re (tr (Xᴴ Y))`. -/
noncomputable def rip (X Y : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * Y)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
noncomputable def posIndex (Q : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if h : Q.IsHermitian then (Finset.univ.filter (fun i => 0 < h.eigenvalues i)).card else 0

/-! ### Basic properties of the Frobenius inner product -/

lemma rip_self (X : Matrix (Fin d) (Fin d) ℂ) : rip X X = frobSq X := rfl

lemma rip_comm (X Y : Matrix (Fin d) (Fin d) ℂ) : rip X Y = rip Y X := by
  unfold rip
  rw [show (Yᴴ * X) = (Xᴴ * Y)ᴴ from by simp, Matrix.trace_conjTranspose]
  simp

lemma frobSq_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ frobSq X :=
  (Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

lemma frobSq_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X + Y) = frobSq X + 2 * rip X Y + frobSq Y := by
  have h := rip_comm X Y
  unfold frobSq rip at *
  simp only [Matrix.conjTranspose_add, add_mul, mul_add, Matrix.trace_add, Complex.add_re]
  linarith

lemma frobSq_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X - Y) = frobSq X - 2 * rip X Y + frobSq Y := by
  have h := rip_comm X Y
  unfold frobSq rip at *
  simp only [Matrix.conjTranspose_sub, sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

lemma rip_smul (X A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    rip X ((t : ℂ) • A) = t * rip X A := by
  unfold rip
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

lemma frobSq_smul (A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    frobSq ((t : ℂ) • A) = t ^ 2 * frobSq A := by
  have h : ((t : ℂ) • A)ᴴ * ((t : ℂ) • A) = ((t ^ 2 : ℝ) : ℂ) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def,
      Complex.conj_ofReal]
    push_cast
    ring_nf
  unfold frobSq
  rw [h, Matrix.trace_smul]
  simp [-Complex.ofReal_pow]

/-- The basic quadratic bound: `‖X‖² ≥ 2⟨A,X⟩ - ‖A‖²`, scaled by a real parameter `t`. -/
lemma key_bound (A X : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    2 * t * rip A X - t ^ 2 * frobSq A ≤ frobSq X := by
  have h0 : 0 ≤ frobSq (X - (t : ℂ) • A) := frobSq_nonneg _
  rw [frobSq_sub, rip_smul, frobSq_smul] at h0
  rw [rip_comm A X]
  nlinarith [h0]

/-! ### Spectral functional calculus for Hermitian matrices -/

section Spec

variable {A : Matrix (Fin d) (Fin d) ℂ}

/-- `specMat hA f` is the matrix `U * diagonal f * Uᴴ` where `U` diagonalizes `A`. -/
noncomputable def specMat (hA : A.IsHermitian) (f : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (f i : ℂ)) *
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ

lemma uni_mul_star (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
  have := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose] at this

lemma star_mul_uni (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ *
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose] at this

lemma specMat_mul (hA : A.IsHermitian) (f g : Fin d → ℝ) :
    specMat hA f * specMat hA g = specMat hA (fun i => f i * g i) := by
  unfold specMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ)
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ), star_mul_uni hA, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  push_cast
  ring

lemma specMat_sub (hA : A.IsHermitian) (f g : Fin d → ℝ) :
    specMat hA f - specMat hA g = specMat hA (fun i => f i - g i) := by
  unfold specMat
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [h]

lemma specMat_one (hA : A.IsHermitian) : specMat hA (fun _ => (1 : ℝ)) = 1 := by
  unfold specMat
  simp [uni_mul_star hA]

lemma specMat_isHermitian (hA : A.IsHermitian) (f : Fin d → ℝ) :
    (specMat hA f).IsHermitian := by
  unfold specMat Matrix.IsHermitian
  have h : (star fun i => ((f i : ℝ) : ℂ)) = fun i => ((f i : ℝ) : ℂ) := by
    funext i; simp
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.diagonal_conjTranspose, h]

lemma specMat_posSemidef (hA : A.IsHermitian) {f : Fin d → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (specMat hA f).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using Complex.zero_le_real.mpr (hf i)
  exact hd.mul_mul_conjTranspose_same _

lemma specMat_trace (hA : A.IsHermitian) (f : Fin d → ℝ) :
    (specMat hA f).trace = ((∑ i, f i : ℝ) : ℂ) := by
  unfold specMat
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_uni hA, Matrix.one_mul,
    Matrix.trace_diagonal]
  push_cast
  rfl

lemma specMat_zero (hA : A.IsHermitian) : specMat hA (fun _ => (0 : ℝ)) = 0 := by
  unfold specMat
  simp

lemma specMat_eigenvalues (hA : A.IsHermitian) : specMat hA hA.eigenvalues = A := by
  conv_rhs => rw [hA.spectral_theorem]
  unfold specMat
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

end Spec

/-! ### Traces of products of positive semidefinite matrices -/

lemma trace_mul_nonneg {A B : Matrix (Fin d) (Fin d) ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  set U := (hA.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hA' : A = U * Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hA.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  have hM : ((Uᴴ * B * U)).PosSemidef := hB.conjTranspose_mul_mul_same U
  have htr : Matrix.trace (A * B)
      = Matrix.trace (Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) *
          (Uᴴ * B * U)) := by
    conv_lhs => rw [hA']
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hsum : Matrix.trace (Matrix.diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) *
      (Uᴴ * B * U)) = ∑ i, ((hA.1.eigenvalues i : ℝ) : ℂ) * (Uᴴ * B * U) i i := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  rw [htr, hsum, Complex.re_sum]
  refine Finset.sum_nonneg (fun i _ => ?_)
  have h1 : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
  have h2 : 0 ≤ ((Uᴴ * B * U) i i).re := (Complex.le_def.mp hM.diag_nonneg).1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  positivity

/-! ### The rank-trace inequality -/

/-- **The rank-trace inequality (Lemma 3.2).** For Hermitian `P, Q` with `P` positive
semidefinite of rank at most `r` and `Q` having at most `b` strictly positive eigenvalues,
and any `c > 0`,
`c * tr P - (c²/4) * r + 2c * tr Q - c² * b ≤ ‖P + Q‖²_F`. -/
theorem rank_trace_ineq {r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex Q ≤ b)
    {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  classical
  have hPh : P.IsHermitian := hP.1
  set lam : Fin d → ℝ := hQ.eigenvalues with hlam
  set mu : Fin d → ℝ := hPh.eigenvalues with hmu
  set Qp : Matrix (Fin d) (Fin d) ℂ := specMat hQ (fun i => max (lam i) 0) with hQpdef
  set Qm : Matrix (Fin d) (Fin d) ℂ := specMat hQ (fun i => max (-(lam i)) 0) with hQmdef
  set Pip : Matrix (Fin d) (Fin d) ℂ :=
    specMat hQ (fun i => if 0 < lam i then (1 : ℝ) else 0) with hPipdef
  set PiP : Matrix (Fin d) (Fin d) ℂ :=
    specMat hPh (fun i => if mu i ≠ 0 then (1 : ℝ) else 0) with hPiPdef
  -- positivity of the pieces
  have hQpPSD : Qp.PosSemidef := specMat_posSemidef hQ (fun i => le_max_right _ _)
  have hQmPSD : Qm.PosSemidef := specMat_posSemidef hQ (fun i => le_max_right _ _)
  -- `Q` splits as `Qp - Qm`
  have hQeq : Qp - Qm = Q := by
    rw [hQpdef, hQmdef, specMat_sub]
    have : (fun i => max (lam i) 0 - max (-(lam i)) 0) = lam := by
      funext i
      rcases le_total 0 (lam i) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [this, hlam, specMat_eigenvalues hQ]
  -- the positive and negative parts are orthogonal
  have hQmQp : Qm * Qp = 0 := by
    rw [hQmdef, hQpdef, specMat_mul]
    have : (fun i => max (-(lam i)) 0 * max (lam i) 0) = fun _ => (0 : ℝ) := by
      funext i
      rcases le_total 0 (lam i) with h | h
      · rw [max_eq_right (by linarith : -(lam i) ≤ 0)]; ring
      · rw [max_eq_right h]; ring
    rw [this, specMat_zero hQ]
  -- the spectral projection onto the positive part of `Q`
  have hPipQp : Pip * Qp = Qp := by
    rw [hPipdef, hQpdef, specMat_mul]
    congr 1
    funext i
    by_cases h : 0 < lam i
    · simp [h, max_eq_left h.le]
    · simp [h, max_eq_right (not_lt.mp h)]
  have hPipH : Pipᴴ = Pip := specMat_isHermitian hQ _
  have hPipPip : Pip * Pip = Pip := by
    rw [hPipdef, specMat_mul]
    congr 1
    funext i
    by_cases h : 0 < lam i <;> simp [h]
  have hPiptrace : rtrace Pip = (posIndex Q : ℝ) := by
    rw [hPipdef, rtrace, specMat_trace, Complex.ofReal_re, posIndex, dif_pos hQ,
      Finset.sum_boole]
  have hPipfrob : frobSq Pip = (posIndex Q : ℝ) := by
    rw [frobSq, hPipH, hPipPip, ← rtrace, hPiptrace]
  -- the spectral projection onto the range of `P`
  have hPspec : specMat hPh mu = P := by rw [hmu]; exact specMat_eigenvalues hPh
  have hPiPP : PiP * P = P := by
    have h0 : specMat hPh (fun i => if mu i ≠ 0 then (1 : ℝ) else 0) * specMat hPh mu
        = specMat hPh mu := by
      rw [specMat_mul]
      congr 1
      funext i
      by_cases h : mu i = 0 <;> simp [h]
    rwa [← hPiPdef, hPspec] at h0
  have hPiPH : PiPᴴ = PiP := specMat_isHermitian hPh _
  have hPiPcompl : ((1 : Matrix (Fin d) (Fin d) ℂ) - PiP).PosSemidef := by
    have h1 : (1 : Matrix (Fin d) (Fin d) ℂ) = specMat hPh (fun _ => (1 : ℝ)) :=
      (specMat_one hPh).symm
    rw [h1, hPiPdef, specMat_sub]
    refine specMat_posSemidef hPh (fun i => ?_)
    by_cases h : mu i = 0 <;> simp [h]
  have hPiPfrob : frobSq PiP = (P.rank : ℝ) := by
    have hPiPPiP : PiP * PiP = PiP := by
      rw [hPiPdef, specMat_mul]
      congr 1
      funext i
      by_cases h : mu i = 0 <;> simp [h]
    have hrk : P.rank = (Finset.univ.filter (fun i => mu i ≠ 0)).card := by
      rw [hPh.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    rw [frobSq, hPiPH, hPiPPiP, ← rtrace, hPiPdef, rtrace, specMat_trace, Complex.ofReal_re,
      Finset.sum_boole, hrk]
  -- traces
  have htrQ : rtrace Q = rtrace Qp - rtrace Qm := by
    rw [← hQeq, rtrace, rtrace, rtrace, Matrix.trace_sub, Complex.sub_re]
  have htrQm : 0 ≤ rtrace Qm := (Complex.le_def.mp hQmPSD.trace_nonneg).1
  -- Step A : the cross term is nonnegative
  have hstepA : frobSq (P - Qm) + frobSq Qp ≤ frobSq (P + Q) := by
    have hsum : P + Q = (P - Qm) + Qp := by rw [← hQeq]; abel
    have hcross : 0 ≤ rip (P - Qm) Qp := by
      have h1 : (P - Qm)ᴴ = P - Qm := by
        rw [Matrix.conjTranspose_sub, hPh, (specMat_isHermitian hQ _ : Qmᴴ = Qm)]
      have h2 : rip (P - Qm) Qp = (Matrix.trace (P * Qp)).re - (Matrix.trace (Qm * Qp)).re := by
        rw [rip, h1, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
      rw [h2, hQmQp]
      simpa using trace_mul_nonneg hP hQpPSD
    rw [hsum, frobSq_add]
    linarith
  -- Step B : bound for the positive part of `Q`
  have hstepB : 2 * c * rtrace Qp - c ^ 2 * b ≤ frobSq Qp := by
    have hkey := key_bound Pip Qp c
    have h1 : rip Pip Qp = rtrace Qp := by
      rw [rip, hPipH, hPipQp, rtrace]
    have h2 : c ^ 2 * frobSq Pip ≤ c ^ 2 * b := by
      rw [hPipfrob]
      have : (posIndex Q : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      nlinarith [sq_nonneg c]
    rw [h1] at hkey
    linarith
  -- Step C : bound for `P - Qm`
  have hstepC : c * (rtrace P - rtrace Qm) - (c ^ 2 / 4) * r ≤ frobSq (P - Qm) := by
    have hkey := key_bound PiP (P - Qm) (c / 2)
    have h1 : rip PiP (P - Qm) = rtrace P - (Matrix.trace (PiP * Qm)).re := by
      rw [rip, hPiPH, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hPiPP, rtrace]
    have h2 : (Matrix.trace (PiP * Qm)).re ≤ rtrace Qm := by
      have h3 := trace_mul_nonneg hPiPcompl hQmPSD
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, Matrix.one_mul] at h3
      rw [rtrace]
      linarith
    have h4 : c * (rtrace P - rtrace Qm) ≤ 2 * (c / 2) * rip PiP (P - Qm) := by
      rw [h1]
      have : 2 * (c / 2) = c := by ring
      rw [this]
      nlinarith [hc.le]
    have h5 : (c / 2) ^ 2 * frobSq PiP ≤ (c ^ 2 / 4) * r := by
      rw [hPiPfrob]
      have : (P.rank : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith [sq_nonneg c]
    linarith
  -- combine
  have hfin : c * rtrace Qm ≥ 0 := by positivity
  rw [htrQ]
  linarith

/-- The special case `c = 2` of the rank-trace inequality. -/
theorem rank_trace_ineq_two {r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex Q ≤ b) :
    2 * rtrace P + 4 * rtrace Q - 4 * b - frobSq (P + Q) ≤ r := by
  have := rank_trace_ineq hP hQ hr hb (c := 2) (by norm_num)
  norm_num at this ⊢
  linarith

end Zeta23Redux.LinAlg

#print axioms Zeta23Redux.LinAlg.rank_trace_ineq
#print axioms Zeta23Redux.LinAlg.rank_trace_ineq_two

