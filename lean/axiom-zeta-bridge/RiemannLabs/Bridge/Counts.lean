/-
Copyright (c) 2026 Riemann Labs.
Released under Apache 2.0 license.
-/
module

public import Zeta23.Statement.SeamClosed
public import ZetaZeros.Defs

open scoped BigOperators
open Set

noncomputable section

namespace RiemannLabs.Bridge

/-- Axiom's cumulative nontrivial-zero set is exactly Zeta23's window `(0, T]`. -/
@[simp]
theorem nontrivialZeros_eq_zerosIn (T : ℝ) :
    ZetaZeros.nontrivialZeros T = Zeta23.zerosIn 0 T := by
  ext ρ
  simp only [ZetaZeros.nontrivialZeros, Zeta23.zerosIn, Zeta23.IsNontrivialZero,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hre0, hre1, him0, himT⟩
    exact ⟨⟨hz, hre0, hre1⟩, him0, himT⟩
  · rintro ⟨⟨hz, hre0, hre1⟩, him0, himT⟩
    exact ⟨hz, hre0, hre1, him0, himT⟩

/-- Both projects use the natural-valued analytic order of `riemannZeta`. -/
@[simp]
theorem zeroMultiplicity_eq_zeroMult (ρ : ℂ) :
    ZetaZeros.zeroMultiplicity ρ = Zeta23.zeroMult ρ := by
  rfl

/-- Axiom's cumulative zero count is Zeta23's multiplicity-weighted count on `(0, T]`. -/
@[simp]
theorem zeroCount_eq_Ncount (T : ℝ) :
    ZetaZeros.zeroCount T = Zeta23.Ncount 0 T := by
  simp only [ZetaZeros.zeroCount, Zeta23.Ncount, nontrivialZeros_eq_zerosIn,
    zeroMultiplicity_eq_zeroMult]

end RiemannLabs.Bridge
