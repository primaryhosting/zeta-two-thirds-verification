/-
# Sq Ge Linear
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sq_ge_linear
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Redux.LinAlg

/-- For all real `x`, `c`: `c * x - c ^ 2 / 4 ≤ x ^ 2`, since this is `(x - c / 2) ^ 2 ≥ 0`. -/
theorem sq_ge_linear (x c : ℝ) : c * x - c ^ 2 / 4 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - c / 2)]

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

