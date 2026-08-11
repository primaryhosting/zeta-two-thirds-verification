import Mathlib
/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step, coming from `(m - 1)^2 ≥ 0`:
for every natural number `m` we have `2 * m ≤ m ^ 2 + 1`, equivalently
`(m : ℤ) ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_shadow :
    (∀ m : ℕ, 2 * m ≤ m ^ 2 + 1) ∧ (∀ m : ℕ, ((m : ℤ)) ^ 2 ≥ 2 * (m : ℤ) - 1) := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · zify
    nlinarith [sq_nonneg ((m : ℤ) - 1)]
  · nlinarith [sq_nonneg ((m : ℤ) - 1)]

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

