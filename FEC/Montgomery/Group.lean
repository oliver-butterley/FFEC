import FEC.Montgomery.Equiv
import FEC.Framework

/-!
# MontgomeryCurve point group (transported)

The MontgomeryCurve point group is obtained by transporting Mathlib's Weierstrass group along the
canonical `pointEquiv`. NO group axioms are re-proved — this is the transfer theorem in action.
-/


open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)]

/-- The MontgomeryCurve point group, transported from Weierstrass via `pointEquiv`. -/
noncomputable instance (M : MontgomeryCurve F) : AddCommGroup M.Point :=
  M.pointEquiv.addCommGroup

-- Architectural stress test: the full pipeline composes and the group instance resolves.
noncomputable example (M : MontgomeryCurve F) : AddCommGroup M.Point := inferInstance

