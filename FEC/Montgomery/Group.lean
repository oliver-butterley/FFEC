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

/-- The transport bridge `M.Point ≃ W.Point` as an **additive** equivalence: the group on `M.Point`
is *defined* as the transport along `pointEquiv`, so the bridge is a group isomorphism by
construction — no addition-formula reasoning required. -/
noncomputable def MontgomeryCurve.pointAddEquiv (M : MontgomeryCurve F) :
    M.Point ≃+ (M.toWeierstrass).toAffine.Point :=
  Equiv.addEquiv M.pointEquiv

/-- The group identity of `M.Point` is the point at infinity. -/
@[simp] theorem MontgomeryCurve.zero_def (M : MontgomeryCurve F) : (0 : M.Point) = .zero := by
  refine M.pointEquiv.injective ?_
  change M.pointAddEquiv 0 = M.pointEquiv .zero
  rw [map_zero]; rfl

-- Architectural stress test: the full pipeline composes and the group instance resolves.
noncomputable example (M : MontgomeryCurve F) : AddCommGroup M.Point := inferInstance

