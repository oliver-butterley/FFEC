import FEC.Curve

/-!
# Weierstrass as the existence anchor (one model among equals)

Mathlib's `WeierstrassCurve.Affine.Point` already carries a complete `AddCommGroup`. That is the
*existence anchor* for the curve's group — but Weierstrass is not privileged in any statement: it is
simply the model whose points are, by definition, `c.group`. Its transfer datum is the identity.
-/

namespace FEC

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

/-- The canonical group is, by construction, the group of Weierstrass points — so the Weierstrass
transfer is the identity. Weierstrass is one model among equals. -/
def Curve.weierstrassTransfer (c : Curve F) : GroupTransfer c.group c.group :=
  ⟨Equiv.refl _⟩

end FEC
