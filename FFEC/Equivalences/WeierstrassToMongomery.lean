module
public import FFEC.Montgomery
public import FFEC.IsoClasses
public import Mathlib

public section

variable (p : Nat) [Fact p.Prime] [Fact (3 < p)]

/- TODO: move the info about `WeierstrassCurve` to an appropriate home. -/

def WeierstrassOfJ (J : EllipticCurveUpToIso p) : WeierstrassCurve 𝔽[p] := sorry

variable (J : EllipticCurveUpToIso p)

instance : (WeierstrassOfJ p J).IsElliptic := sorry

theorem j_of_WeierstrassOfJ : (WeierstrassOfJ p J).j = (Quotient.out J).1 := sorry

/- TODO: spec about D? -/

def MontgomeryCurveOfJ (J : EllipticCurveUpToIso p) : MontgomeryCurve 𝔽[p] := sorry

/- TODO: extend to CommRing -/
def MontgomeryCurve.j {R : Type*} [Field R] (M : MontgomeryCurve R) : R :=
  256 * ((M.A ^ 2) - 3)^3 / (M.A ^ 2 - 4)

theorem j_of_MontgomeryCurveOfJ : (MontgomeryCurveOfJ p J).j = (Quotient.out J).1 := sorry

-- #print MontgomeryCurve.Point

def Weierstrass.toMontgomeryCurve : WeierstrassCurve.Affine.Point (WeierstrassOfJ p J) ≃
  MontgomeryCurve.Point (MontgomeryCurveOfJ p J) := sorry
