module
public import FFEC.Montgomery
public import FFEC.IsoClasses
public import Mathlib

public section

variable (p : Nat) [Fact p.Prime]

/- TODO: move the info about `WeierstrassCurve` to an appropriate home. -/

/- We have to do this or open Classical in each of the following three. -/
noncomputable instance : DecidableEq 𝔽[p] := Classical.decEq _

noncomputable def WeierstrassOfJ (J : EllipticCurveUpToIso p) : WeierstrassCurve 𝔽[p] :=
  WeierstrassCurve.ofJ (Quotient.out J).1

variable (J : EllipticCurveUpToIso p)

instance : (WeierstrassOfJ p J).IsElliptic :=
  inferInstanceAs (WeierstrassCurve.ofJ (Quotient.out J).1).IsElliptic

theorem j_of_WeierstrassOfJ : (WeierstrassOfJ p J).j = (Quotient.out J).1 :=
  WeierstrassCurve.ofJ_j _

/-! Weierstrass to Montgomery

TODO: spec about D? -/

def MontgomeryCurveOfJ (J : EllipticCurveUpToIso p) : MontgomeryCurve 𝔽[p] := sorry

/- TODO: extend to CommRing -/
def MontgomeryCurve.j {R : Type*} [Field R] (M : MontgomeryCurve R) : R :=
  256 * ((M.A ^ 2) - 3)^3 / (M.A ^ 2 - 4)

theorem j_of_MontgomeryCurveOfJ : (MontgomeryCurveOfJ p J).j = (Quotient.out J).1 := sorry

def Weierstrass.toMontgomeryCurve : WeierstrassCurve.Affine.Point (WeierstrassOfJ p J) ≃
  MontgomeryCurve.Point (MontgomeryCurveOfJ p J) := sorry
