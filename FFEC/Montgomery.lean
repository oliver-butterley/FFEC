module
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs

public section

/-!
# Montgomery equations of elliptic curves

A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy `IsUnit (B (A² − 4))`. Defined over an
arbitrary `[CommRing R]`.
-/

variable {R : Type*} [CommRing R]

/-- A Montgomery curve `B y² = x³ + A x² + x`, nondegenerate.

The nondegeneracy datum is `IsUnit (B (A² − 4))` — the unit-valued condition mirroring Mathlib's
`EllipticCurve.Δ' : Rˣ` (and `WeierstrassCurve.IsElliptic`, which asks `IsUnit Δ`). Here
`B (A² − 4)` is the non-`16` factor of the Weierstrass discriminant `Δ = 16 B⁶ (A² − 4)`, so over a
field of char ≠ 2 it is exactly the Montgomery nonsingularity condition `B ≠ 0 ∧ A ≠ ±2`. Over a
field `IsUnit x ↔ x ≠ 0`; the `IsUnit` form is the correct one over a general ring (it is what makes
the curve smooth over `Spec R`, not merely over the fraction field). -/
structure MontgomeryCurve (R : Type*) [CommRing R] where
  A : R
  B : R
  nondegen : IsUnit (B * (A ^ 2 - 4))

namespace MontgomeryCurve

/-- The MontgomeryCurve defining equation `B y² = x³ + A x² + x`. -/
def Equation (M : MontgomeryCurve R) (x y : R) : Prop :=
  M.B * y ^ 2 = x ^ 3 + M.A * x ^ 2 + x

/-- Points: the identity (point at infinity) plus affine on-curve points.
note: `some` carries only the polynomial `Equation`; on the Weierstrass side
`equation_iff_nonsingular` upgrades it to `Nonsingular` once `IsElliptic` is available. -/
inductive Point (M : MontgomeryCurve R)
  | zero
  | some (x y : R) (h : M.Equation x y)
  deriving DecidableEq

/-- Two affine points are equal once their coordinates agree, the on-curve proof is irrelevant. -/
theorem Point.some_ext {M : MontgomeryCurve R} {x₁ y₁ : R} {h₁ : M.Equation x₁ y₁}
    {x₂ y₂ : R} {h₂ : M.Equation x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : M.Point) = Point.some x₂ y₂ h₂ := by subst hx; subst hy; rfl

end MontgomeryCurve
