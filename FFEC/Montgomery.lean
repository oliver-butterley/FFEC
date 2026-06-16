module
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs

public section

/-!
# Montgomery equations of elliptic curves

A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy `IsUnit (B (A² − 4))`.
-/

variable {R : Type*} [CommRing R]

/-- A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy condition. -/
structure MontgomeryCurve (R : Type*) [CommRing R] where
  A : R
  B : R
  nondegen : IsUnit (B * (A ^ 2 - 4))

namespace MontgomeryCurve

/-- The MontgomeryCurve defining equation `B y² = x³ + A x² + x`. -/
def Equation (M : MontgomeryCurve R) (x y : R) : Prop :=
  M.B * y ^ 2 = x ^ 3 + M.A * x ^ 2 + x

/-- Points: the identity (point at infinity) plus affine on-curve points. -/
inductive Point (M : MontgomeryCurve R)
  | zero
  | some (x y : R) (h : M.Equation x y)
  deriving DecidableEq

/-- Two affine points are equal once their coordinates agree, the on-curve proof is irrelevant. -/
theorem Point.some_ext {M : MontgomeryCurve R} {x₁ y₁ : R} {h₁ : M.Equation x₁ y₁}
    {x₂ y₂ : R} {h₂ : M.Equation x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.some x₁ y₁ h₁ : M.Point) = Point.some x₂ y₂ h₂ := by subst hx; subst hy; rfl

end MontgomeryCurve
