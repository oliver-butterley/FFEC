import FEC.Curve

/-!
# Montgomery model: definitions

A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy `B (A² − 4) ≠ 0`. Defined over an
arbitrary `[CommRing R]` (params and equation); the point group specializes to `𝔽 p` later.
-/

namespace FEC

variable {R : Type*} [CommRing R]

/-- A Montgomery curve `B y² = x³ + A x² + x`, nondegenerate (`B (A² − 4) ≠ 0`). -/
structure Montgomery (R : Type*) [CommRing R] where
  A : R
  B : R
  nondegen : B * (A ^ 2 - 4) ≠ 0

namespace Montgomery

/-- The Montgomery defining equation `B y² = x³ + A x² + x`. -/
def Equation (M : Montgomery R) (x y : R) : Prop :=
  M.B * y ^ 2 = x ^ 3 + M.A * x ^ 2 + x

/-- Points: the identity (point at infinity) plus affine on-curve points.
note: `some` carries only the polynomial `Equation`; on the Weierstrass side
`equation_iff_nonsingular` upgrades it to `Nonsingular` once `IsElliptic` is available. -/
inductive Point (M : Montgomery R)
  | zero
  | some (x y : R) (h : M.Equation x y)

end Montgomery

end FEC
