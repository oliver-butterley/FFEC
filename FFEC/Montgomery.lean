module
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Defs
public import FFEC.IsoClasses

public section

/-!
# Montgomery equations of elliptic curves

A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy `IsUnit (B (A² − 4))`.
-/

open EllipticCurve

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

/-! ## Admissibility of an isomorphism class

Which isomorphism classes over `𝔽[p]` admit a Montgomery model.

TODO: move `isAdmissible` and `AdmissibleIsomCl` to their own file.
-/

/-- The class `ic` admits a Montgomery `A`-parameter over `𝔽[p]`: the inversion cubic
`256·(A²−3)³/(A²−4) = j` has a nondegenerate root. -/
def isAdmissible {p : Nat} [Fact p.Prime] [Fact (3 < p)] (ic : IsomCl p) : Prop :=
  ∃ a : 𝔽[p], a ^ 2 - 4 ≠ 0 ∧ 256 * (a ^ 2 - 3) ^ 3 / (a ^ 2 - 4) = (Quotient.out ic).1
-- TODO: check this

/-- The content of `isAdmissible`, published as a lemma so that the definition itself can stay
sealed. -/
theorem isAdmissible_iff {p : Nat} [Fact p.Prime] [Fact (3 < p)] {ic : IsomCl p} :
    isAdmissible ic ↔ ∃ a : 𝔽[p], a ^ 2 - 4 ≠ 0 ∧
      256 * (a ^ 2 - 3) ^ 3 / (a ^ 2 - 4) = (Quotient.out ic).1 :=
  Iff.rfl

/-- The elliptic curve admits a Montgomery representation. -/
structure AdmissibleIsomCl (p : Nat) [Fact p.Prime] [Fact (3 < p)] where
  ic : IsomCl p
  is_admissible : isAdmissible ic

namespace AdmissibleIsomCl

variable {p : Nat} [Fact p.Prime] [Fact (3 < p)] (α : AdmissibleIsomCl p)

/-- A Montgomery `A`-parameter for the admissible class `α`.  Chosen once here, where
`isAdmissible` is transparent, so that the definition need not be exposed. -/
noncomputable def A : 𝔽[p] := α.is_admissible.choose

/-- The chosen parameter is nondegenerate. -/
theorem A_sq_sub_four_ne_zero : α.A ^ 2 - 4 ≠ 0 := α.is_admissible.choose_spec.1

/-- The chosen parameter inverts the `j`-invariant of the class. -/
theorem j_A : 256 * (α.A ^ 2 - 3) ^ 3 / (α.A ^ 2 - 4) = (Quotient.out α.ic).1 :=
  α.is_admissible.choose_spec.2

end AdmissibleIsomCl

end MontgomeryCurve
