import FFEC.Messy.Field
import FFEC.Montgomery

/-!
# MontgomeryCurve model: definitions

A Montgomery curve `B y² = x³ + A x² + x` with nondegeneracy `IsUnit (B (A² − 4))`. Defined over an
arbitrary `[CommRing R]` (the structure, `Equation`, `Point`, and base change `map`); the point
group specializes to a field later.

The basis of the Montgomery chain: `ToWeierstrass` (the Weierstrass embedding, `Δ`, `IsElliptic`,
`j`), `Equiv` (the point bijection to Weierstrass), and `Group` (the transported group + explicit
law) all build on this file. `Edwards.Defs` also targets it via the birational `toMontgomery`.
-/


variable {R : Type*} [CommRing R]

namespace MontgomeryCurve

variable {R' : Type*} [CommRing R']

/-- Base change of a Montgomery curve along a ring hom `f : R →+* R'` (mirrors
`WeierstrassCurve.map`). The `IsUnit` nondegeneracy transports via `IsUnit.map`. -/
def map (M : MontgomeryCurve R) (f : R →+* R') : MontgomeryCurve R' where
  A := f M.A
  B := f M.B
  nondegen := by
    have e : f M.B * (f M.A ^ 2 - 4) = f (M.B * (M.A ^ 2 - 4)) := by
      simp only [map_mul, map_sub, map_pow, map_ofNat]
    rw [e]; exact M.nondegen.map f

@[simp] theorem map_A (M : MontgomeryCurve R) (f : R →+* R') : (M.map f).A = f M.A := rfl
@[simp] theorem map_B (M : MontgomeryCurve R) (f : R →+* R') : (M.map f).B = f M.B := rfl

/-- The point at infinity makes `M.Point` inhabited. -/
instance (M : MontgomeryCurve R) : Inhabited M.Point := ⟨.zero⟩

end MontgomeryCurve
