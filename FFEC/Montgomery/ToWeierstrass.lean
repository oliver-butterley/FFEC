import FFEC.Montgomery.Defs

/-!
# MontgomeryCurve → Weierstrass

The integral, division-free change of variables `(x, y) ↦ (B x, B² y)` sends
`B y² = x³ + A x² + x` to `(B²y)² = (Bx)³ + (AB)(Bx)² + (B²)(Bx)`, i.e. the Weierstrass curve
`{a₁ := 0, a₂ := A·B, a₃ := 0, a₄ := B², a₆ := 0}` (an `IsCharNeTwoNF` curve). Its discriminant
is `Δ = 16 B⁶ (A² − 4)`, so the MontgomeryCurve nondegeneracy (plus `char ≠ 2`) is exactly
`IsElliptic`.
-/


open WeierstrassCurve

variable {R : Type*} [CommRing R]

namespace MontgomeryCurve

/-- The associated Weierstrass curve via `(x, y) ↦ (B x, B² y)`. -/
def toWeierstrass (M : MontgomeryCurve R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := M.A * M.B
  a₃ := 0
  a₄ := M.B ^ 2
  a₆ := 0

/-- `toWeierstrass` is in characteristic-`≠2` normal form (`a₁ = a₃ = 0`). -/
instance (M : MontgomeryCurve R) : (M.toWeierstrass).IsCharNeTwoNF :=
  ⟨rfl, rfl⟩

/-- `Δ(W) = 16 B⁶ (A² − 4)`.
note: `Δ_of_isCharNeTwoNF` with `a₆ = 0`, then `simp only [toWeierstrass]; ring`. -/
theorem toWeierstrass_Δ (M : MontgomeryCurve R) :
    (M.toWeierstrass).Δ = 16 * M.B ^ 6 * (M.A ^ 2 - 4) := by
  rw [Δ_of_isCharNeTwoNF]
  simp only [toWeierstrass]
  ring

/-- The `j`-invariant of the Montgomery curve, defined via its Weierstrass realization.
(`WeierstrassCurve.j` needs `[IsElliptic]` — available wherever the curve is nondegenerate, e.g.
over `𝔽 p` with `char ≠ 2`.) -/
noncomputable def j (M : MontgomeryCurve R) [(M.toWeierstrass).IsElliptic] : R :=
  (M.toWeierstrass).j

end MontgomeryCurve

