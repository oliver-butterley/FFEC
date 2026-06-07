import FFEC.Montgomery.ToWeierstrass

/-!
# MontgomeryCurve ≃ Weierstrass on points (the per-model datum)

Over `F` with `char ≠ 2`, the scaling `(x, y) ↦ (B x, B² y)` is a bijection of point sets between
the Montgomery curve and its Weierstrass realization (infinity ↦ identity). This `pointEquiv` is the
**only** datum the MontgomeryCurve model supplies; the group then transports (see `Group.lean`).
-/


open WeierstrassCurve

variable {F : Type*} [Field F] [NeZero (2 : F)]

namespace MontgomeryCurve

/-- `2 ≠ 0` (the field has characteristic ≠ 2, recorded by `[NeZero (2 : F)]`). -/
theorem two_ne_zero : (2 : F) ≠ 0 := NeZero.ne (2 : F)

omit [NeZero (2 : F)] in
/-- `B ≠ 0`. From `nondegen : IsUnit (B (A²−4))`. -/
theorem B_ne_zero (M : MontgomeryCurve F) : M.B ≠ 0 :=
  left_ne_zero_of_mul M.nondegen.ne_zero

omit [NeZero (2 : F)] in
/-- `A² − 4 ≠ 0`. From `nondegen`. -/
theorem A_sq_sub_four_ne_zero (M : MontgomeryCurve F) : M.A ^ 2 - 4 ≠ 0 :=
  right_ne_zero_of_mul M.nondegen.ne_zero

/-- `W(M)` is elliptic.
note: `Δ = 16 B⁶ (A²−4)` (`toWeierstrass_Δ`) is a unit, since `16 ≠ 0` (`two_ne_zero`), `B ≠ 0`,
`A²−4 ≠ 0`. Conclude `IsUnit` via `isUnit_of_ne_zero` + `mul_ne_zero`. -/
instance (M : MontgomeryCurve F) : (M.toWeierstrass).IsElliptic := by
  refine ⟨?_⟩
  rw [toWeierstrass_Δ, isUnit_iff_ne_zero]
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 two_ne_zero
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 6 (B_ne_zero M))) (A_sq_sub_four_ne_zero M)

omit [NeZero (2 : F)] in
/-- On-curve transfers forward under `(x, y) ↦ (B x, B² y)`.
note: `rw [equation_iff]`, then `linear_combination (M.B ^ 3) * h`. -/
theorem equation_toW (M : MontgomeryCurve F) {x y : F} (h : M.Equation x y) :
    (M.toWeierstrass).toAffine.Equation (M.B * x) (M.B ^ 2 * y) := by
  rw [MontgomeryCurve.Equation] at h
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [MontgomeryCurve.toWeierstrass]
  linear_combination (M.B ^ 3) * h

omit [NeZero (2 : F)] in
/-- On-curve transfers backward under `(u, v) ↦ (u / B, v / B²)`.
note: `field_simp [B_ne_zero]` both sides, then `linear_combination`. -/
theorem equation_ofW (M : MontgomeryCurve F) {u v : F}
    (h : (M.toWeierstrass).toAffine.Equation u v) :
    M.Equation (u / M.B) (v / M.B ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [MontgomeryCurve.toWeierstrass] at h
  rw [MontgomeryCurve.Equation]
  have hB := B_ne_zero M
  field_simp
  linear_combination h

omit [NeZero (2 : F)] in
/-- **The per-model datum**: the canonical bijection `M.Point ≃ W(M).Point`.
note: `(x, y) ↦ (B x, B² y)`, `zero ↦ zero`; inverse `(u, v) ↦ (u / B, v / B²)`. Bijective because
the scaling is invertible (`B ≠ 0`); the `Nonsingular` proofs come from `equation_iff_nonsingular`
applied to `equation_toW` / `equation_ofW`. `left_inv`/`right_inv`: `B * x / B = x`, etc. -/
noncomputable def pointEquiv (M : MontgomeryCurve F) :
    M.Point ≃ (M.toWeierstrass).toAffine.Point where
  toFun P := match P with
    | .zero => .zero
    | .some x y h =>
        .some (M.B * x) (M.B ^ 2 * y)
          ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp (equation_toW M h))
  invFun Q := match Q with
    | .zero => .zero
    | .some u v h =>
        .some (u / M.B) (v / M.B ^ 2)
          (equation_ofW M ((WeierstrassCurve.Affine.equation_iff_nonsingular).mpr h))
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · have hB := B_ne_zero M
      simp only [MontgomeryCurve.Point.some.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp
  right_inv := by
    rintro (_ | ⟨u, v, h⟩)
    · rfl
    · have hB := B_ne_zero M
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp

/-- **Computation lemma**: the bridge sends the affine MontgomeryCurve point `(x, y)` to the
Weierstrass point `(B·x, B²·y)` (`B = M.B`). Unfolds the `match` in `pointEquiv`. -/
theorem pointEquiv_some (M : MontgomeryCurve F) {x y : F} (h : M.Equation x y) :
    M.pointEquiv (MontgomeryCurve.Point.some x y h)
      = .some (M.B * x) (M.B ^ 2 * y)
          ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp (equation_toW M h)) := rfl

end MontgomeryCurve

