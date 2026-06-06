import FEC.Montgomery.ToWeierstrass

/-!
# Montgomery ≃ Weierstrass on points (the per-model datum)

Over `𝔽 p` with `char ≠ 2`, the scaling `(x, y) ↦ (B x, B² y)` is a bijection of point sets between
the Montgomery curve and its Weierstrass realization (infinity ↦ identity). This `pointEquiv` is the
**only** datum the Montgomery model supplies; the group then transports (see `Group.lean`).
-/

namespace FEC

open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

namespace Montgomery

/-- `2 ≠ 0` in `𝔽 p`. From `2 < p` (prime characteristic). -/
theorem two_ne_zero : (2 : 𝔽 p) ≠ 0 := by
  have hp : 2 < p := Fact.out
  have h : ((2 : ℕ) : 𝔽 p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  simpa using h

omit [Fact (2 < p)] in
/-- `B ≠ 0`. From `nondegen : B (A²−4) ≠ 0`. -/
theorem B_ne_zero (M : Montgomery (𝔽 p)) : M.B ≠ 0 :=
  left_ne_zero_of_mul M.nondegen

omit [Fact (2 < p)] in
/-- `A² − 4 ≠ 0`. From `nondegen`. -/
theorem A_sq_sub_four_ne_zero (M : Montgomery (𝔽 p)) : M.A ^ 2 - 4 ≠ 0 :=
  right_ne_zero_of_mul M.nondegen

/-- `W(M)` is elliptic.
note: `Δ = 16 B⁶ (A²−4)` (`toWeierstrass_Δ`) is a unit, since `16 ≠ 0` (`two_ne_zero`), `B ≠ 0`,
`A²−4 ≠ 0`. Conclude `IsUnit` via `isUnit_of_ne_zero` + `mul_ne_zero`. -/
instance (M : Montgomery (𝔽 p)) : (M.toWeierstrass).IsElliptic := by
  refine ⟨?_⟩
  rw [toWeierstrass_Δ, isUnit_iff_ne_zero]
  have h16 : (16 : 𝔽 p) ≠ 0 := by
    have : (16 : 𝔽 p) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero 4 two_ne_zero
  exact mul_ne_zero (mul_ne_zero h16 (pow_ne_zero 6 (B_ne_zero M))) (A_sq_sub_four_ne_zero M)

omit [Fact (2 < p)] in
/-- On-curve transfers forward under `(x, y) ↦ (B x, B² y)`.
note: `rw [equation_iff]`, then `linear_combination (M.B ^ 3) * h`. -/
theorem equation_toW (M : Montgomery (𝔽 p)) {x y : 𝔽 p} (h : M.Equation x y) :
    (M.toWeierstrass).toAffine.Equation (M.B * x) (M.B ^ 2 * y) := by
  rw [Montgomery.Equation] at h
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [Montgomery.toWeierstrass]
  linear_combination (M.B ^ 3) * h

omit [Fact (2 < p)] in
/-- On-curve transfers backward under `(u, v) ↦ (u / B, v / B²)`.
note: `field_simp [B_ne_zero]` both sides, then `linear_combination`. -/
theorem equation_ofW (M : Montgomery (𝔽 p)) {u v : 𝔽 p}
    (h : (M.toWeierstrass).toAffine.Equation u v) :
    M.Equation (u / M.B) (v / M.B ^ 2) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [Montgomery.toWeierstrass] at h
  rw [Montgomery.Equation]
  have hB := B_ne_zero M
  field_simp
  linear_combination h

/-- **The per-model datum**: the canonical bijection `M.Point ≃ W(M).Point`.
note: `(x, y) ↦ (B x, B² y)`, `zero ↦ zero`; inverse `(u, v) ↦ (u / B, v / B²)`. Bijective because
the scaling is invertible (`B ≠ 0`); the `Nonsingular` proofs come from `equation_iff_nonsingular`
applied to `equation_toW` / `equation_ofW`. `left_inv`/`right_inv`: `B * x / B = x`, etc. -/
noncomputable def pointEquiv (M : Montgomery (𝔽 p)) :
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
      simp only [Montgomery.Point.some.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp
  right_inv := by
    rintro (_ | ⟨u, v, h⟩)
    · rfl
    · have hB := B_ne_zero M
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp

end Montgomery

end FEC
