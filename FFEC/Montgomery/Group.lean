import FFEC.Montgomery.Equiv
import FFEC.Framework

/-!
# MontgomeryCurve point group (transported)

The MontgomeryCurve point group is obtained by transporting Mathlib's Weierstrass group along the
canonical `pointEquiv`. NO group axioms are re-proved — this is the transfer theorem in action.
-/


open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)]

/-- The MontgomeryCurve point group, transported from Weierstrass via `pointEquiv`. -/
noncomputable instance (M : MontgomeryCurve F) : AddCommGroup M.Point :=
  M.pointEquiv.addCommGroup

/-- The transport bridge `M.Point ≃ W.Point` as an **additive** equivalence: the group on `M.Point`
is *defined* as the transport along `pointEquiv`, so the bridge is a group isomorphism by
construction — no addition-formula reasoning required. -/
noncomputable def MontgomeryCurve.pointAddEquiv (M : MontgomeryCurve F) :
    M.Point ≃+ (M.toWeierstrass).toAffine.Point :=
  Equiv.addEquiv M.pointEquiv

/-- The group identity of `M.Point` is the point at infinity. -/
@[simp] theorem MontgomeryCurve.zero_def (M : MontgomeryCurve F) : (0 : M.Point) = .zero := by
  refine M.pointEquiv.injective ?_
  change M.pointAddEquiv 0 = M.pointEquiv .zero
  rw [map_zero]; rfl

namespace MontgomeryCurve

/-- Negation in `M.Point` is the MontgomeryCurve inverse `(x, y) ↦ (x, −y)`. -/
@[simp] theorem neg_some (M : MontgomeryCurve F) {x y : F} (h : M.Equation x y) :
    -(MontgomeryCurve.Point.some x y h)
      = .some x (-y) (by rw [Equation] at h ⊢; linear_combination h) := by
  refine M.pointEquiv.injective ?_
  change M.pointAddEquiv (-(MontgomeryCurve.Point.some x y h))
    = M.pointEquiv (.some x (-y) _)
  rw [map_neg]
  change -M.pointEquiv (MontgomeryCurve.Point.some x y h) = M.pointEquiv (.some x (-y) _)
  rw [M.pointEquiv_some, M.pointEquiv_some,
    WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨rfl, ?_⟩
  simp only [WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
  ring

omit [DecidableEq F] [NeZero (2 : F)] in
/-- The Weierstrass secant slope of the scaled points equals `B·λ` (`λ` the Montgomery slope). -/
theorem slope_secant_eq (M : MontgomeryCurve F) {x₁ y₁ x₂ y₂ : F}
    (hB : M.B ≠ 0) (hd : x₂ - x₁ ≠ 0) :
    (M.B ^ 2 * y₁ - M.B ^ 2 * y₂) / (M.B * x₁ - M.B * x₂)
      = M.B * ((y₂ - y₁) / (x₂ - x₁)) := by
  have hd' : x₁ - x₂ ≠ 0 := fun h => hd (by linear_combination -h)
  have hbd : M.B * x₁ - M.B * x₂ ≠ 0 := fun h => hd' (mul_left_cancel₀ hB (by linear_combination h))
  field_simp
  ring

omit [DecidableEq F] [NeZero (2 : F)] in
/-- The result of the chord (`x₁ ≠ x₂`) addition lands on the curve: with `λ = (y₂−y₁)/(x₂−x₁)`,
`x₃ = B·λ² − A − x₁ − x₂`, `y₃ = λ·(x₁ − x₃) − y₁`, the point `(x₃, y₃)` satisfies `Equation`. -/
theorem add_some_onCurve (M : MontgomeryCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : M.Equation x₁ y₁) (h₂ : M.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    M.Equation (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂)
      ((y₂ - y₁) / (x₂ - x₁)
        * (x₁ - (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂)) - y₁) := by
  classical
  have hB := M.B_ne_zero
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  set W := (M.toWeierstrass).toAffine with hWdef
  have hxy : ¬(M.B * x₁ = M.B * x₂ ∧ M.B ^ 2 * y₁ = W.negY (M.B * x₂) (M.B ^ 2 * y₂)) :=
    fun he => hx (mul_left_cancel₀ hB he.1)
  -- Mathlib: the Weierstrass chord sum of the scaled points is on `W`.
  have hWeq := WeierstrassCurve.Affine.equation_add (M.equation_toW h₁) (M.equation_toW h₂) hxy
  -- The chord-sum X/Y coordinates equal `B·x₃` and `B²·y₃`.
  have hAX : W.addX (M.B * x₁) (M.B * x₂)
        (W.slope (M.B * x₁) (M.B * x₂) (M.B ^ 2 * y₁) (M.B ^ 2 * y₂))
      = M.B * (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂) := by
    simp only [hWdef, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [if_neg (fun he => hx (mul_left_cancel₀ hB he)), M.slope_secant_eq hB hd]
    field_simp; ring
  have hAY : W.addY (M.B * x₁) (M.B * x₂) (M.B ^ 2 * y₁)
        (W.slope (M.B * x₁) (M.B * x₂) (M.B ^ 2 * y₁) (M.B ^ 2 * y₂))
      = M.B ^ 2 * ((y₂ - y₁) / (x₂ - x₁)
          * (x₁ - (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂)) - y₁) := by
    simp only [hWdef, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [if_neg (fun he => hx (mul_left_cancel₀ hB he)), M.slope_secant_eq hB hd]
    field_simp; ring
  -- Transfer the on-`W` fact back to the Montgomery curve via `equation_ofW`.
  rw [hAX, hAY] at hWeq
  have := M.equation_ofW hWeq
  rwa [mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ (pow_ne_zero 2 hB)] at this

/-- Addition in `M.Point` in explicit coordinates, chord case (`x₁ ≠ x₂`): the Montgomery secant
addition law. With slope `λ = (y₂ − y₁)/(x₂ − x₁)`, `x₃ = B·λ² − A − x₁ − x₂`,
`y₃ = λ·(x₁ − x₃) − y₁`. -/
theorem add_some (M : MontgomeryCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : M.Equation x₁ y₁) (h₂ : M.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    (MontgomeryCurve.Point.some x₁ y₁ h₁) + (MontgomeryCurve.Point.some x₂ y₂ h₂)
      = .some (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂)
          ((y₂ - y₁) / (x₂ - x₁)
            * (x₁ - (M.B * ((y₂ - y₁) / (x₂ - x₁)) ^ 2 - M.A - x₁ - x₂)) - y₁)
          (M.add_some_onCurve h₁ h₂ hx) := by
  have hB := M.B_ne_zero
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  refine M.pointEquiv.injective ?_
  change M.pointAddEquiv (_ + _) = M.pointEquiv (.some _ _ _)
  rw [map_add]
  change M.pointEquiv (MontgomeryCurve.Point.some x₁ y₁ h₁)
    + M.pointEquiv (MontgomeryCurve.Point.some x₂ y₂ h₂) = M.pointEquiv (.some _ _ _)
  rw [M.pointEquiv_some, M.pointEquiv_some, M.pointEquiv_some]
  have hxy : ¬(M.B * x₁ = M.B * x₂ ∧
      M.B ^ 2 * y₁ = (M.toWeierstrass).toAffine.negY (M.B * x₂) (M.B ^ 2 * y₂)) := by
    rintro ⟨he, -⟩
    exact hx (mul_left_cancel₀ hB he)
  rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [if_neg (fun he => hx (mul_left_cancel₀ hB he)), M.slope_secant_eq hB hd]
    field_simp
    ring
  · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [if_neg (fun he => hx (mul_left_cancel₀ hB he)), M.slope_secant_eq hB hd]
    field_simp
    ring

omit [DecidableEq F] in
/-- The result of the tangent (doubling, `y ≠ 0`) addition lands on the curve: with
`λ = (3x² + 2Ax + 1)/(2By)`, `x₃ = B·λ² − A − 2x`, `y₃ = λ·(x − x₃) − y`. -/
theorem double_onCurve (M : MontgomeryCurve F) {x y : F} (h : M.Equation x y) (hy : y ≠ 0) :
    M.Equation (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x)
      ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)
        * (x - (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x)) - y) := by
  classical
  have hB := M.B_ne_zero
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  set W := (M.toWeierstrass).toAffine with hWdef
  have hBy : M.B ^ 2 * y ≠ 0 := mul_ne_zero (pow_ne_zero 2 hB) hy
  -- The image is *not* its own Weierstrass inverse (`y ≠ 0`), so the tangent slope is well-defined.
  have hne : M.B ^ 2 * y ≠ W.negY (M.B * x) (M.B ^ 2 * y) := by
    simp only [hWdef, WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    intro he
    have h2y : 2 * (M.B ^ 2 * y) = 0 := by linear_combination he
    exact hBy ((mul_eq_zero.mp h2y).resolve_left h2)
  have hxy : ¬(M.B * x = M.B * x ∧ M.B ^ 2 * y = W.negY (M.B * x) (M.B ^ 2 * y)) :=
    fun hc => hne hc.2
  have hWeq := WeierstrassCurve.Affine.equation_add (M.equation_toW h) (M.equation_toW h) hxy
  -- The Weierstrass tangent slope equals `B·λ`.
  have hslope : W.slope (M.B * x) (M.B * x) (M.B ^ 2 * y) (M.B ^ 2 * y)
      = M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hne]
    simp only [hWdef, WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [show M.B ^ 2 * y - (-(M.B ^ 2 * y) - 0 * (M.B * x) - 0) = 2 * M.B ^ 2 * y by ring]
    field_simp
    ring
  have hAX : W.addX (M.B * x) (M.B * x) (W.slope (M.B * x) (M.B * x) (M.B ^ 2 * y) (M.B ^ 2 * y))
      = M.B * (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x) := by
    rw [hslope]
    simp only [hWdef, WeierstrassCurve.Affine.addX, MontgomeryCurve.toWeierstrass]
    field_simp; ring
  have hAY : W.addY (M.B * x) (M.B * x) (M.B ^ 2 * y)
        (W.slope (M.B * x) (M.B * x) (M.B ^ 2 * y) (M.B ^ 2 * y))
      = M.B ^ 2 * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)
          * (x - (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x))
          - y) := by
    rw [hslope]
    simp only [hWdef, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    field_simp; ring
  rw [hAX, hAY] at hWeq
  have := M.equation_ofW hWeq
  rwa [mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ (pow_ne_zero 2 hB)] at this


/-- Doubling in `M.Point` in explicit coordinates (tangent case, `y ≠ 0`): the Montgomery doubling
law. With tangent slope `λ = (3x² + 2Ax + 1)/(2By)`, `x₃ = B·λ² − A − 2x`, `y₃ = λ·(x − x₃) − y`. -/
theorem double (M : MontgomeryCurve F) {x y : F} (h : M.Equation x y) (hy : y ≠ 0) :
    (MontgomeryCurve.Point.some x y h) + (MontgomeryCurve.Point.some x y h)
      = .some (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x)
          ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)
            * (x - (M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) ^ 2 - M.A - 2 * x)) - y)
          (M.double_onCurve h hy) := by
  have hB := M.B_ne_zero
  have hBy : M.B ^ 2 * y ≠ 0 := mul_ne_zero (pow_ne_zero 2 hB) hy
  set W := (M.toWeierstrass).toAffine with hWdef
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (M.equation_toW h)
  have hne : M.B ^ 2 * y ≠ W.negY (M.B * x) (M.B ^ 2 * y) := by
    simp only [hWdef, WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    intro he
    have h2y : 2 * (M.B ^ 2 * y) = 0 := by linear_combination he
    exact hBy ((mul_eq_zero.mp h2y).resolve_left two_ne_zero)
  refine M.pointEquiv.injective ?_
  change M.pointAddEquiv (_ + _) = M.pointEquiv (.some _ _ _)
  rw [map_add]
  change M.pointEquiv (MontgomeryCurve.Point.some x y h)
    + M.pointEquiv (MontgomeryCurve.Point.some x y h) = M.pointEquiv (.some _ _ _)
  rw [M.pointEquiv_some, M.pointEquiv_some]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' (h₁ := hns) hne,
    WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
  -- The tangent slope of the scaled point equals `B·λ`.
  have hslope : W.slope (M.B * x) (M.B * x) (M.B ^ 2 * y) (M.B ^ 2 * y)
      = M.B * ((3 * x ^ 2 + 2 * M.A * x + 1) / (2 * M.B * y)) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hne]
    simp only [hWdef, WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    rw [show M.B ^ 2 * y - (-(M.B ^ 2 * y) - 0 * (M.B * x) - 0) = 2 * M.B ^ 2 * y by ring]
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hslope]
    simp only [WeierstrassCurve.Affine.addX, MontgomeryCurve.toWeierstrass]
    field_simp; ring
  · rw [hslope]
    simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, MontgomeryCurve.toWeierstrass]
    field_simp; ring

-- Architectural stress tests: the explicit laws compose with the group structure.
example (M : MontgomeryCurve F) (P : M.Point) : P + (-P) = 0 := add_neg_cancel P

-- Commutativity of the transported group, on explicit affine points.
example (M : MontgomeryCurve F) {x₁ y₁ x₂ y₂ : F}
    (h₁ : M.Equation x₁ y₁) (h₂ : M.Equation x₂ y₂) :
    ((MontgomeryCurve.Point.some x₁ y₁ h₁) + (MontgomeryCurve.Point.some x₂ y₂ h₂)
      : M.Point)
      = (MontgomeryCurve.Point.some x₂ y₂ h₂) + (MontgomeryCurve.Point.some x₁ y₁ h₁) :=
  add_comm _ _

end MontgomeryCurve

