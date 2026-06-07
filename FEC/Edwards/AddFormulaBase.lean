import FEC.Edwards.Defs

/-! # `addFormula_eq_add`, part 1/3 — supporting lemmas (no heavy certificates).
Definitions + completeness + the bridge computation lemmas + cases A/B/identity/inverse.
Imported by `AddFormulaCerts` (the coordinate certificates) and `AddFormula` (assembly). -/


open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)]

namespace TwistedEdwardsCurve

/-- The explicit complete twisted-Edwards addition on coordinates — the formula an implementation
uses directly (cf. curve25519-dalek's `add_coords`):
`(x₁,y₁) + (x₂,y₂) = ((x₁y₂+y₁x₂)/(1+d·x₁x₂y₁y₂), (y₁y₂−a·x₁x₂)/(1−d·x₁x₂y₁y₂))`. -/
noncomputable def addCoords (E : TwistedEdwardsCurve F) (x₁ y₁ x₂ y₂ : F) : F × F :=
  ((x₁ * y₂ + y₁ * x₂) / (1 + E.d * x₁ * x₂ * y₁ * y₂),
   (y₁ * y₂ - E.a * x₁ * x₂) / (1 - E.d * x₁ * x₂ * y₁ * y₂))

omit [DecidableEq F] in
/-- **Completeness.** `λ := d·x₁x₂y₁y₂` satisfies `λ² ≠ 1` (else `d` would be a square).
Adapted from Bernstein–Birkner–Joye–Lange–Peters; the proof curve25519-dalek calls
`lam_sq_eq_one_impossible`. -/
theorem lam_sq_ne_one (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂) :
    (E.d * x₁ * x₂ * y₁ * y₂) ^ 2 ≠ 1 := by
  rw [TwistedEdwardsCurve.Equation] at h1 h2
  intro hLamSq
  set lamVal := E.d * x₁ * x₂ * y₁ * y₂ with hlam
  have hlamne : lamVal ≠ 0 := by intro h; rw [h] at hLamSq; norm_num at hLamSq
  have hx1 : x₁ ≠ 0 := fun h => hlamne (by rw [hlam, h]; ring)
  have hy1 : y₁ ≠ 0 := fun h => hlamne (by rw [hlam, h]; ring)
  have hx2 : x₂ ≠ 0 := fun h => hlamne (by rw [hlam, h]; ring)
  obtain ⟨a', ha'⟩ := E.ha
  have ha'0 : a' ≠ 0 := fun h => E.ha0 (by rw [ha', h]; ring)
  have lem1 : E.d * x₁ ^ 2 * y₁ ^ 2 * (E.a * x₂ ^ 2 + y₂ ^ 2) = E.a * x₁ ^ 2 + y₁ ^ 2 := by
    linear_combination E.d * x₁ ^ 2 * y₁ ^ 2 * h2 + hLamSq - h1
  have lem2 : (a' * x₁ + lamVal * y₁) ^ 2 = E.d * x₁ ^ 2 * y₁ ^ 2 * (a' * x₂ + y₂) ^ 2 := by
    linear_combination (E.d * x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 - x₁ ^ 2) * ha' + y₁ ^ 2 * hLamSq - lem1
  by_cases hcasePos : a' * x₂ + y₂ = 0
  · by_cases hcaseNeg : a' * x₂ - y₂ = 0
    · have h2x : 2 * a' * x₂ = 0 := by linear_combination hcasePos + hcaseNeg
      exact hx2 ((mul_eq_zero.mp h2x).resolve_left (mul_ne_zero MontgomeryCurve.two_ne_zero ha'0))
    · exact E.hd ⟨(a' * x₁ - lamVal * y₁) / (x₁ * y₁ * (a' * x₂ - y₂)), by
        rw [← sq, div_pow, eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcaseNeg))]
        linear_combination -lem2⟩
  · exact E.hd ⟨(a' * x₁ + lamVal * y₁) / (x₁ * y₁ * (a' * x₂ + y₂)), by
      rw [← sq, div_pow, eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcasePos))]
      linear_combination -lem2⟩

omit [DecidableEq F] in
/-- The TwistedEdwardsCurve addition-law denominators `1 ± d·x₁x₂y₁y₂` are nonzero
(completeness). -/
theorem denoms_ne_zero (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂) :
    (1 + E.d * x₁ * x₂ * y₁ * y₂ ≠ 0) ∧ (1 - E.d * x₁ * x₂ * y₁ * y₂ ≠ 0) := by
  have key := E.lam_sq_ne_one h1 h2
  refine ⟨fun h => key ?_, fun h => key ?_⟩
  · linear_combination (E.d * x₁ * x₂ * y₁ * y₂ - 1) * h
  · linear_combination -(E.d * x₁ * x₂ * y₁ * y₂ + 1) * h

omit [DecidableEq F] in
/-- The explicit addition lands on the curve (closure), given completeness. -/
theorem addCoords_onCurve (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂) :
    E.Equation (E.addCoords x₁ y₁ x₂ y₂).1 (E.addCoords x₁ y₁ x₂ y₂).2 := by
  obtain ⟨hpos, hneg⟩ := E.denoms_ne_zero h1 h2
  have e : x₁ * y₂ * y₁ * x₂ * E.d = E.d * x₁ * x₂ * y₁ * y₂ := by ring
  have hpos' : (1 : F) + x₁ * y₂ * y₁ * x₂ * E.d ≠ 0 := by rw [e]; exact hpos
  have hneg' : (1 : F) - x₁ * y₂ * y₁ * x₂ * E.d ≠ 0 := by rw [e]; exact hneg
  rw [TwistedEdwardsCurve.Equation] at h1 h2
  simp only [TwistedEdwardsCurve.addCoords, TwistedEdwardsCurve.Equation]
  field_simp [hpos', hneg']
  linear_combination
    ((E.a * x₂ ^ 2 + y₂ ^ 2) - E.d * x₂ ^ 2 * y₂ ^ 2 - E.d * x₂ ^ 2 * y₁ ^ 2 * y₂ ^ 2
        - E.a * x₁ ^ 2 * x₂ ^ 2 * y₂ ^ 2 * E.d + x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 * y₂ ^ 4 * E.d ^ 2
        - x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 * y₂ ^ 2 * E.d ^ 2
        + E.a * x₁ ^ 2 * x₂ ^ 4 * y₁ ^ 2 * y₂ ^ 2 * E.d ^ 2) * h1
      + (1 - x₁ ^ 2 * y₁ ^ 2 * y₂ ^ 2 * E.d - E.a * x₁ ^ 2 * x₂ ^ 2 * y₁ ^ 2 * E.d
        + x₁ ^ 4 * x₂ ^ 2 * y₁ ^ 4 * y₂ ^ 2 * E.d ^ 3) * h2

/-- The explicit TwistedEdwardsCurve addition as an operation on points
(an implementation's `add`). -/
noncomputable def addFormula (E : TwistedEdwardsCurve F) : E.Point → E.Point → E.Point
  | .mk x₁ y₁ h1, .mk x₂ y₂ h2 =>
      .mk (E.addCoords x₁ y₁ x₂ y₂).1 (E.addCoords x₁ y₁ x₂ y₂).2 (E.addCoords_onCurve h1 h2)

omit [NeZero (2 : F)] [DecidableEq F] in
/-- `(0,1)` is the additive identity of the explicit formula (a clean `field_simp` fact, used by the
identity case of `pointEquiv_addFormula`). -/
theorem addCoords_zero_left (E : TwistedEdwardsCurve F) (x y : F) :
    E.addCoords 0 1 x y = (x, y) := by
  simp [TwistedEdwardsCurve.addCoords]

omit [NeZero (2 : F)] [DecidableEq F] in
/-- Adding the identity `(0,1)` on the right returns the point. -/
theorem addCoords_zero_right (E : TwistedEdwardsCurve F) (x y : F) :
    E.addCoords x y 0 1 = (x, y) := by
  simp [TwistedEdwardsCurve.addCoords]

omit [DecidableEq F] in
/-- `(−x, y)` is the explicit inverse: `addFormula` with it returns the identity `(0,1)`. -/
theorem addCoords_inv (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (h' : E.Equation (-x) y) : E.addCoords x y (-x) y = (0, 1) := by
  obtain ⟨_, hden⟩ := E.denoms_ne_zero h h'
  rw [TwistedEdwardsCurve.Equation] at h
  simp only [TwistedEdwardsCurve.addCoords, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [div_eq_zero_iff]; left; ring
  · rw [div_eq_one_iff_eq hden]; linear_combination h

/-- **Computation lemma**: the bridge sends the TwistedEdwardsCurve identity `(0,1)` to the
Weierstrass zero. -/
theorem pointEquiv_zero_one (E : TwistedEdwardsCurve F) (h : E.Equation 0 1) :
    E.pointEquiv (TwistedEdwardsCurve.Point.mk 0 1 h) = 0 := by
  simp only [TwistedEdwardsCurve.pointEquiv, Equiv.trans_apply, TwistedEdwardsCurve.pointEquivMont,
    MontgomeryCurve.pointEquiv, Equiv.coe_fn_mk, dif_pos, if_pos]
  rfl

omit [NeZero (2 : F)] [DecidableEq F] in
/-- `toMontV` is odd in `x`: `toMontV (−x) y = −toMontV x y`. -/
theorem toMontV_neg {x y : F} (hx : x ≠ 0) (hy : (1 : F) - y ≠ 0) :
    toMontV (-x) y = -toMontV x y := by
  unfold toMontV; field_simp

/-- **Computation lemma** (feeds both remaining cases): for `x ≠ 0`, the bridge sends the affine
TwistedEdwardsCurve point `(x, y)` to the Weierstrass point with coordinates
`(B · toMontU y, B² · toMontV x y)` (`B = E.toMontgomery.B`), via
TwistedEdwardsCurve → MontgomeryCurve → Weierstrass. -/
theorem pointEquiv_some (E : TwistedEdwardsCurve F) {x y : F} (h : E.Equation x y) (hx : x ≠ 0) :
    E.pointEquiv (TwistedEdwardsCurve.Point.mk x y h) =
      .some (E.toMontgomery.B * toMontU y) (E.toMontgomery.B ^ 2 * toMontV x y)
        ((WeierstrassCurve.Affine.equation_iff_nonsingular).mp
          (MontgomeryCurve.equation_toW E.toMontgomery (E.forward_onCurve h hx))) := by
  simp only [TwistedEdwardsCurve.pointEquiv, Equiv.trans_apply, TwistedEdwardsCurve.pointEquivMont,
    MontgomeryCurve.pointEquiv, Equiv.coe_fn_mk, dif_neg hx]

/-- **The bridge respects negation**: `pointEquiv (−x, y) = −(pointEquiv (x, y))`
(TwistedEdwardsCurve negation is `(x,y) ↦ (−x, y)`; on the W side `negY = −y` as `a₁ = a₃ = 0`). -/
theorem pointEquiv_neg (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (h' : E.Equation (-x) y) :
    E.pointEquiv (TwistedEdwardsCurve.Point.mk (-x) y h')
      = -(E.pointEquiv (TwistedEdwardsCurve.Point.mk x y h)) := by
  by_cases hx : x = 0
  · subst hx
    simp only [neg_zero] at h' ⊢
    by_cases hy1 : y = 1
    · subst hy1; simp only [pointEquiv_zero_one, neg_zero]
    · -- the `(0,−1)`-type 2-torsion point: `pointEquiv = some 0 0 = −(some 0 0)`
      have key : E.pointEquiv (TwistedEdwardsCurve.Point.mk 0 y h)
          = -(E.pointEquiv (TwistedEdwardsCurve.Point.mk 0 y h)) := by
        have hc : E.pointEquiv (TwistedEdwardsCurve.Point.mk 0 y h)
            = (E.toMontgomery).pointEquiv (.some 0 0 (by simp [MontgomeryCurve.Equation])) := by
          simp only [TwistedEdwardsCurve.pointEquiv, Equiv.trans_apply,
            TwistedEdwardsCurve.pointEquivMont, Equiv.coe_fn_mk, dif_pos, if_neg hy1]
        rw [hc]
        simp only [MontgomeryCurve.pointEquiv, Equiv.coe_fn_mk, mul_zero,
          WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq,
          true_and]
        simp only [WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]; ring
      exact key
  · rw [pointEquiv_some E h' (neg_ne_zero.mpr hx), pointEquiv_some E h hx,
      WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨rfl, ?_⟩
    rw [toMontV_neg hx (E.one_sub_y_ne_zero h hx)]
    simp only [WeierstrassCurve.Affine.negY, MontgomeryCurve.toWeierstrass]
    ring

/-- **Unified computation lemma.** For *any* non-identity point `(x, y) ≠ (0,1)` — generic
(`x ≠ 0`) *or* the `(0,−1)` 2-torsion — the bridge has the same coordinate formula
`(B · toMontU y, B² · toMontV x y)`. (At `(0,−1)`: `toMontU (−1) = 0`, `toMontV 0 (−1) = 0/0 = 0`,
so the formula gives `(0,0)`, matching the 2-torsion image.) The `∃ hns` avoids writing the
Weierstrass nonsingularity proof. This absorbs all input-special-point subcases downstream. -/
theorem pointEquiv_eq_some (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (hne : ¬(x = 0 ∧ y = 1)) :
    ∃ hns, E.pointEquiv (TwistedEdwardsCurve.Point.mk x y h)
      = .some (E.toMontgomery.B * toMontU y) (E.toMontgomery.B ^ 2 * toMontV x y) hns := by
  by_cases hx : x = 0
  · subst hx
    have hy : y = -1 := by
      have hy2 : y ^ 2 = 1 := by rw [TwistedEdwardsCurve.Equation] at h; linear_combination h
      rcases mul_eq_zero.mp (show (y - 1) * (y + 1) = 0 by linear_combination hy2) with h' | h'
      · exact absurd (by linear_combination h' : y = 1) (fun hh => hne ⟨rfl, hh⟩)
      · linear_combination h'
    subst hy
    have hne1 : (-1 : F) ≠ 1 := fun hh => MontgomeryCurve.two_ne_zero (by linear_combination -hh)
    have hu : toMontU (-1 : F) = 0 := by unfold toMontU; norm_num
    have hv : toMontV (0 : F) (-1) = 0 := by unfold toMontV; simp
    rw [hu, hv, mul_zero, mul_zero]
    refine ⟨(WeierstrassCurve.Affine.equation_iff_nonsingular).mp ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.equation_zero]; rfl
    · have hc : E.pointEquiv (TwistedEdwardsCurve.Point.mk 0 (-1) h)
          = (E.toMontgomery).pointEquiv (.some 0 0 (by simp [MontgomeryCurve.Equation])) := by
        simp only [TwistedEdwardsCurve.pointEquiv, Equiv.trans_apply,
          TwistedEdwardsCurve.pointEquivMont, Equiv.coe_fn_mk, dif_pos, if_neg hne1]
      rw [hc]
      simp only [MontgomeryCurve.pointEquiv, Equiv.coe_fn_mk, mul_zero]
  · exact ⟨_, pointEquiv_some E h hx⟩

/-! ### The four cases of `pointEquiv_addFormula` (each a separate lemma) -/

/-- **Case 1a (identity, left)** — EASY: `addFormula (0,1) Q = Q` and `pointEquiv (0,1) = 0`. -/
theorem pointEquiv_addFormula_id_left (E : TwistedEdwardsCurve F) {x₂ y₂ : F}
    (h01 : E.Equation 0 1) (h2 : E.Equation x₂ y₂) :
    E.pointEquiv (E.addFormula (.mk 0 1 h01) (.mk x₂ y₂ h2))
      = E.pointEquiv (.mk 0 1 h01) + E.pointEquiv (.mk x₂ y₂ h2) := by
  have hadd : E.addFormula (.mk 0 1 h01) (.mk x₂ y₂ h2) = .mk x₂ y₂ h2 := by
    simp only [TwistedEdwardsCurve.addFormula, E.addCoords_zero_left]
  rw [hadd, pointEquiv_zero_one, zero_add]

/-- **Case 1b (identity, right)** — EASY: `addFormula P (0,1) = P`. -/
theorem pointEquiv_addFormula_id_right (E : TwistedEdwardsCurve F) {x₁ y₁ : F}
    (h1 : E.Equation x₁ y₁) (h01 : E.Equation 0 1) :
    E.pointEquiv (E.addFormula (.mk x₁ y₁ h1) (.mk 0 1 h01))
      = E.pointEquiv (.mk x₁ y₁ h1) + E.pointEquiv (.mk 0 1 h01) := by
  have hadd : E.addFormula (.mk x₁ y₁ h1) (.mk 0 1 h01) = .mk x₁ y₁ h1 := by
    simp only [TwistedEdwardsCurve.addFormula, E.addCoords_zero_right]
  rw [hadd, pointEquiv_zero_one, add_zero]

/-- **Case 2 (inverse)** — `Q = (−x, y) = −P`: `addFormula P (−P) = (0,1)` (via `addCoords_inv`)
with `pointEquiv (0,1) = 0`, while the RHS `pointEquiv P + pointEquiv (−P) = 0`
(`pointEquiv_neg`). -/
theorem pointEquiv_addFormula_inverse (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (h' : E.Equation (-x) y) :
    E.pointEquiv (E.addFormula (.mk x y h) (.mk (-x) y h'))
      = E.pointEquiv (.mk x y h) + E.pointEquiv (.mk (-x) y h') := by
  have hadd : E.addFormula (.mk x y h) (.mk (-x) y h')
      = .mk 0 1 (by simp [TwistedEdwardsCurve.Equation]) := by
    simp only [TwistedEdwardsCurve.addFormula, E.addCoords_inv h h']
  rw [hadd, pointEquiv_zero_one, E.pointEquiv_neg h h', add_neg_cancel]

omit [DecidableEq F] in
/-- **Piece A** (`hsumid`): the explicit sum is not the identity `(0,1)` — else `Q = −P`,
contradicting `¬inv`. (Contrapositive: `addCoords = (0,1) ⟹ x₂ = −x₁ ∧ y₂ = y₁`.) -/
theorem generic_sumNeId (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    ¬((E.addCoords x₁ y₁ x₂ y₂).1 = 0 ∧ (E.addCoords x₁ y₁ x₂ y₂).2 = 1) := by
  rintro ⟨hX, hY⟩
  apply hinv
  obtain ⟨hpos, hneg⟩ := E.denoms_ne_zero h1 h2
  simp only [TwistedEdwardsCurve.addCoords] at hX hY
  rw [div_eq_zero_iff] at hX
  rcases hX with hA1 | hbad
  · rw [div_eq_one_iff_eq hneg] at hY
    rw [TwistedEdwardsCurve.Equation] at h1 h2
    -- Two factorizations of the system (both pure `linear_combination`, no division):
    have hfacY : (y₂ - y₁) * (1 - E.d * x₁ ^ 2 * y₁ * y₂) = 0 := by
      linear_combination y₁ * hY - y₂ * h1 + (E.a * x₁ - E.d * x₁ * y₁ * y₂) * hA1
    have hfacX : (x₂ + x₁) * (1 + E.d * x₁ * x₂ * y₁ ^ 2) = 0 := by
      linear_combination -x₂ * h1 - x₁ * hY + (y₁ + E.d * x₁ * x₂ * y₁) * hA1
    rcases mul_eq_zero.mp hfacY with hy | hcof
    · -- **Main branch** `y₂ = y₁`: then the `hfacX` cofactor is `1 + λ ≠ 0`, forcing `x₂ = -x₁`.
      have hyeq : y₂ = y₁ := by linear_combination hy
      refine ⟨?_, hyeq⟩
      rcases mul_eq_zero.mp hfacX with hx | hcofx
      · linear_combination hx
      · exact absurd (by linear_combination hcofx + E.d * x₁ * x₂ * y₁ * hy :
          (1 : F) + E.d * x₁ * x₂ * y₁ * y₂ = 0) hpos
    · -- **Spurious branch** `1 − d·x₁²·y₁·y₂ = 0`: impossible by completeness (`hpos`/`hneg`).
      exfalso
      have hC : E.d * x₁ ^ 2 * y₁ * y₂ = 1 := by linear_combination -hcof
      rcases mul_eq_zero.mp hfacX with hx | hcofx
      · -- `x₂ = −x₁` ⟹ `λ = −1`, contradicting `hpos`.
        exact hpos (by linear_combination E.d * x₁ * y₁ * y₂ * hx - hC)
      · -- `1 + d·x₁·x₂·y₁² = 0` together with `hC` and the curve eqs forces `λ² = 1`.
        grind
  · exact absurd hbad hpos

omit [DecidableEq F] in
/-- **Piece B** (`hxy`): the two Weierstrass images are not inverses. The condition says exactly
`pointEquiv P = −(pointEquiv Q)`; since `pointEquiv` respects negation (`pointEquiv_neg`) and is
injective, this forces `P = (−x₂, y₂)`, i.e. `inv`. No raw field algebra — `negY`/`B≠0` are folded
into the already-proven `pointEquiv_some`/`pointEquiv_neg`. -/
theorem generic_notWInv (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    ¬(E.toMontgomery.B * toMontU y₁ = E.toMontgomery.B * toMontU y₂ ∧
      E.toMontgomery.B ^ 2 * toMontV x₁ y₁
        = (E.toMontgomery.toWeierstrass).toAffine.negY
            (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₂ y₂)) := by
  classical
  rintro ⟨hU, hV⟩
  apply hinv
  obtain ⟨hnsP, hPeq⟩ := E.pointEquiv_eq_some h1 hP
  obtain ⟨hnsQ, hQeq⟩ := E.pointEquiv_eq_some h2 hQ
  have h2' : E.Equation (-x₂) y₂ := by
    rw [TwistedEdwardsCurve.Equation] at h2 ⊢; linear_combination h2
  have hneg : E.pointEquiv (.mk x₁ y₁ h1) = E.pointEquiv (.mk (-x₂) y₂ h2') := by
    rw [E.pointEquiv_neg h2 h2', hPeq, hQeq, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hU, hV⟩
  have hpt := E.pointEquiv.injective hneg
  rw [TwistedEdwardsCurve.Point.mk.injEq] at hpt
  exact ⟨by rw [hpt.1]; ring, hpt.2.symm⟩

omit [NeZero (2 : F)] [DecidableEq F] in
/-- A non-identity point has `y ≠ 1` (on the curve `y = 1` forces `x = 0`, i.e. the identity). -/
theorem y_ne_one (E : TwistedEdwardsCurve F) {x y : F} (h : E.Equation x y)
    (hP : ¬(x = 0 ∧ y = 1)) :
    y ≠ 1 := by
  intro hy
  refine hP ⟨?_, hy⟩
  subst hy
  rw [TwistedEdwardsCurve.Equation] at h
  have hx2 : (E.a - E.d) * x ^ 2 = 0 := by linear_combination h
  exact (pow_eq_zero_iff (by norm_num)).mp
    ((mul_eq_zero.mp hx2).resolve_left (sub_ne_zero.mpr E.a_ne_d))


end TwistedEdwardsCurve

