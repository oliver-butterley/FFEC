import FEC.Edwards.AddFormulaCerts

/-!
# TwistedEdwardsCurve explicit addition agrees with the transported Weierstrass group law

This file proves that the **explicit** (rational) twisted-Edwards addition formula agrees with the
group operation transported from Mathlib's Weierstrass group along the bridge
`E.pointEquiv : E.Point ≃ W.Point` (built in `FEC.Edwards.Defs` via
TwistedEdwardsCurve → MontgomeryCurve → Weierstrass). The agreement lemma `addFormula_eq_add` then
yields **associativity of TwistedEdwardsCurve addition for free** (`addFormula_assoc`) — the exact
theorem `curve25519-dalek-lean-verify` leaves as `sorry`
(`add_assoc_Ed25519`, citing the Hales–Raya IJCAR 2020 formal proof). A verification project adopts
this by transporting its points into `E.Point` (or bridging to it).

## Structure of the proof

`addFormula_eq_add` ← `pointEquiv_addFormula` (dispatcher) ← four case lemmas, all fully proven:
* `pointEquiv_addFormula_id_left` / `id_right` / `inverse` — the identity and inverse cases, built
  on `pointEquiv_eq_some` (a *unified* computation absorbing the `(0,−1)` 2-torsion via `0/0 = 0`),
  `pointEquiv_neg`, `toMontV_neg`, `addCoords_inv`, `addCoords_zero_left/right`.
* `pointEquiv_addFormula_generic` — neither point the identity, not inverses. Reduced via
  `pointEquiv_eq_some` and Mathlib's `add_some` to four residual pieces (in `AddFormulaBase` and
  `AddFormulaCerts`):
  - **A** `generic_sumNeId`: the sum is not the identity `(0,1)`.
  - **B** `generic_notWInv`: the two W-images are not Weierstrass-inverses.
  - **C** `generic_addX` / **D** `generic_addY`: the X- and Y-coordinate identities, discharged by
    splitting tangent (`slope_of_Y_ne`) vs secant (`slope_of_X_ne`), `field_simp`, and a
    `linear_combination` with Singular-computed cofactors that `ring` re-checks.
-/


open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)]

namespace TwistedEdwardsCurve
/-- **Case 3 (generic)** — neither point the identity, not inverses. Clean assembly of the four
pieces `generic_sumNeId`, `generic_notWInv`, `generic_addX`, `generic_addY` via the unified
computation `pointEquiv_eq_some` and Mathlib's `add_some`. -/
theorem pointEquiv_addFormula_generic (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    E.pointEquiv (E.addFormula (.mk x₁ y₁ h1) (.mk x₂ y₂ h2))
      = E.pointEquiv (.mk x₁ y₁ h1) + E.pointEquiv (.mk x₂ y₂ h2) := by
  obtain ⟨hnsP, hP'⟩ := E.pointEquiv_eq_some h1 hP
  obtain ⟨hnsQ, hQ'⟩ := E.pointEquiv_eq_some h2 hQ
  have hsum := E.addCoords_onCurve h1 h2
  obtain ⟨hnsS, hS⟩ := E.pointEquiv_eq_some hsum (E.generic_sumNeId h1 h2 hinv)
  rw [hP', hQ', WeierstrassCurve.Affine.Point.add_some (E.generic_notWInv h1 h2 hP hQ hinv)]
  simp only [TwistedEdwardsCurve.addFormula]
  rw [hS, WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨E.generic_addX h1 h2 hP hQ hinv, E.generic_addY h1 h2 hP hQ hinv⟩

/-- **Main hard argument.** The bridge `pointEquiv` carries `addFormula` to Mathlib's Weierstrass
addition. Dispatches to the four cases above. -/
theorem pointEquiv_addFormula (E : TwistedEdwardsCurve F) (P Q : E.Point) :
    E.pointEquiv (E.addFormula P Q) = E.pointEquiv P + E.pointEquiv Q := by
  obtain ⟨x₁, y₁, h1⟩ := P
  obtain ⟨x₂, y₂, h2⟩ := Q
  by_cases hP : x₁ = 0 ∧ y₁ = 1
  · obtain ⟨hx, hy⟩ := hP; subst hx; subst hy; exact E.pointEquiv_addFormula_id_left h1 h2
  by_cases hQ : x₂ = 0 ∧ y₂ = 1
  · obtain ⟨hx, hy⟩ := hQ; subst hx; subst hy; exact E.pointEquiv_addFormula_id_right h1 h2
  by_cases hinv : x₂ = -x₁ ∧ y₂ = y₁
  · obtain ⟨hx, hy⟩ := hinv; subst hx; subst hy; exact E.pointEquiv_addFormula_inverse h1 h2
  · exact E.pointEquiv_addFormula_generic h1 h2 hP hQ hinv

/-- The explicit TwistedEdwardsCurve addition equals the transported group operation — a short
consequence of `pointEquiv_addFormula` (the bridge is injective and additive). -/
theorem addFormula_eq_add (E : TwistedEdwardsCurve F) (P Q : E.Point) :
    E.addFormula P Q = P + Q := by
  apply E.pointEquiv.injective
  rw [show E.pointEquiv (P + Q) = E.pointEquiv P + E.pointEquiv Q from
      map_add (Equiv.addEquiv E.pointEquiv) P Q]
  exact E.pointEquiv_addFormula P Q

-- `DecidableEq F` is used in the proof (Mathlib's point group) though not in this statement's type.
set_option linter.unusedDecidableInType false in
/-- **Payoff**: the explicit twisted-Edwards addition is associative — derived for free from
Mathlib's Weierstrass group via the bridge, with NO direct proof. This is exactly the theorem
`curve25519-dalek-lean-verify` leaves as `sorry` (`add_assoc_Ed25519`). -/
theorem addFormula_assoc (E : TwistedEdwardsCurve F) (P Q R : E.Point) :
    E.addFormula (E.addFormula P Q) R = E.addFormula P (E.addFormula Q R) := by
  simp only [addFormula_eq_add]; rw [add_assoc]

set_option linter.unusedDecidableInType false in
/-- Likewise commutativity, identity, inverses all transport for free once `addFormula_eq_add`
holds — the whole `AddCommGroup` is already on `E.Point`. -/
theorem addFormula_comm (E : TwistedEdwardsCurve F) (P Q : E.Point) :
    E.addFormula P Q = E.addFormula Q P := by
  simp only [addFormula_eq_add]; rw [add_comm]

/-! ## Group API in explicit coordinates -/

/-- The transport bridge `E.Point ≃ W.Point` as an **additive** equivalence (Edwards → Montgomery →
Weierstrass): the group is the transport along `pointEquiv`, so this is a group isomorphism by
construction. -/
noncomputable def pointAddEquiv (E : TwistedEdwardsCurve F) :
    E.Point ≃+ (E.toMontgomery).toWeierstrass.toAffine.Point :=
  Equiv.addEquiv E.pointEquiv

/-- The group identity of `E.Point` is the affine point `(0, 1)`. -/
@[simp] theorem zero_def (E : TwistedEdwardsCurve F) :
    (0 : E.Point) = .mk 0 1 (by rw [TwistedEdwardsCurve.Equation]; ring) := by
  refine E.pointEquiv.injective ?_
  change E.pointAddEquiv 0 = E.pointEquiv (.mk 0 1 _)
  rw [map_zero, E.pointEquiv_zero_one]

/-- Negation in `E.Point` is the twisted-Edwards inverse `(x, y) ↦ (−x, y)`. -/
@[simp] theorem neg_mk (E : TwistedEdwardsCurve F) {x y : F} (h : E.Equation x y) :
    -(TwistedEdwardsCurve.Point.mk x y h)
      = .mk (-x) y (by rw [TwistedEdwardsCurve.Equation] at h ⊢; linear_combination h) := by
  refine E.pointEquiv.injective ?_
  change E.pointAddEquiv (-(TwistedEdwardsCurve.Point.mk x y h)) = E.pointEquiv (.mk (-x) y _)
  rw [map_neg, E.pointEquiv_neg h]
  rfl

/-- The bridge to Mathlib's Weierstrass group is injective (already proven, no `sorry`). -/
example (E : TwistedEdwardsCurve F) : Function.Injective E.pointEquiv := E.pointEquiv.injective

/-! ## The core demonstration (no `sorry`)

The theorem `curve25519-dalek-lean-verify` leaves as `sorry` — associativity of the
TwistedEdwardsCurve group — is **fully proven** in FEC, available as the ordinary `add_assoc` on
`E.Point`, because the group is
transported from Mathlib's Weierstrass group law. A verification project that adopts this group
(transporting its points in, rather than re-deriving a group from an explicit formula) gets
associativity — and the whole `AddCommGroup` — for free, with no group-law proof of its own. -/

/-- TwistedEdwardsCurve points form an `AddCommGroup` — fully realized, no `sorry`. -/
noncomputable example (E : TwistedEdwardsCurve F) : AddCommGroup E.Point := inferInstance

/-- Associativity (dalek's `add_assoc_Ed25519`) — proven, for free. -/
example (E : TwistedEdwardsCurve F) (P Q R : E.Point) : P + Q + R = P + (Q + R) := add_assoc P Q R

/-- Commutativity, identity, inverses — likewise free. -/
example (E : TwistedEdwardsCurve F) (P Q : E.Point) : P + Q = Q + P := add_comm P Q
example (E : TwistedEdwardsCurve F) (P : E.Point) : P + (-P) = 0 := add_neg_cancel P


end TwistedEdwardsCurve

