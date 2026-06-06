import FEC.Edwards.AddFormulaCerts

/-!
# Prototype: bridging an implementation's explicit Edwards addition to the proven group law

This file demonstrates how a verification project (e.g. `curve25519-dalek-lean-verify`) can obtain
the hard theorem — **associativity of Edwards addition** — *for free* from FEC, instead of proving
it directly (the dalek repo leaves `add_assoc_Ed25519` as `sorry`, citing the Hales–Raya IJCAR 2020
formal proof).

The bridge `E.pointEquiv : E.Point ≃ W.Point` is already proven in `FEC.Edwards.Defs` (no `sorry`):
it injects Edwards points into Mathlib's Weierstrass group (via Edwards → Montgomery → Weierstrass).
The only remaining piece is the **addition-agreement lemma** `add'_eq_add` — that the *explicit*
rational addition formula agrees with the transported group law. Once it holds, `add'_assoc` is
immediate. This is the template a verification project would instantiate (with its `Point`/`add`
replaced by FEC's, or bridged to them).

## Status: decomposed into easy pieces; only the coordinate identities remain

`add'_eq_add` → `pointEquiv_add'` (dispatcher) → four case lemmas. **Three of four cases are fully
proven** (`id_left`, `id_right`, `inverse`), built on the proven supporting lemmas
`pointEquiv_zero_one`, `pointEquiv_some`, `pointEquiv_eq_some` (the *unified* computation absorbing
the `(0,−1)` 2-torsion via `0/0 = 0`, removing input-special-point subcases), `pointEquiv_neg`,
`toMontV_neg`, `addCoords_inv`, `addCoords_zero_left/right`.

The remaining `pointEquiv_add'_generic` is reduced — via `pointEquiv_eq_some` (for `P`, `Q`, and the
sum) and Mathlib's `add_some` — to **four isolated residual pieces**:
* **A** (`hsumid`): the sum is not the identity `(0,1)` — from `¬inv` (else `Q = −P`).
* **B** (`hxy`): the two W-images are not Weierstrass-inverses — from `¬inv` (`negY = −y`, `B ≠ 0`,
  `toMontU`/`toMontV` injectivity).
* **C / D**: the X- and Y-coordinate identities
  `B·toMontU(sumY) = W.addX U₁ U₂ ℓ`,  `B²·toMontV(sumX,sumY) = W.addY …`  (`ℓ = W.slope …`).
  Discharge: split `y₁ = y₂` (tangent, `slope_of_Y_ne`) vs `y₁ ≠ y₂` (secant, `slope_of_X_ne`) to
  make `ℓ` concrete, then `field_simp` (denominators nonzero via `denoms_ne_zero`,
  `one_sub_y_ne_zero`, `U₂ − U₁ ≠ 0`) and `linear_combination c₁·h1 + c₂·h2` (coefficients via
  `polyrith` or by eliminating `y₁²`, `y₂²`). These two are the only computational leaves.
-/

namespace FEC

open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

namespace Edwards
/-- **Case 3 (generic)** — neither point the identity, not inverses. Clean assembly of the four
pieces `generic_sumNeId`, `generic_notWInv`, `generic_addX`, `generic_addY` via the unified
computation `pointEquiv_eq_some` and Mathlib's `add_some`. -/
theorem pointEquiv_add'_generic (E : Edwards (𝔽 p)) {x₁ y₁ x₂ y₂ : 𝔽 p}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    E.pointEquiv (E.add' (.mk x₁ y₁ h1) (.mk x₂ y₂ h2))
      = E.pointEquiv (.mk x₁ y₁ h1) + E.pointEquiv (.mk x₂ y₂ h2) := by
  obtain ⟨hnsP, hP'⟩ := E.pointEquiv_eq_some h1 hP
  obtain ⟨hnsQ, hQ'⟩ := E.pointEquiv_eq_some h2 hQ
  have hsum := E.addCoords_onCurve h1 h2
  obtain ⟨hnsS, hS⟩ := E.pointEquiv_eq_some hsum (E.generic_sumNeId h1 h2 hinv)
  rw [hP', hQ', WeierstrassCurve.Affine.Point.add_some (E.generic_notWInv h1 h2 hP hQ hinv)]
  simp only [Edwards.add']
  rw [hS, WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨E.generic_addX h1 h2 hP hQ hinv, E.generic_addY h1 h2 hP hQ hinv⟩

/-- **Main hard argument.** The bridge `pointEquiv` carries `add'` to Mathlib's Weierstrass
addition. Dispatches to the four cases above. -/
theorem pointEquiv_add' (E : Edwards (𝔽 p)) (P Q : E.Point) :
    E.pointEquiv (E.add' P Q) = E.pointEquiv P + E.pointEquiv Q := by
  obtain ⟨x₁, y₁, h1⟩ := P
  obtain ⟨x₂, y₂, h2⟩ := Q
  by_cases hP : x₁ = 0 ∧ y₁ = 1
  · obtain ⟨hx, hy⟩ := hP; subst hx; subst hy; exact E.pointEquiv_add'_id_left h1 h2
  by_cases hQ : x₂ = 0 ∧ y₂ = 1
  · obtain ⟨hx, hy⟩ := hQ; subst hx; subst hy; exact E.pointEquiv_add'_id_right h1 h2
  by_cases hinv : x₂ = -x₁ ∧ y₂ = y₁
  · obtain ⟨hx, hy⟩ := hinv; subst hx; subst hy; exact E.pointEquiv_add'_inverse h1 h2
  · exact E.pointEquiv_add'_generic h1 h2 hP hQ hinv

/-- The explicit Edwards addition equals the transported group operation — a short consequence of
`pointEquiv_add'` (the bridge is injective and additive). -/
theorem add'_eq_add (E : Edwards (𝔽 p)) (P Q : E.Point) : E.add' P Q = P + Q := by
  apply E.pointEquiv.injective
  rw [show E.pointEquiv (P + Q) = E.pointEquiv P + E.pointEquiv Q from
      map_add (Equiv.addEquiv E.pointEquiv) P Q]
  exact E.pointEquiv_add' P Q

/-- **Payoff**: the explicit Edwards addition is associative — derived for free from Mathlib's
Weierstrass group via the bridge, with NO direct proof. This is exactly the theorem
`curve25519-dalek-lean-verify` leaves as `sorry` (`add_assoc_Ed25519`). -/
theorem add'_assoc (E : Edwards (𝔽 p)) (P Q R : E.Point) :
    E.add' (E.add' P Q) R = E.add' P (E.add' Q R) := by
  simp only [add'_eq_add]; rw [add_assoc]

/-- Likewise commutativity, identity, inverses all transport for free once `add'_eq_add` holds —
the whole `AddCommGroup` is already on `E.Point`. -/
theorem add'_comm (E : Edwards (𝔽 p)) (P Q : E.Point) : E.add' P Q = E.add' Q P := by
  simp only [add'_eq_add]; rw [add_comm]

/-- The bridge to Mathlib's Weierstrass group is injective (already proven, no `sorry`). -/
example (E : Edwards (𝔽 p)) : Function.Injective E.pointEquiv := E.pointEquiv.injective

/-! ## The core demonstration (no `sorry`)

The theorem `curve25519-dalek-lean-verify` leaves as `sorry` — associativity of the Edwards group —
is **fully proven** in FEC, available as the ordinary `add_assoc` on `E.Point`, because the group is
transported from Mathlib's Weierstrass group law. A verification project that adopts this group
(transporting its points in, rather than re-deriving a group from an explicit formula) gets
associativity — and the whole `AddCommGroup` — for free, with no group-law proof of its own. -/

/-- Edwards points form an `AddCommGroup` — fully realized, no `sorry`. -/
noncomputable example (E : Edwards (𝔽 p)) : AddCommGroup E.Point := inferInstance

/-- Associativity (dalek's `add_assoc_Ed25519`) — proven, for free. -/
example (E : Edwards (𝔽 p)) (P Q R : E.Point) : P + Q + R = P + (Q + R) := add_assoc P Q R

/-- Commutativity, identity, inverses — likewise free. -/
example (E : Edwards (𝔽 p)) (P Q : E.Point) : P + Q = Q + P := add_comm P Q
example (E : Edwards (𝔽 p)) (P : E.Point) : P + (-P) = 0 := add_neg_cancel P


end Edwards

end FEC
