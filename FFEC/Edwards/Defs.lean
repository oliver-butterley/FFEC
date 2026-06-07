import FFEC.Montgomery.Group

/-!
# TwistedEdwardsCurve model (composes through MontgomeryCurve)

A *complete* twisted Edwards curve `a x² + y² = 1 + d x² y²`, where `a` is a (nonzero) square and
`d` is a non-square. Completeness is **baked into the structure**: it is exactly the condition under
which the affine point set is the full group (no points at infinity), so that
`TwistedEdwardsCurve.Point` (affine only) biject with `MontgomeryCurve.Point` (which has the
identity at infinity). Without it the bijection `pointEquivMont` would be false. This is also the
cryptographically relevant case.

TwistedEdwardsCurve is birational to a Montgomery curve, so its only per-model datum is
`pointEquivMont : E.Point ≃ E.toMontgomery.Point`; composing with MontgomeryCurve's `pointEquiv`
and transporting reuses the Weierstrass group a second time, never re-proving it. Because
TwistedEdwardsCurve transfers to the *same* group `G = E.toMontgomery.toWeierstrass.Point` as its
Montgomery curve, the
cross-model group isomorphism `E.Point ≃+ E.toMontgomery.Point` is free (`Equiv.addEquiv`).
-/


open WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- A complete twisted Edwards curve `a x² + y² = 1 + d x² y²`: `a` a nonzero square, `d` a
non-square (the completeness condition). -/
structure TwistedEdwardsCurve (R : Type*) [CommRing R] where
  a : R
  d : R
  ha : IsSquare a
  ha0 : a ≠ 0
  hd : ¬ IsSquare d

namespace TwistedEdwardsCurve

/-- The twisted Edwards defining equation. -/
def Equation (E : TwistedEdwardsCurve R) (x y : R) : Prop :=
  E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- Points of a complete twisted Edwards curve; the identity is the affine point `(0, 1)`.
Completeness (in the structure) means these affine points form the whole group. -/
inductive Point (E : TwistedEdwardsCurve R)
  | mk (x y : R) (h : E.Equation x y)
  deriving DecidableEq

/-- `a ≠ 0` (a nonzero square, by hypothesis). -/
theorem a_ne_zero (E : TwistedEdwardsCurve R) : E.a ≠ 0 := E.ha0

/-- `d ≠ 0` (a non-square, and `0` is a square). -/
theorem d_ne_zero (E : TwistedEdwardsCurve R) : E.d ≠ 0 := by
  rintro h; exact E.hd ⟨0, by rw [h]; ring⟩

/-- `a ≠ d` (else the non-square `d` would equal the square `a`). -/
theorem a_ne_d (E : TwistedEdwardsCurve R) : E.a ≠ E.d := fun h => E.hd (h ▸ E.ha)

/-- Two points are equal once their coordinates agree (the on-curve proof is irrelevant). -/
theorem Point.ext {E : TwistedEdwardsCurve R} {x₁ y₁ : R} {h₁ : E.Equation x₁ y₁}
    {x₂ y₂ : R} {h₂ : E.Equation x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Point.mk x₁ y₁ h₁ : E.Point) = Point.mk x₂ y₂ h₂ := by subst hx; subst hy; rfl

/-- The identity `(0, 1)` makes `E.Point` inhabited. -/
instance (E : TwistedEdwardsCurve R) : Inhabited E.Point :=
  ⟨.mk 0 1 (by rw [TwistedEdwardsCurve.Equation]; ring)⟩

end TwistedEdwardsCurve

section Field

open TwistedEdwardsCurve

variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- TwistedEdwardsCurve → MontgomeryCurve: `A = 2(a+d)/(a−d)`, `B = 4/(a−d)`.
Nondegeneracy holds because `B(A²−4) = 64 a d /(a−d)³ ≠ 0` (`a,d ≠ 0`, `a ≠ d`, `char ≠ 2`). -/
noncomputable def TwistedEdwardsCurve.toMontgomery (E : TwistedEdwardsCurve F) :
    MontgomeryCurve F where
  A := 2 * (E.a + E.d) / (E.a - E.d)
  B := 4 / (E.a - E.d)
  nondegen := by
    have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
    have h64 : (64 : F) ≠ 0 := by
      have : (64 : F) = 2 ^ 6 := by norm_num
      rw [this]; exact pow_ne_zero 6 MontgomeryCurve.two_ne_zero
    have key : 4 / (E.a - E.d) * ((2 * (E.a + E.d) / (E.a - E.d)) ^ 2 - 4)
        = 64 * (E.a * E.d) / (E.a - E.d) ^ 3 := by
      field_simp
      ring
    rw [isUnit_iff_ne_zero, key]
    exact div_ne_zero (mul_ne_zero h64 (mul_ne_zero E.a_ne_zero E.d_ne_zero)) (pow_ne_zero 3 had)

/-- The `j`-invariant of a twisted Edwards curve, taken through its Montgomery (hence Weierstrass)
form. (`E.toMontgomery` is elliptic, so `MontgomeryCurve.j` is available.) -/
noncomputable def TwistedEdwardsCurve.j (E : TwistedEdwardsCurve F) : F := E.toMontgomery.j

/-! ### TwistedEdwardsCurve ⇄ MontgomeryCurve point bijection (top-down outline)

The standard birational map (Bernstein–Birkner–Joye–Lange–Peters):
  forward  `(x, y) ↦ (u, v) = ((1+y)/(1−y), (1+y)/((1−y)x))`
  backward `(u, v) ↦ (x, y) = (u/v, (u−1)/(u+1))`.

**Reasonableness check — the exceptional set is exactly two points each side**, thanks to
completeness (`a` square, `d` non-square):
* Affine TwistedEdwardsCurve points with `x = 0` are exactly `(0, 1)` and `(0, −1)` (since
  `x²(a−d) = 0`, `a ≠ d`); and `y = 1 ⟺ (0,1)`, `y = −1 ⟺ (0,−1)`. So `x ≠ 0 ⟺ y ∉ {1, −1}`, and
  the forward
  denominators `1−y`, `x` are then nonzero.
* On `E.toMontgomery`, `A²−4 = 16 a d /(a−d)²` is a **non-square** (`a` square · `d` non-square ⇒
  `a d` non-square), so `u² + A u + 1 = 0` has no roots ⇒ the only affine 2-torsion is `(0, 0)`.
  Also `u = −1` would force `v² = d` (a non-square) ⇒ no such point. So backward denominators
  `v`, `u+1` are nonzero off `(0,0)`.
Hence the bijection is: `(0,1) ↔ ∞`, `(0,−1) ↔ (0,0)`, and the generic rational map elsewhere.

**Decomposition (all parts now proven):**
  (a) forward lands on MontgomeryCurve (`forward_onCurve`);  (b) backward lands on
  TwistedEdwardsCurve (`backward_onCurve`);  (c) special points on-curve;  (d) `left_inv`;
  (e) `right_inv`.
Supporting: `one_sub_y_ne_zero`, `one_add_y_ne_zero`, `u_add_one_ne_zero`, `no_root`, and the four
round-trip identities `ofMontX_toMont`/`ofMontY_toMont`/`toMontU_ofMont`/`toMontV_ofMont`. -/

/-- Forward affine coordinates `TwistedEdwardsCurve → MontgomeryCurve` (generic case, `x ≠ 0`). -/
noncomputable def toMontU (y : F) : F := (1 + y) / (1 - y)
noncomputable def toMontV (x y : F) : F := (1 + y) / ((1 - y) * x)
/-- Backward affine coordinates `MontgomeryCurve → TwistedEdwardsCurve`
(generic case, `v ≠ 0`, `u ≠ −1`). -/
noncomputable def ofMontX (u v : F) : F := u / v
noncomputable def ofMontY (u : F) : F := (u - 1) / (u + 1)

omit [NeZero (2 : F)] in
/-- `1 - y ≠ 0` generically: `y = 1` would force `x = 0` (via `(a−d)x² = 0`). -/
theorem TwistedEdwardsCurve.one_sub_y_ne_zero (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (hx : x ≠ 0) : 1 - y ≠ 0 := by
  intro hy
  rw [sub_eq_zero] at hy
  rw [TwistedEdwardsCurve.Equation, ← hy] at h
  have key : (E.a - E.d) * x ^ 2 = 0 := by linear_combination h
  have hx2 : x ^ 2 = 0 := (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr E.a_ne_d)
  exact hx ((pow_eq_zero_iff (by norm_num)).mp hx2)

omit [NeZero (2 : F)] in
/-- `1 + y ≠ 0` generically: `y = −1` would force `x = 0`. -/
theorem TwistedEdwardsCurve.one_add_y_ne_zero (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (hx : x ≠ 0) : 1 + y ≠ 0 := by
  intro hy
  have hy' : y = -1 := by linear_combination hy
  rw [TwistedEdwardsCurve.Equation, hy'] at h
  have key : (E.a - E.d) * x ^ 2 = 0 := by linear_combination h
  have hx2 : x ^ 2 = 0 := (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr E.a_ne_d)
  exact hx ((pow_eq_zero_iff (by norm_num)).mp hx2)

/-- (a) Forward map lands on the Montgomery curve (generic `x ≠ 0`). -/
theorem TwistedEdwardsCurve.forward_onCurve (E : TwistedEdwardsCurve F) {x y : F}
    (h : E.Equation x y) (hx : x ≠ 0) :
    (E.toMontgomery).Equation (toMontU y) (toMontV x y) := by
  have hy1 := E.one_sub_y_ne_zero h hx
  have hy2 := E.one_add_y_ne_zero h hx
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [TwistedEdwardsCurve.Equation] at h
  simp only [MontgomeryCurve.Equation, TwistedEdwardsCurve.toMontgomery, toMontU, toMontV]
  field_simp
  linear_combination -4 * h

/-- `u + 1 ≠ 0` on the Montgomery curve: `u = −1` would give `v² = d`, a non-square. -/
theorem TwistedEdwardsCurve.u_add_one_ne_zero (E : TwistedEdwardsCurve F) {u v : F}
    (hM : (E.toMontgomery).Equation u v) : u + 1 ≠ 0 := by
  intro hu
  have hu' : u = -1 := by linear_combination hu
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  apply E.hd
  refine ⟨v, ?_⟩
  rw [MontgomeryCurve.Equation, TwistedEdwardsCurve.toMontgomery, hu'] at hM
  field_simp at hM
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero 2 MontgomeryCurve.two_ne_zero
  have h4d : (4 : F) * E.d = 4 * (v * v) := by linear_combination -hM
  exact mul_left_cancel₀ h4 h4d

/-- (b) Backward map lands on the TwistedEdwardsCurve curve (generic `v ≠ 0`). -/
theorem TwistedEdwardsCurve.backward_onCurve (E : TwistedEdwardsCurve F) {u v : F}
    (hM : (E.toMontgomery).Equation u v) (hv : v ≠ 0) :
    E.Equation (ofMontX u v) (ofMontY u) := by
  have hu1 := E.u_add_one_ne_zero hM
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  simp only [MontgomeryCurve.Equation, TwistedEdwardsCurve.toMontgomery] at hM
  field_simp at hM
  simp only [TwistedEdwardsCurve.Equation, ofMontX, ofMontY]
  field_simp
  linear_combination -u * hM

/-! Round-trip coordinate identities (the content of `left_inv`/`right_inv`). -/

omit [NeZero (2 : F)] in
theorem TwistedEdwardsCurve.ofMontX_toMont {x y : F} (hx : x ≠ 0) (hy1 : 1 - y ≠ 0)
    (hy2 : 1 + y ≠ 0) :
    ofMontX (toMontU y) (toMontV x y) = x := by
  unfold ofMontX toMontU toMontV; field_simp

theorem TwistedEdwardsCurve.ofMontY_toMont {y : F} (hy1 : 1 - y ≠ 0) :
    ofMontY (toMontU y) = y := by
  have h2 : (2 : F) ≠ 0 := MontgomeryCurve.two_ne_zero
  unfold ofMontY toMontU; field_simp
  rw [div_eq_iff (by intro hc; exact h2 (by linear_combination hc))]; ring

theorem TwistedEdwardsCurve.toMontU_ofMont {u : F} (hu1 : u + 1 ≠ 0) :
    toMontU (ofMontY u) = u := by
  have h2 : (2 : F) ≠ 0 := MontgomeryCurve.two_ne_zero
  unfold toMontU ofMontY; field_simp
  rw [div_eq_iff (by intro hc; exact h2 (by linear_combination hc))]; ring

theorem TwistedEdwardsCurve.toMontV_ofMont {u v : F} (hu0 : u ≠ 0) (hv : v ≠ 0) (hu1 : u + 1 ≠ 0) :
    toMontV (ofMontX u v) (ofMontY u) = v := by
  have h2 : (2 : F) ≠ 0 := MontgomeryCurve.two_ne_zero
  unfold toMontV ofMontX ofMontY; field_simp
  rw [div_eq_iff (by intro hc; exact h2 (by linear_combination hc))]; ring

/-- The Montgomery curve has no rational 2-torsion beyond `(0,0)`: `u² + A u + 1 ≠ 0`.
(`u² + A u + 1 = 0` ⟹ `(2u+A)² = A²−4 = 16ad/(a−d)²`, making `d` a square — contradicting `hd`.) -/
theorem TwistedEdwardsCurve.no_root (E : TwistedEdwardsCurve F) (u : F) :
    u ^ 2 + E.toMontgomery.A * u + 1 ≠ 0 := by
  intro hq
  obtain ⟨s, hs⟩ := E.ha
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  have hs0 : s ≠ 0 := fun hh => E.a_ne_zero (by rw [hs, hh]; ring)
  have h2 : (2 : F) ≠ 0 := MontgomeryCurve.two_ne_zero
  simp only [TwistedEdwardsCurve.toMontgomery] at hq
  apply E.hd
  refine ⟨((E.a - E.d) * u + E.a + E.d) / (2 * s), ?_⟩
  field_simp at hq ⊢
  linear_combination -(E.a - E.d) * hq - 4 * E.d * hs

-- the bridge/group decls below use Mathlib's affine-point group, which needs `DecidableEq`
variable [DecidableEq F]

/-- **The per-model datum**: the birational bijection `E.Point ≃ E.toMontgomery.Point`. -/
noncomputable def TwistedEdwardsCurve.pointEquivMont (E : TwistedEdwardsCurve F) :
    E.Point ≃ (E.toMontgomery).Point where
  toFun P := match P with
    | .mk x y h =>
        if hx : x = 0 then
          if y = 1 then .zero                        -- (0,1)  ↦ ∞
          else .some 0 0 (by simp [MontgomeryCurve.Equation])  -- (0,−1) ↦ (0,0)   [(c) ✓]
        else
          .some (toMontU y) (toMontV x y) (E.forward_onCurve h hx)   -- [(a)]
  invFun P := match P with
    | .zero => .mk 0 1 (by simp [TwistedEdwardsCurve.Equation])  -- ∞     ↦ (0,1)    [(c) ✓]
    | .some u v h =>
        -- (0,0) ↦ (0,−1)  [(c) ✓]
        if hv : v = 0 then .mk 0 (-1) (by simp [TwistedEdwardsCurve.Equation])
        else .mk (ofMontX u v) (ofMontY u) (E.backward_onCurve h hv)  -- [(b)]
  left_inv := by
    rintro ⟨x, y, h⟩
    by_cases hx : x = 0
    · subst hx
      have hyeq : y ^ 2 = 1 := by rw [TwistedEdwardsCurve.Equation] at h; linear_combination h
      by_cases hy : y = 1
      · subst hy; simp
      · have hy' : y = -1 := by
          rcases mul_eq_zero.mp (show (y - 1) * (y + 1) = 0 by linear_combination hyeq) with h1 | h2
          · exact absurd (by linear_combination h1) hy
          · linear_combination h2
        subst hy'; simp only [if_neg hy]; simp
    · have hy1 := E.one_sub_y_ne_zero h hx
      have hy2 := E.one_add_y_ne_zero h hx
      have hVne : toMontV x y ≠ 0 := div_ne_zero hy2 (mul_ne_zero hy1 hx)
      simp only [dif_neg hx, dif_neg hVne]
      simp only [ofMontX_toMont hx hy1 hy2, ofMontY_toMont hy1]
  right_inv := by
    have hne : (-1 : F) ≠ 1 := fun hh => MontgomeryCurve.two_ne_zero (by linear_combination -hh)
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 ^ 2 := by norm_num
      rw [this]; exact pow_ne_zero 2 MontgomeryCurve.two_ne_zero
    have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
    have hBne : E.toMontgomery.B ≠ 0 := by
      rw [TwistedEdwardsCurve.toMontgomery]; exact div_ne_zero h4 had
    rintro (_ | ⟨u, v, hM⟩)
    · simp
    · by_cases hv : v = 0
      · have hu0 : u = 0 := by
          have key : u * (u ^ 2 + E.toMontgomery.A * u + 1) = 0 := by
            rw [MontgomeryCurve.Equation, hv] at hM; linear_combination -hM
          exact (mul_eq_zero.mp key).resolve_right (E.no_root u)
        subst hv; subst hu0; simp [if_neg hne]
      · have hu0 : u ≠ 0 := by
          intro hu; subst hu
          rw [MontgomeryCurve.Equation] at hM
          have hBv : E.toMontgomery.B * v ^ 2 = 0 := by linear_combination hM
          exact hv ((pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp hBv).resolve_left hBne))
        have hu1 := E.u_add_one_ne_zero hM
        have hx' : ofMontX u v ≠ 0 := div_ne_zero hu0 hv
        simp only [dif_neg hv, dif_neg hx']
        simp only [toMontU_ofMont hu1, toMontV_ofMont hu0 hv hu1]

/-- Compose to the Weierstrass anchor: `TwistedEdwardsCurve ≃ MontgomeryCurve ≃ Weierstrass`. -/
noncomputable def TwistedEdwardsCurve.pointEquiv (E : TwistedEdwardsCurve F) :
    E.Point ≃ (E.toMontgomery).toWeierstrass.toAffine.Point :=
  E.pointEquivMont.trans (E.toMontgomery).pointEquiv

/-- The TwistedEdwardsCurve point group, transported through MontgomeryCurve to Weierstrass.
Group reused, not re-proved. -/
noncomputable instance (E : TwistedEdwardsCurve F) : AddCommGroup E.Point :=
  E.pointEquiv.addCommGroup

/-- **Cross-model group isomorphism** `E.Point ≃+ E.toMontgomery.Point`, *free* because both
transfer to the same group `G = E.toMontgomery.toWeierstrass.Point`. No addition formulas needed. -/
noncomputable def TwistedEdwardsCurve.toMontgomeryAddEquiv (E : TwistedEdwardsCurve F) :
    E.Point ≃+ (E.toMontgomery).Point :=
  (Equiv.addEquiv E.pointEquiv).trans (Equiv.addEquiv (E.toMontgomery).pointEquiv).symm

end Field

