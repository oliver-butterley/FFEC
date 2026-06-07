import FEC.Edwards.AddFormula
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import PrimeCert

/-!
# Examples: Ed25519, Curve25519, Ristretto over `𝔽 (2²⁵⁵ − 19)`

These mirror the curve definitions in `curve25519-dalek-lean-verify`, but built on **FEC** — so the
group structure (associativity included) comes *for free* by transport from Mathlib's Weierstrass
group, rather than being proved directly (which dalek leaves as `sorry`, citing Hales–Raya 2020).

* **Ed25519** — twisted Edwards `−x² + y² = 1 + d x² y²`, `d = −121665/121666`.
* **Curve25519** — MontgomeryCurve `v² = u³ + A u² + u`, `A = 486662` (`B = 1`).
* **Ristretto** — placeholder (the prime-order quotient; math model deferred).

## Number-theoretic facts (all proven — no axioms)
The two certificate-level facts about `𝔽 (2²⁵⁵−19)` are both proven here:
* **primality** of `2²⁵⁵−19` — `p_prime`, via a Pratt/Pocklington certificate checked by the
  `PrimeCert` dependency's `prime_cert%` elaborator;
* `d` is a **non-square** — `edwardsD_not_square`, via a Legendre-symbol computation (`norm_num`).
Together with the field, char ≠ 2, `−1` a square, nondegeneracy, and the **entire group structure**,
this development contains **no axioms** and **no `sorry`s**.
-/

namespace Examples


/-- The Curve25519 / Ed25519 base-field prime `p = 2²⁵⁵ − 19`. -/
abbrev p : ℕ := 2 ^ 255 - 19

set_option maxRecDepth 10000 in -- PrimeCert's 255-bit certificate check recurses deeply
set_option linter.style.longLine false in
/-- `2²⁵⁵ − 19` is prime, via a Pratt/Pocklington certificate checked by `PrimeCert`'s `prime_cert%`
elaborator (the certificate is dalek's, `Math/PrimeCerts.lean:19`). -/
theorem p_prime : Nat.Prime p := prime_cert%
  [small {2; 3; 5; 7; 43},
  pock3 (430751, 17, 1, 7, 2 * 5^3),
  pock3 (1923133, 2, 1, 5, 2^2 * 3 * 43),
  pock3 (31757755568855353, 10, 1, 5, 2 ^ 3 * 430751),
  pock3 (74058212732561358302231226437062788676166966415465897661863160754340907,
    2, 1, 5, 2 * 3 * 1923133 * 31757755568855353),
  pock (57896044618658097711785492504343953926634992332820282019728792003956564819949,
    2, 74058212732561358302231226437062788676166966415465897661863160754340907)]

instance : Fact (Nat.Prime p) := ⟨p_prime⟩
instance : Fact (2 < p) := ⟨by norm_num [p]⟩

/-- `2 ≠ 0` in `𝔽 p` (char ≠ 2) — the instance the generalized model layer expects. From `2 < p`. -/
instance : NeZero (2 : 𝔽 p) := ⟨by
  have hp : 2 < p := Fact.out
  have h : ((2 : ℕ) : 𝔽 p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)
  exact_mod_cast h⟩

/-! ## Ed25519 (twisted Edwards) -/

/-- The Ed25519 curve constant `d = −121665 / 121666`. -/
noncomputable def edwardsD : 𝔽 p := -121665 / 121666

/-- For `b ≠ 0` in a field, `a / b` is a square iff `a * b` is (they differ by `b²`). -/
private theorem isSquare_div_iff_mul {F : Type*} [Field F] {a b : F} (hb : b ≠ 0) :
    IsSquare (a / b) ↔ IsSquare (a * b) := by
  constructor
  · rintro ⟨r, hr⟩
    rw [div_eq_iff hb] at hr
    exact ⟨r * b, by rw [hr]; ring⟩
  · rintro ⟨s, hs⟩
    refine ⟨s / b, ?_⟩
    rw [div_mul_div_comm, ← hs, div_eq_div_iff hb (mul_ne_zero hb hb)]
    ring

/-- `d` is a non-square in `𝔽 p`: the completeness condition making the TwistedEdwardsCurve
addition law exception-free. Reduce `IsSquare (−121665/121666)` to the integer
`−121665·121666 = −14802493890`
(non-square iff `legendreSym p = −1`), then evaluate the Legendre symbol by `norm_num` (dalek's
pattern, `Math/Edwards/Curve.lean:56`). -/
theorem edwardsD_not_square : ¬ IsSquare edwardsD := by
  unfold edwardsD
  rw [isSquare_div_iff_mul (show (121666 : 𝔽 p) ≠ 0 by decide),
    show (-121665 * 121666 : 𝔽 p) = ((-14802493890 : ℤ) : 𝔽 p) by push_cast; ring]
  exact (@legendreSym.eq_neg_one_iff p _ (-14802493890)).mp (by norm_num [p])

/-- `−1` is a square in `𝔽 p`, since `p ≡ 1 (mod 4)`. -/
theorem neg_one_is_square : IsSquare (-1 : 𝔽 p) :=
  ZMod.exists_sq_eq_neg_one_iff.mpr (by decide)

/-- **Ed25519** as a complete twisted Edwards curve in FEC: `a = −1`, `d = −121665/121666`. -/
noncomputable def Ed25519 : TwistedEdwardsCurve (𝔽 p) where
  a := -1
  d := edwardsD
  ha := neg_one_is_square
  ha0 := neg_ne_zero.mpr one_ne_zero
  hd := edwardsD_not_square

/-- **The payoff** — Ed25519 points form an `AddCommGroup`, *associativity included, no `sorry`*:
exactly the theorem `curve25519-dalek-lean-verify` leaves open as `add_assoc_Ed25519`, here obtained
for free by transport from Mathlib's Weierstrass group law. -/
noncomputable example : AddCommGroup Ed25519.Point := inferInstance

example (P Q R : Ed25519.Point) : P + Q + R = P + (Q + R) := add_assoc P Q R
example (P Q : Ed25519.Point) : P + Q = Q + P := add_comm P Q
example (P : Ed25519.Point) : P + (-P) = 0 := add_neg_cancel P

/-- The bridge into Mathlib's Weierstrass group
(TwistedEdwardsCurve → MontgomeryCurve → Weierstrass), proven. -/
noncomputable example : Ed25519.Point ≃ (Ed25519.toMontgomery).toWeierstrass.toAffine.Point :=
  Ed25519.pointEquiv

/-- …and that bridge is an *additive* equivalence (a group isomorphism), via the new API. -/
noncomputable example :
    Ed25519.Point ≃+ (Ed25519.toMontgomery).toWeierstrass.toAffine.Point :=
  Ed25519.pointAddEquiv

example (P Q : Ed25519.Point) :
    Ed25519.pointAddEquiv (P + Q) = Ed25519.pointAddEquiv P + Ed25519.pointAddEquiv Q :=
  map_add _ _ _

-- `zero_def`/`neg_mk` fire as `simp` lemmas, computing the group ops in explicit coordinates.
example : (0 : Ed25519.Point) = .mk 0 1 (by rw [TwistedEdwardsCurve.Equation]; ring) := by simp
example (x y : 𝔽 p) (h : Ed25519.Equation x y) :
    -(TwistedEdwardsCurve.Point.mk x y h)
      = .mk (-x) y (by rw [TwistedEdwardsCurve.Equation] at h ⊢; linear_combination h) := by simp

/-! ## Curve25519 (MontgomeryCurve) -/

/-- **Curve25519** Montgomery curve `v² = u³ + 486662 u² + u` (`A = 486662`, `B = 1`). -/
noncomputable def Curve25519 : MontgomeryCurve (𝔽 p) where
  A := 486662
  B := 1
  nondegen := by
    rw [isUnit_iff_ne_zero]
    norm_num
    decide

/-- Curve25519 points form an `AddCommGroup` — again free via FEC's Weierstrass transport. -/
noncomputable example : AddCommGroup Curve25519.Point := inferInstance

example (P Q R : Curve25519.Point) : P + Q + R = P + (Q + R) := add_assoc P Q R
example (P Q : Curve25519.Point) :
    Curve25519.pointAddEquiv (P + Q) = Curve25519.pointAddEquiv P + Curve25519.pointAddEquiv Q :=
  map_add _ _ _
example : (0 : Curve25519.Point) = .zero := by simp

-- Base change is available (mirrors `WeierstrassCurve.map`): reduce Curve25519 along any ring hom.
example (f : 𝔽 p →+* 𝔽 p) : (Curve25519.map f).A = f 486662 := rfl

/-! ## Ristretto (placeholder) -/

/-- **Ristretto** — placeholder. The Ristretto group is the prime-order quotient of Ed25519 by its
cofactor-8 subgroup (even points, `IsSquare (1 − y²)`); its FEC math model + encoding are deferred.
For now this marks the underlying curve. -/
noncomputable def Ristretto : TwistedEdwardsCurve (𝔽 p) := Ed25519

end Examples
