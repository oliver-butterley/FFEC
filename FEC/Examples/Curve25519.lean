import FEC.Edwards.AddFormula

/-!
# Examples: Ed25519, Curve25519, Ristretto over `𝔽 (2²⁵⁵ − 19)`

These mirror the curve definitions in `curve25519-dalek-lean-verify`, but built on **FEC** — so the
group structure (associativity included) comes *for free* by transport from Mathlib's Weierstrass
group, rather than being proved directly (which dalek leaves as `sorry`, citing Hales–Raya 2020).

* **Ed25519** — twisted Edwards `−x² + y² = 1 + d x² y²`, `d = −121665/121666`.
* **Curve25519** — Montgomery `v² = u³ + A u² + u`, `A = 486662` (`B = 1`).
* **Ristretto** — placeholder (the prime-order quotient; math model deferred).

## Assumed facts (certificate-level number theory)
Two facts about `𝔽 (2²⁵⁵−19)` are taken as `axiom`s here: **primality** of `2²⁵⁵−19` and that the
Edwards `d` is a **non-square**. In curve25519-dalek these are discharged by a Pocklington primality
certificate (`prime_cert%`) and a Legendre-symbol computation — specialized tactics not present in
plain Mathlib. They are orthogonal to the group-law content this development is about; everything
else here (the field, char ≠ 2, `−1` a square, nondegeneracy, and the **entire group structure**)
is fully proven.
-/

namespace FEC.Examples

open FEC

/-- The Curve25519 / Ed25519 base-field prime `p = 2²⁵⁵ − 19`. -/
abbrev p : ℕ := 2 ^ 255 - 19

/-- **Assumed**: `2²⁵⁵ − 19` is prime (dalek: Pocklington certificate `prime_cert%`). -/
axiom p_prime : Nat.Prime p

instance : Fact (Nat.Prime p) := ⟨p_prime⟩
instance : Fact (2 < p) := ⟨by norm_num [p]⟩

/-! ## Ed25519 (twisted Edwards) -/

/-- The Ed25519 curve constant `d = −121665 / 121666`. -/
noncomputable def edwardsD : 𝔽 p := -121665 / 121666

/-- **Assumed**: `d` is a non-square in `𝔽 p` (dalek: Legendre symbol `legendreSym p d = −1`). This
is the completeness condition that makes the Edwards addition law exception-free. -/
axiom edwardsD_not_square : ¬ IsSquare edwardsD

/-- `−1` is a square in `𝔽 p`, since `p ≡ 1 (mod 4)`. -/
theorem neg_one_is_square : IsSquare (-1 : 𝔽 p) :=
  ZMod.exists_sq_eq_neg_one_iff.mpr (by decide)

/-- **Ed25519** as a complete twisted Edwards curve in FEC: `a = −1`, `d = −121665/121666`. -/
noncomputable def Ed25519 : Edwards (𝔽 p) where
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

/-- The bridge into Mathlib's Weierstrass group (Edwards → Montgomery → Weierstrass), proven. -/
noncomputable example : Ed25519.Point ≃ (Ed25519.toMontgomery).toWeierstrass.toAffine.Point :=
  Ed25519.pointEquiv

/-! ## Curve25519 (Montgomery) -/

/-- **Curve25519** Montgomery curve `v² = u³ + 486662 u² + u` (`A = 486662`, `B = 1`). -/
noncomputable def Curve25519 : Montgomery (𝔽 p) where
  A := 486662
  B := 1
  nondegen := by
    norm_num
    decide

/-- Curve25519 points form an `AddCommGroup` — again free via FEC's Weierstrass transport. -/
noncomputable example : AddCommGroup Curve25519.Point := inferInstance

example (P Q R : Curve25519.Point) : P + Q + R = P + (Q + R) := add_assoc P Q R

/-! ## Ristretto (placeholder) -/

/-- **Ristretto** — placeholder. The Ristretto group is the prime-order quotient of Ed25519 by its
cofactor-8 subgroup (even points, `IsSquare (1 − y²)`); its FEC math model + encoding are deferred.
For now this marks the underlying curve. -/
noncomputable def Ristretto : Edwards (𝔽 p) := Ed25519

end FEC.Examples
