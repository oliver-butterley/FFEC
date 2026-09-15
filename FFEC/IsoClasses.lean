module
public import Mathlib.FieldTheory.Finite.GaloisField

public section


/-! # Elliptic curves (over fields of characteristic `3 < p`)

Consider an elliptic curve over the field `𝔽ₚ` where the field has prime characteristic `p`. We
require that `3 < p`. Attached to any elliptic curve is the `j`-invariant. Additionally each curve
has its twist parameter `D`. Whilst `j` fixes the curve up to isomorphism over the algebraic closure
`𝔽̄ₚ`, `(j, D)` fixes the curve up to isomorphism over 𝔽.

The idea is to have an inherent concept of the curve, independent of any specific equations. Then we
have multiple different models which can be used to represent a given curve.


-/

namespace EllipticCurve

variable (p : Nat) [Fact p.Prime] [Fact (3 < p)]

notation "𝔽["p"]" => GaloisField p 1

abbrev J :=  𝔽[p] × 𝔽[p]ˣ
-- j fixes the curve up to isomorphism over the algebraic closure 𝔽̄
-- (j, D) fixes the curve up to isomorphism over 𝔽
-- (j, D, model, coordinates) specific equation

-- /-- `1728 ≠ 0` in `𝔽[p]`, because `1728 = 2⁶·3³` and `3 < p`.  This is what makes the two
-- exceptional `j`-invariants `0` and `1728` distinct, and hence `nJ` well defined by its cases. -/
-- theorem cast_1728_ne_zero : (1728 : 𝔽[p]) ≠ 0 := by
--   have hp : p.Prime := Fact.out
--   have h3 : 3 < p := Fact.out
--   intro h
--   have hdvd : p ∣ 1728 := by
--     have h' : ((1728 : ℕ) : 𝔽[p]) = 0 := by exact_mod_cast h
--     exact (CharP.cast_eq_zero_iff 𝔽[p] p 1728).mp h'
--   rw [show (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 by norm_num] at hdvd
--   rcases (Nat.Prime.dvd_mul hp).mp hdvd with h' | h' <;>
--     · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h')
--       omega

variable {p} in
/-- The order of `Aut(E)` for an elliptic curve `E/𝔽[p]` with `j`-invariant `x`, under the
assumption `3 < p`.  Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), Prop. X.5.4
(see also III.10.1 for `Aut(E)` itself).

The two exceptional cases must be tested **in `𝔽[p]`**: `(1728 : 𝔽[p])` is `1728` reduced mod `p`,
which for `p ≤ 1728` is not the natural number `1728`.  Testing a `ZMod.val` against the literal
`1728` would silently make the `j = 1728` branch unreachable for every sucEllipticCurveh `p`.

Relaxing `3 < p` is not a matter of adding cases here: in char 2 twists are additive
(Artin–Schreier `K/℘(K)`, not `Kˣ/(Kˣ)ⁿ`), and at `j = 0` in char 2 and 3 `Aut(E)` is non-abelian
(order 24, resp. 12), so the whole `(j, D)` classification fails. -/
noncomputable def nJ (x : 𝔽[p]) : Nat :=
  open Classical in
  if x = 0 then 6 else if x = 1728 then 4 else 2

variable {p}

-- omit [Fact (3 < p)] in
-- @[simp] theorem nJ_zero : nJ (0 : 𝔽[p]) = 6 := by simp [nJ]

-- @[simp] theorem nJ_1728 : nJ (1728 : 𝔽[p]) = 4 := by
--   simp [nJ, cast_1728_ne_zero p]

-- omit [Fact (3 < p)] in
-- theorem nJ_of_ne {x : 𝔽[p]} (h0 : x ≠ 0) (h1728 : x ≠ 1728) : nJ x = 2 := by
--   simp [nJ, h0, h1728]

variable (p)

instance ellRel : Setoid (J p) where
  r := fun (j₁, D₁) (j₂, D₂) ↦ j₁ = j₂ ∧ ∃ k, D₁ * D₂⁻¹ = k ^ (nJ j₁)
  iseqv := by
    constructor
    · simp only [true_and]
      intro _
      use 1
      simp
    · intro (j₁, D₁) (j₂, D₂) ⟨h1, h2⟩
      simp only at *
      refine ⟨h1.symm, ?_⟩
      obtain ⟨k, hk⟩ := h2
      use k⁻¹
      simp [inv_pow, ← hk, ← h1]
    · intro (j₁, D₁) (j₂, D₂) (j₃, D₃) ⟨hj1, hD1⟩ ⟨hj2, hD2⟩
      simp_all only [true_and]
      obtain ⟨k1, hk1⟩ := hD1
      obtain ⟨k2, hk2⟩ := hD2
      use k1 * k2
      have : (k1 * k2) ^ nJ j₃ = k1 ^ nJ j₃ * (k2 ^ nJ j₃) := by rw [mul_pow]
      rw [this, ← hk1, ← hk2, ← mul_assoc, inv_mul_cancel_right]

/-- The `𝔽[p]` isomorphism classes of elliptic curves over `𝔽[p]`. -/
abbrev IsomCl := Quotient (ellRel p)

end EllipticCurve
