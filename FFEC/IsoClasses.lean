module
public import Mathlib.FieldTheory.Finite.GaloisField

public section

variable (p : Nat) [Fact p.Prime] [Fact (3 < p)]

notation "𝔽["p"]" => GaloisField p 1

abbrev J :=  𝔽[p] × 𝔽[p]ˣ
-- (j, D) : J
-- j fixes the curve up to iso — over the algebraic closure 𝔽̄
-- (j, D) fixes the curve up to iso — over 𝔽
-- (j, D, model, coordinates) specific equation

variable {p} in
/-- The order of the `Aut(E)` for an elliptic curve `E/K` under the assumption that `3 < char(K)`.
Silverman 1986, Theorem 10.1. -/
noncomputable def nJ (x : 𝔽[p]) : Nat :=
  match (GaloisField.equivZmodP p x).val with
  | 0 => 6
  | 1728 => 4
  | _ => 2
  -- More options if we relax the requirement that `3 < p`

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

abbrev EllipticCurveUpToIso := Quotient (ellRel p)
