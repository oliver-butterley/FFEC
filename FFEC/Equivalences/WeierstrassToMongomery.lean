module
public import FFEC.Montgomery
public import FFEC.IsoClasses
public import Mathlib

public section

variable (p : Nat) [Fact p.Prime]

/- TODO: move the info about `WeierstrassCurve` to an appropriate home. -/

/- We have to do this or open Classical in each of the following three. -/
noncomputable instance : DecidableEq 𝔽[p] := Classical.decEq _

noncomputable def WeierstrassOfJ (J : IsomCl p) : WeierstrassCurve 𝔽[p] :=
  WeierstrassCurve.ofJ (Quotient.out J).1

variable (J : IsomCl p)

instance : (WeierstrassOfJ p J).IsElliptic :=
  inferInstanceAs (WeierstrassCurve.ofJ (Quotient.out J).1).IsElliptic

theorem j_of_WeierstrassOfJ : (WeierstrassOfJ p J).j = (Quotient.out J).1 :=
  WeierstrassCurve.ofJ_j _

/-! Weierstrass to Montgomery

TODO: spec about D? -/

/- TODO: extend to CommRing -/
def MontgomeryCurve.j {R : Type*} [Field R] (M : MontgomeryCurve R) : R :=
  256 * ((M.A ^ 2) - 3)^3 / (M.A ^ 2 - 4)

variable [Fact (3 < p)]

-- /-- The class `J` admits a Montgomery `A`-parameter over `𝔽[p]`: the inversion cubic
-- `256·(A²−3)³ = j·(A²−4)` has a *nondegenerate* root in the field.  Not every class satisfies
-- this — the cubic in `A²` need not have a square root in `𝔽[p]` — which is exactly why
-- `j_of_MontgomeryCurveOfJ` below carries this as a hypothesis. -/
-- def HasMontgomeryParam (ic : IsomCl p) : Prop :=
--   ∃ a : 𝔽[p], a ^ 2 - 4 ≠ 0 ∧ 256 * (a ^ 2 - 3) ^ 3 / (a ^ 2 - 4) = (Quotient.out ic).1

-- /-- **The inversion is genuinely partial.**  There is a `j ∈ 𝔽[p]` attained by *no* `A`: the
-- map `a ↦ 256·(a²−3)³/(a²−4)` factors through `a ↦ a²`, so it identifies `1` and `-1` and is
-- not injective; on the finite field `𝔽[p]` a non-injective self-map is non-surjective. -/
-- theorem exists_j_not_in_montgomery_image :
--     ∃ j : 𝔽[p], ∀ a : 𝔽[p], 256 * (a ^ 2 - 3) ^ 3 / (a ^ 2 - 4) ≠ j := by
--   have h2 : (2 : 𝔽[p]) ≠ 0 := by
--     have h3 : 3 < p := Fact.out
--     intro h
--     have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff 𝔽[p] p 2).mp (by exact_mod_cast h)
--     have := Nat.le_of_dvd (by norm_num) hdvd
--     omega
--   have hne : (1 : 𝔽[p]) ≠ -1 := fun h => h2 (by linear_combination h)
--   have hns : ¬ Function.Surjective (fun a : 𝔽[p] => 256 * (a ^ 2 - 3) ^ 3 / (a ^ 2 - 4)) := by
--     rw [← Finite.injective_iff_surjective]
--     intro hinj
--     exact hne (hinj (by dsimp only; ring))
--   simp only [Function.Surjective, not_forall, not_exists] at hns
--   obtain ⟨j, hj⟩ := hns
--   exact ⟨j, hj⟩

-- /-- Consequently no Montgomery curve over `𝔽[p]` has that `j`-invariant, so an *unconditional*
-- `j_of_MontgomeryCurveOfJ` (dropping the `HasMontgomeryParam` hypothesis) is unprovable. -/
-- theorem exists_j_no_montgomeryCurve :
--     ∃ j : 𝔽[p], ∀ M : MontgomeryCurve 𝔽[p], MontgomeryCurve.j M ≠ j := by
--   obtain ⟨j, hj⟩ := exists_j_not_in_montgomery_image p
--   exact ⟨j, fun M => hj M.A⟩
open MontgomeryCurve

open Classical in
/-- A Montgomery model for the class `J`.  When `J` admits a Montgomery parameter we pick a
genuine root `A` (so the `j`-invariant is correct, see `j_of_MontgomeryCurveOfJ`) and take `B`
to be a representative of the twist `D = (Quotient.out J).2`.  Otherwise we return a
nondegenerate fallback curve (`A = 0`, `B = 1`), whose `j` is *not* `J`'s. -/
noncomputable def MontgomeryCurveOfJ (α : AdmissibleIsomCl p) : MontgomeryCurve 𝔽[p] :=
  { A := 0
    B := 1
    nondegen := by
      have h4 : (4 : 𝔽[p]) ≠ 0 := by
        have hp : p.Prime := Fact.out
        have h3 : 3 < p := Fact.out
        intro h4
        have hdvd : p ∣ 4 :=
          (CharP.cast_eq_zero_iff 𝔽[p] p 4).mp (by exact_mod_cast h4)
        have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        have hpeq : p = 4 := by omega
        rw [hpeq] at hp
        exact absurd hp (by decide)
      have he : (1 : 𝔽[p]) * ((0 : 𝔽[p]) ^ 2 - 4) = -4 := by ring
      rw [he, isUnit_iff_ne_zero, neg_ne_zero]
      exact h4 }
-- TODO: check the above and correct. Why isn't α used?

/-- The `j`-invariant of `MontgomeryCurveOfJ` is correct **provided** the class admits a
Montgomery parameter.  This cannot be dropped: a class whose inversion cubic has no square
root in `𝔽[p]` has no Montgomery model at all, so the fallback curve's `j` differs. -/
theorem j_of_MontgomeryCurveOfJ (α : AdmissibleIsomCl p) :
    (MontgomeryCurveOfJ p J).j = (Quotient.out J).1 := by
  unfold MontgomeryCurve.j MontgomeryCurveOfJ
  rw [dif_pos h]
  exact h.choose_spec.2
-- TODO: correct this

/-- The point sets of the Weierstrass and Montgomery models are in bijection.

TODO: this is only a genuine isomorphism when `HasMontgomeryParam p J` holds (otherwise the two
curves have different `j`-invariants and are not isomorphic).  Even then it requires the explicit
Weierstrass ↔ Montgomery coordinate change (`x ↦ B·u − A/3`, etc.). -/
def Weierstrass.toMontgomeryCurve : WeierstrassCurve.Affine.Point (WeierstrassOfJ p J) ≃
    MontgomeryCurve.Point (MontgomeryCurveOfJ p J) := by
  sorry
-- TODO: insert explict formula for this. Probably by cases for point at infinity.


-- TODO: are there several different montgomery representations for the same elliptic curve?

/- TODO (LATER): all the moving of group structure from place to place...
READ: hope to use the fact that any two group structures of a given montgomery model
which share the same identity are the same group structure.
This is true for weierstrass (is it in mathlib?). -/

-- TODO (LATER): design all the api for working with the models and moving between them.
