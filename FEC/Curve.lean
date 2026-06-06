import FEC.Framework

/-!
# The abstract elliptic curve (organizing hub)

An abstract elliptic curve over `R` is an isomorphism class, identified by its `j`-invariant
together with a twist `D` (Silverman X.5 Cor 5.4.1: iso classes ↔ `(j, D)/∼`). It is realized
*canonically* by a Weierstrass curve `W(c)`; every concrete model attaches to the hub by computing
its `j` forward and proving `toWeierstrass ≅ W(c)`.

The curve's group is the (Mathlib-provided) group of `W(c).Point` — which *is* `Pic⁰` on the `|3·O|`
model. No model is privileged in any statement: the per-model datum is the **canonical** Abel–Jacobi
map `ι : P ↦ [(P) − (O)]`, and the group is determined by it (uniqueness, below). Weierstrass merely
*anchors existence* of the group structure.
-/

namespace FEC

open WeierstrassCurve

/-- An abstract elliptic curve over `R`, as an iso class identified by `j` and a twist `D`. -/
structure Curve (R : Type*) [CommRing R] where
  j : R
  D : Rˣ

namespace Curve

variable {R : Type*} [CommRing R]

/-- `n(j) = #Aut(E) ∈ {2,4,6}`: `6` at `j = 0`, `4` at `j = 1728`, else `2`.
Governs the twist count `gcd(n(j), p−1)` over `𝔽 p`. -/
def nJ [DecidableEq R] (c : Curve R) : ℕ :=
  if c.j = 0 then 6 else if c.j = 1728 then 4 else 2

section Field

variable {F : Type*} [Field F] [DecidableEq F]

/-- The canonical Weierstrass realization `W(c)` of the abstract curve.

**j-only hub (twist deferred):** we realize `c` by Mathlib's canonical `WeierstrassCurve.ofJ c.j`,
which handles all cases (`j = 0`, `1728`, `char 2, 3`) and is elliptic with `j`-invariant `c.j`.
This ignores the twist `c.D`, so the hub currently identifies curves up to *geometric* (over the
algebraic closure) isomorphism only; faithful over-`𝔽 p` twist distinction awaits the twist theory
(Silverman X.5), which Mathlib does not provide. -/
noncomputable def toWeierstrass (c : Curve F) : WeierstrassCurve F :=
  WeierstrassCurve.ofJ c.j

/-- `W(c)` is elliptic — from Mathlib's `(ofJ _).IsElliptic`. -/
instance (c : Curve F) : (c.toWeierstrass).IsElliptic :=
  inferInstanceAs (WeierstrassCurve.ofJ c.j).IsElliptic

/-- `W(c)` realizes the chosen `j` — Mathlib's `ofJ_j`. -/
theorem toWeierstrass_j (c : Curve F) : (c.toWeierstrass).j = c.j :=
  WeierstrassCurve.ofJ_j c.j

/-- The curve's canonical group: the points of its Weierstrass realization, carrying Mathlib's
already-proven `AddCommGroup` (built as `ClassGroup (CoordinateRing W)` = `Pic⁰`). -/
abbrev group (c : Curve F) : Type _ := c.toWeierstrass.toAffine.Point

/-- **Uniqueness of the group law (intrinsic characterization).**
If the canonical bijection `e : Pt ≃ c.group` is additive for *some* `AddCommGroup Pt`, then the
addition is forced to be the transported one `e.symm (e a + e b)`. So the group law is determined by
the canonical map `e` alone — no model privileged, no arbitrary choice survives.

This is the honest, provable form of uniqueness: it pins the *operation*, not the bundled
`AddCommGroup` instance (whose `nsmul`/`zsmul` data can differ — the usual diamond). The genuine
content is that `e` is the canonical Abel–Jacobi map `ι` (forced by the identity `O`), which is
rigidity; supplying a non-canonical `e` would not give uniqueness. -/
theorem add_forced_of_equiv_additive {Pt : Type*} [AddCommGroup Pt] (c : Curve F) (e : Pt ≃ c.group)
    (hadd : ∀ a b : Pt, e (a + b) = e a + e b) (a b : Pt) :
    a + b = e.symm (e a + e b) := by
  apply e.injective
  rw [hadd, e.apply_symm_apply]

end Field

end Curve

end FEC
