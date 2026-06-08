import FFEC.Field
import FFEC.Framework
import FFEC.Montgomery.Defs
import FFEC.Montgomery.ToWeierstrass
import FFEC.Montgomery.Equiv
import FFEC.Montgomery.Group
import FFEC.Edwards.Defs
import FFEC.Edwards.AddFormulaBase
import FFEC.Edwards.AddFormulaCerts
import FFEC.Edwards.AddFormula
import FFEC.Examples.Curve25519

/-!
# FFEC — Finite Field Elliptic Curves

A multi-coordinate-model formalization of elliptic curves over a field, with **one `AddCommGroup`
per model reusing Mathlib's proven Weierstrass group law** — transported along an explicit point
bijection — instead of re-proving the group axioms per model. Everything is axiom-free and
`sorry`-free; the concrete Ed25519 / Curve25519 instantiations live in `Examples`.

This root module only re-exports the development. The layers, in dependency order (each file imports
the previous in its chain):

* `FFEC.Field` — the base field `𝔽 p = ZMod p`; imported (transitively) by everything.
* `FFEC.Framework` — the **transfer theorem** (`GroupTransfer`): a bijection from a model's point
  set to a group transports the whole `AddCommGroup` for free; two models sharing a reference group
  are canonically `≃+` (`crossAddEquiv`). Consumed by `Montgomery.Group` and `Edwards.Defs`.
* `FFEC.Montgomery.*` — the Montgomery model `B y² = x³ + A x² + x`:
  `Defs` (structure with `IsUnit` nondegeneracy, `Point`, base change `map`) → `ToWeierstrass`
  (the change of variables `(x,y) ↦ (Bx, B²y)`, `Δ`, `IsElliptic`, `j`) → `Equiv` (the point
  bijection `pointEquiv` to Weierstrass — the per-model datum) → `Group` (the transported
  `AddCommGroup`, `pointAddEquiv`, the explicit law `add_some`/`double`/`neg_some`, and the X25519
  ladder identities `uADD`/`uDBL`).
* `FFEC.Edwards.*` — the twisted Edwards model `a x² + y² = 1 + d x² y²`, which **composes through
  Montgomery**: `Defs` (the complete curve, the birational `toMontgomery`, `pointEquivMont`, the
  transported group, `j`) → `AddFormulaBase` → `AddFormulaCerts` → `AddFormula`. The last three are
  one proof in three files: that the *explicit* rational addition `addFormula` agrees with the
  transported group `+` (`addFormula_eq_add`, hence `addFormula_assoc` for free — the theorem
  curve25519-dalek leaves `sorry`), plus the coordinate API and the computable model `nsmulFormula`.
* `FFEC.Examples.Curve25519` — Ed25519 and Curve25519 over `𝔽 (2²⁵⁵ − 19)`, instantiating the
  general models; both number-theoretic side conditions (`p` prime via the `PrimeCert` dependency,
  `d` a non-square via a Legendre symbol) are proven, so the examples too are axiom-free.

Deferred workstreams (point counting / `#E`, torsion, Ristretto, the faithful `(j, twist)` hub) are
written up in `notes/future-work.md` and `notes/twist-theory.md`.
-/
