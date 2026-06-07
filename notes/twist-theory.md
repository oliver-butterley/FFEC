# Twist theory and a faithful abstract elliptic-curve hub

> **Status: deferred / future workstream.** This document is a design and future-notes plan,
> not a description of code that exists. The current development *dropped* its earlier abstract
> `Curve` hub (`FFEC/Curve.lean`), because that hub was keyed on the `j`-invariant **alone**, was
> unused (the concrete models each carry their own `toWeierstrass` and never route through it),
> and — most importantly — is **mathematically unfaithful** over a non-algebraically-closed
> field: it cannot tell a curve apart from its twists. This document is the plan to redo the hub
> *properly*, classifying curves up to `F`-isomorphism by the pair **(j-invariant, twist)** with
> full Galois/twist detail, and to prove that the concrete coordinate models (Montgomery, twisted
> Edwards, Ristretto) route through it. It is intended to be picked up and executed on a later
> occasion; nothing here should be built as part of the current upstream-quality pass.

This is the `S = Spec F` fiber, in a Weierstrass trivialization, of the Grothendieck picture an
elliptic curve is a smooth proper genus-1 group scheme `(E → S, e)`; the group law is unique by
rigidity; `E ≅ Pic⁰_{E/S}`; a "model" is a relative very-ample embedding; and the set of forms (the
twist) is `H¹(S_ét, Aut E)`. We deliberately stay in the field-level shadow of that picture because
Mathlib has no relative Picard / group-scheme / moduli infrastructure. The faithful hub described
below is the honest field-level realization of "an elliptic curve = its iso class".

---

## 1. Motivation and goal

### 1.1 Why `j` alone is not a faithful invariant over `F`

Over an algebraically closed (or merely separably closed) field `F̄`, the `j`-invariant is a
*complete* invariant: two elliptic curves over `F̄` are `F̄`-isomorphic **iff** they have the same
`j`. This is exactly Mathlib's

```
WeierstrassCurve.exists_variableChange_of_j_eq
  {F} [Field F] [IsSepClosed F] (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
  (heq : E.j = E'.j) : ∃ C : WeierstrassCurve.VariableChange F, C • E = E'
```

(`Mathlib/AlgebraicGeometry/EllipticCurve/IsomOfJ.lean`). The crucial hypothesis is
`[IsSepClosed F]`: the change of variables it produces uses roots/`n`-th roots that exist *only*
over the separable closure.

Over a general field `F` (in particular over a finite field `𝔽_p`), `j` is **not** complete. Two
curves can have equal `j` yet be non-isomorphic over `F`, becoming isomorphic only after base change
to `F̄`. The standard example: `y² = x³ − x` and `y² = x³ − 4x` over `ℚ` both have `j = 1728` but
are not `ℚ`-isomorphic — they are *quadratic twists* of one another, related by `x ↦ 2x, y ↦ 2√2 y`,
an isomorphism defined only over `ℚ(√2)`.

So the old hub `structure Curve (R) where j : R; D : Rˣ`, whose `toWeierstrass` was literally
`WeierstrassCurve.ofJ c.j` (ignoring `D` entirely; see the deleted `FFEC/Curve.lean`), classifies
curves only up to *geometric* (over `F̄`) isomorphism. Its `D` field was decorative. That is the
defect this workstream fixes.

### 1.2 The target

A type, schematically

```
structure EllipticCurveUpToIso (F : Type*) [Field F] where
  j     : F
  twist : Twist F j        -- a type that DEPENDS on j (and on char F); see §3.1
```

together with a canonical realization `toWeierstrass : EllipticCurveUpToIso F → WeierstrassCurve F`
and a **faithfulness theorem**

```
toWeierstrass c ≅_F toWeierstrass c'   ↔   c.j = c'.j ∧ c.twist = c'.twist
```

where `≅_F` is `F`-isomorphism (related by a `VariableChange F`). This makes
`EllipticCurveUpToIso F` a *faithful* set of representatives for elliptic curves over `F` modulo
`F`-isomorphism, indexed exactly by `(j, twist)`. The concrete models then attach by

```
MontgomeryCurve.toWeierstrass M  ≅_F  (hub ⟨M.j, twistOf M⟩).toWeierstrass
```

so that the models genuinely *are* instances of the hub — the property the old hub claimed in its
docstring but never delivered.

### 1.3 The intrinsic group story (rigidity / `Pic⁰`)

Independently of the twist classification, the hub should carry the *group law* intrinsically:
`E ≅ Pic⁰(E)` via the canonical Abel–Jacobi map `ι : P ↦ [(P) − (O)]`, with the group law forced by
`O` alone (rigidity). The old hub had a near-tautological "uniqueness" lemma
(`add_forced_of_equiv_additive`: *if* a bijection to the Weierstrass group is additive then the
addition is the transported one). The faithful programme should upgrade this to the genuine
statement that `ι` is the canonical iso forced by `O`, realized through Mathlib's
`ClassGroup (CoordinateRing W)` (which *is* `Pic⁰` on the `|3·O|` model and is what Mathlib's group
instance already uses). See §3.6.

---

## 2. The mathematics of twists

We work in **characteristic ≠ 2, 3** throughout this section unless stated otherwise; char 2, 3 is
genuinely different and deferred to §5. In char ≠ 2, 3 every elliptic curve has a short Weierstrass
model `y² = x³ + Ax + B`, and `j = 1728 · 4A³ / (4A³ + 27B²)`, `Δ = −16(4A³ + 27B²) ≠ 0`.

### 2.1 Geometric vs arithmetic isomorphism classes

Fix `E/F` elliptic. Let `Gal = Gal(F̄/F)`.

- **Geometric class.** Over `F̄`, the iso class of `E` is determined by `j(E)` (and conversely every
  `j ∈ F̄` is realized). So geometric classes ↔ values of `j`.
- **Arithmetic class.** Over `F`, a single geometric class (a fixed `j`) generally *splits* into
  several `F`-isomorphism classes. A curve `E'/F` with `E' ≅_{F̄} E` (i.e. same `j`) but not
  necessarily `E' ≅_F E` is called an **`F`-form** or a **twist** of `E`.
- **The classifying set.** The pointed set of `F`-forms of `E` is in natural bijection with the
  Galois cohomology set

  ```
  Twist(E/F)  ≅  H¹(Gal(F̄/F), Aut_{F̄}(E)),
  ```

  where `Aut_{F̄}(E)` is the group of `F̄`-automorphisms of `E` fixing `O`, with its natural
  `Gal`-action. (Silverman, *AEC*, X.2 — the general descent/forms machinery — and X.5 for elliptic
  curves specifically.) The base point of the set is `E` itself.

The whole subtlety of "twist" lives in `Aut_{F̄}(E)`, which depends on `j`.

### 2.2 `Aut(E)` and the twist degree `n(j)`

For `E/F̄` elliptic in char ≠ 2, 3, the automorphism group (fixing `O`, hence acting on the tangent
space at `O` by scaling) is **cyclic**, and its order `n(j) := #Aut_{F̄}(E)` is:

| `j`              | curve (short form)      | `Aut_{F̄}(E)`        | `n(j)` | extra automorphism |
|------------------|-------------------------|----------------------|--------|--------------------|
| `j ≠ 0, 1728`    | `y² = x³ + Ax + B`      | `{±1} = μ₂`          | `2`    | none beyond `−1`   |
| `j = 1728`       | `y² = x³ + Ax`  (`B=0`) | `μ₄`                 | `4`    | `i : (x,y) ↦ (−x, iy)` |
| `j = 0`          | `y² = x³ + B`   (`A=0`) | `μ₆`                 | `6`    | `ζ : (x,y) ↦ (ζ₃x, −y)` (order 6) |

**Where these come from.** An automorphism in char ≠ 2,3 of a short-Weierstrass curve is a variable
change of the restricted form `x ↦ u²x, y ↦ u³y` (the only changes preserving the short form and
fixing `O`), with `u ∈ F̄ˣ`. Such a change sends `y² = x³ + Ax + B` to
`y² = x³ + (A/u⁴)x + (B/u⁶)`. For it to be an *auto* (same curve) we need

```
A/u⁴ = A   and   B/u⁶ = B.
```

- **Generic** (`A ≠ 0`, `B ≠ 0`, i.e. `j ≠ 0, 1728`): forces `u⁴ = 1` and `u⁶ = 1`, hence
  `u² = gcd(u⁴,u⁶)-power = 1`, so `u = ±1`. `Aut = μ₂`, the only nontrivial element being `−1`
  (the inversion `(x,y) ↦ (x,−y)`).
- **`j = 1728`** (`B = 0`, `A ≠ 0`, curve `y² = x³ + Ax`): only `u⁴ = 1` is required, so
  `u ∈ μ₄`. `Aut = μ₄`. The order-4 generator `u = i` (a primitive 4th root of unity, present in
  `F̄`) gives `(x,y) ↦ (i²x, i³y) = (−x, −iy)`; up to sign this is "multiplication by `i`" using the
  CM by `ℤ[i]`.
- **`j = 0`** (`A = 0`, `B ≠ 0`, curve `y² = x³ + B`): only `u⁶ = 1` is required, so `u ∈ μ₆`.
  `Aut = μ₆`. The generator `u = ζ₆` (primitive 6th root) gives `(x,y) ↦ (ζ₆²x, ζ₆³y) = (ζ₃x, −y)`;
  this is the CM by `ℤ[ζ₃]` (the curve has CM by the Eisenstein integers).

So `n(j) = 6` at `j = 0`, `4` at `j = 1728`, `2` otherwise. The order is the order of the cyclic
group `{u : u⁴ = u⁶ = 1 within the relevant constraint}` and equals the *degree* of the twists.

### 2.3 Twists are cyclic ⇒ Kummer theory

Because `Aut_{F̄}(E) = μ_{n(j)}` is cyclic (and the `Gal`-action is the natural one on roots of
unity), the classifying set is a *group*:

```
H¹(Gal(F̄/F), μ_{n(j)})  ≅  Fˣ / (Fˣ)^{n(j)}      (Kummer theory).
```

This is the Kummer exact-sequence computation: from `1 → μ_n → F̄ˣ →^{(·)^n} F̄ˣ → 1` and
`H¹(Gal, F̄ˣ) = 1` (Hilbert 90), one gets `H¹(Gal, μ_n) ≅ Fˣ/(Fˣ)^n` **provided** `μ_n ⊂ F`
(which, for the relevant `n`, is exactly the residue condition that makes the extra automorphisms
*defined over `F`*; see §2.4). Hence:

```
twist datum  d ∈ Fˣ / (Fˣ)^{n(j)}.
```

The trivial class `d = 1` is `E` itself; nontrivial classes are the proper twists.

- `n = 2`: `Fˣ/(Fˣ)²` — **quadratic twists** (always available, no root-of-unity condition since
  `μ₂ = {±1} ⊂ F` for char ≠ 2).
- `n = 4`: `Fˣ/(Fˣ)⁴` — **quartic twists** (only relevant at `j = 1728`, and only when `μ₄ ⊂ F`).
- `n = 6`: `Fˣ/(Fˣ)⁶` — **sextic twists** (only relevant at `j = 0`, and only when `μ₆ ⊂ F`).

### 2.4 Counting over `𝔽_p`

Over `𝔽_p` (`p > 3`), `𝔽_pˣ` is **cyclic of order `p − 1`**. For a cyclic group `C` of order `m`,
the `n`-th-power subgroup has index `gcd(n, m)`, so

```
#(𝔽_pˣ / (𝔽_pˣ)^n) = gcd(n, p − 1).
```

Therefore the number of `𝔽_p`-forms with a given `j` is `gcd(n(j), p − 1)`:

- **Generic `j` (`n = 2`):** `gcd(2, p − 1) = 2` for all odd `p` — every curve has exactly its
  quadratic twist partner (2 classes total).
- **`j = 1728` (`n = 4`):** `gcd(4, p − 1) = 4` iff `4 ∣ p − 1`, i.e. **`p ≡ 1 (mod 4)`**
  (equivalently `i ∈ 𝔽_p`, equivalently `μ₄ ⊂ 𝔽_p`). If `p ≡ 3 (mod 4)` then `gcd(4, p−1) = 2`
  and the would-be quartic twists collapse to just the quadratic pair.
- **`j = 0` (`n = 6`):** `gcd(6, p − 1) = 6` iff `6 ∣ p − 1`, i.e. **`p ≡ 1 (mod 3)`** (note
  `p > 3` odd already gives `2 ∣ p − 1`; the binding condition is `3 ∣ p − 1`, i.e. `ζ₃ ∈ 𝔽_p`,
  i.e. `μ₆ ⊂ 𝔽_p`). If `p ≡ 2 (mod 3)` then `gcd(6, p−1) = 2`.

The residue conditions are exactly the conditions that `μ_{n(j)} ⊂ 𝔽_p`, which is what makes the
Kummer identification valid and the extra twists genuinely defined over `𝔽_p`. (When the root of
unity is missing, the extra automorphisms are not `𝔽_p`-rational, the cohomology shrinks, and only
the quadratic twist survives.)

### 2.5 Explicit twist formulas

Concretely, for `d ∈ Fˣ`:

- **Quadratic twist (any `j`, `n = 2`).** For a general Weierstrass curve in `b`-form
  `y² = x³ + a₂x² + a₄x + a₆` (char ≠ 2), the twist by `d` is

  ```
  E^{(d)} :  y² = x³ + a₂ d x² + a₄ d² x + a₆ d³.
  ```

  *Verification that `j` is unchanged:* this is obtained from `E` by the (non-`F`) variable change
  `x ↦ x/d, y ↦ y/(d√d)` followed by clearing `d³`; equivalently, scaling `(A,B) ↦ (Ad², Bd³)` in
  short form `y² = x³ + Ax + B`. Then
  `j(E^{(d)}) = 1728·4(Ad²)³ / (4(Ad²)³ + 27(Bd³)²) = 1728·4A³d⁶/((4A³+27B²)d⁶) = j(E)`. The factor
  `d⁶` cancels — that is *why* `j` is twist-invariant. The two curves are `F(√d)`-isomorphic but not
  `F`-isomorphic unless `d ∈ (Fˣ)²`.

- **Quartic twist (`j = 1728`, `y² = x³ + Ax`, `n = 4`).** The twist by `d` is

  ```
  E^{(d)} :  y² = x³ + A d x,    d taken mod (Fˣ)⁴.
  ```

  Two such are `F`-isomorphic iff `d/d' ∈ (Fˣ)⁴` (the iso `x ↦ u²x, y ↦ u³y` needs `u⁴ = d/d'`).

- **Sextic twist (`j = 0`, `y² = x³ + B`, `n = 6`).** The twist by `d` is

  ```
  E^{(d)} :  y² = x³ + B d,    d taken mod (Fˣ)⁶.
  ```

  Two such are `F`-isomorphic iff `d/d' ∈ (Fˣ)⁶` (`u⁶ = d/d'`).

**Why these degrees.** The twist datum is a `u` with `u^{n(j)}` controlling the change, matching the
`u⁴`/`u⁶` constraints from §2.2. At `j = 1728` the relevant scaling acts on `A` through `u⁴`, so the
twist parameter lives mod `(Fˣ)⁴`; at `j = 0` it acts on `B` through `u⁶`, so mod `(Fˣ)⁶`. The
generic case sees only `u²` (quadratic). In each case the *number* of distinct twists over `𝔽_p` is
`#(𝔽_pˣ/(𝔽_pˣ)^{n(j)}) = gcd(n(j), p−1)` (§2.4).

---

## 3. The Lean design

This section is concrete about Mathlib's actual API. The relevant Mathlib types/lemmas live under
`Mathlib/AlgebraicGeometry/EllipticCurve/`:

- `WeierstrassCurve R` (a `structure` with `a₁ a₂ a₃ a₄ a₆ : R`); `WeierstrassCurve.Δ`, `.c₄`, `.j`.
- `WeierstrassCurve.IsElliptic` (`Δ` is a unit) and `EllipticCurve` packaging.
- `WeierstrassCurve.VariableChange R` (a `structure` with `u : Rˣ`, `r s t : R`) acting by `•`;
  `WeierstrassCurve.variableChange`, `variableChange_Δ`, `variableChange_j`.
- `WeierstrassCurve.Affine.Point` and its `AddCommGroup` over a field, built from
  `ClassGroup (W.CoordinateRing)`.
- `WeierstrassCurve.ofJ`, `ofJ0`, `ofJ1728`, `ofJNe0Or1728`, with `ofJ_j`, `ofJ0_j`, etc.
  (`ModelsWithJ.lean`).
- `WeierstrassCurve.exists_variableChange_of_j_eq` (`IsomOfJ.lean`) — **requires `[IsSepClosed F]`**.

### 3.1 The central difficulty: the twist type depends on `n(j)`

`Twist F j` must be `Fˣ / (Fˣ)^{n(j)}` where `n(j) ∈ {2, 4, 6}` is determined by `j` (and char).
The dependency on the *value* of `j` is the design crux. Options:

1. **Dependent quotient (`QuotientGroup`).** Define `n : F → ℕ` (the `if j = 0 then 6 else if j =
   1728 then 4 else 2` of the old `nJ`), then

   ```
   Twist F (j : F) := Fˣ ⧸ (powMonoidHom (n j)).range      -- or the subgroup of n(j)-th powers
   ```

   Clean conceptually; but `EllipticCurveUpToIso F` becomes a `Σ`/dependent pair `(j : F) ×
   Twist F j`, and every lemma carries the `n j` in its type. `DecidableEq` on `j` is needed to
   compute `n j` (the old hub used `[DecidableEq R]` for exactly this). *Recommended default.*

2. **Flat carrier + setoid.** Store `twist : Fˣ` and impose the equivalence
   `d ∼ d' ⟺ d/d' ∈ (Fˣ)^{n(j)}` as a `Setoid` whose relation reads `n j` off the stored `j`.
   Avoids a dependent type in the field but pushes the dependency into the `Setoid` instance, which
   is awkward (the relation depends on a *sibling* field). Generally worse than option 1.

3. **Σ-type / explicit case split on `j ∈ {0, 1728}` and char.** Make the special cases first-class:

   ```
   inductive EllipticCurveUpToIso (F)
     | generic (j : F) (hj : j ≠ 0 ∧ j ≠ 1728) (d : Fˣ ⧸ squares)
     | j1728  (d : Fˣ ⧸ fourthPowers)            -- only if μ₄ ⊂ F, else falls back to generic-style
     | j0     (d : Fˣ ⧸ sixthPowers)             -- only if μ₆ ⊂ F
   ```

   This makes each twist type *constant* (no dependency), at the cost of duplicated structure and
   needing the root-of-unity side conditions baked into the constructors. Most explicit, most
   verbose. Useful if the dependent-quotient proofs become unwieldy.

**Recommendation:** start with **option 1** (dependent quotient via `QuotientGroup` of the
`n(j)`-th power subgroup of `Fˣ`), with `[DecidableEq F]` to evaluate `n j`. Keep the special-`j`
constructors of option 3 as a fallback if the dependent types obstruct the faithfulness proof.

Note Mathlib has `Fˣ` as `Units F` (a `CommGroup`), and `QuotientGroup` with `MonoidHom.range
(powMonoidHom n)` gives the `n`-th-power subgroup quotient directly. The cardinality
`#(Fˣ/(Fˣ)^n) = gcd(n, #Fˣ)` for finite cyclic `Fˣ` is the only group-theory fact needed for the
count (§3.4) and is essentially `ZMod`/`gcd` arithmetic on a cyclic group.

### 3.2 `toWeierstrass`

```
noncomputable def toWeierstrass (c : EllipticCurveUpToIso F) : WeierstrassCurve F
```

realizing **both** `j` and the twist. Strategy: case on `n(c.j)`.

- **Generic `j`:** take a canonical representative of `j` (e.g. `WeierstrassCurve.ofJ c.j` — already
  `IsElliptic` with the right `j`, see `ofJ_j`), put it in short `b`-form, and apply the quadratic
  twist formula (§2.5) with a chosen lift `d ∈ Fˣ` of `c.twist`.
- **`j = 1728`:** start from `y² = x³ + Ax` (Mathlib's `ofJ1728`) and apply the quartic-twist
  formula `A ↦ A·d`.
- **`j = 0`:** start from `y² = x³ + B` (Mathlib's `ofJ0`) and apply the sextic-twist formula
  `B ↦ B·d`.

`toWeierstrass` must be proven **well-defined on the quotient**: changing the lift `d ↦ d·u^{n(j)}`
must yield an `F`-isomorphic Weierstrass curve (the `u`-scaling variable change). This is the
forward (easy) half of faithfulness and is where the explicit twist formulas earn their keep.

### 3.3 The faithfulness theorem

```
theorem toWeierstrass_iso_iff (c c' : EllipticCurveUpToIso F) :
    Nonempty (toWeierstrass c ≅_F toWeierstrass c')  ↔  c.j = c'.j ∧ c.twist = c'.twist
```

where `≅_F` means `∃ C : VariableChange F, C • toWeierstrass c = toWeierstrass c'`. It needs three
sub-facts:

1. **`F`-iso ⟹ same `j`.** `VariableChange` preserves `j`: this is Mathlib's `variableChange_j`
   (in `VariableChange.lean`). Immediate.
2. **`F`-iso ⟹ same twist.** Given `C • E^{(d)} = E^{(d')}` with both short-form twists of the same
   `j`-curve, deduce `d/d' ∈ (Fˣ)^{n(j)}`. This is the **hard, genuinely new** direction: it is the
   statement that distinct twist classes give non-`F`-isomorphic curves. Proof goes through the
   structure of `VariableChange` (`u, r, s, t`) specialized to short form: `s = t = r = 0` forced
   (to preserve short form / fix `O` up to the `μ` action), leaving `u^{n(j)} = d/d'`, i.e.
   `d/d' ∈ (Fˣ)^{n(j)}`.
3. **same `(j, twist)` ⟹ `F`-iso.** The explicit `u`-scaling realizes the iso (the well-definedness
   of §3.2, run in reverse). Together with (1)+(2) this gives the biconditional.

A useful intermediate is a **classification lemma over `F` (not `F̄`)**:

```
"two short-Weierstrass elliptic curves over F are F-isomorphic
   ⟺ same j AND their (A,B) differ by (u²·, u³·) for some u ∈ Fˣ"
```

This is the `F`-analogue of `exists_variableChange_of_j_eq`, *without* `IsSepClosed`. Mathlib does
**not** have it (its theorem assumes separably closed). Establishing this short-form `F`-iso
criterion is the technical heart of the whole workstream (see §4).

### 3.4 The count theorem over `𝔽_p`

```
theorem card_forms (p : ℕ) [Fact p.Prime] (hp : 3 < p) (j : 𝔽 p) :
    Nat.card (Twist (𝔽 p) j) = Nat.gcd (n j) (p - 1)
```

This is the **easy** part: `(𝔽 p)ˣ` is cyclic of order `p − 1` (`ZMod.instField` +
`instIsCyclicUnits`-style facts in Mathlib), and the index of the `n`-th-power subgroup of a finite
cyclic group of order `m` is `gcd(n, m)`. No twist geometry is needed — pure finite-group
cardinality. Specializations:

- generic `j`: `gcd(2, p−1) = 2`;
- `j = 1728`: `gcd(4, p−1) = 4 ⟺ p ≡ 1 (mod 4)`;
- `j = 0`: `gcd(6, p−1) = 6 ⟺ p ≡ 1 (mod 3)`.

### 3.5 Routing models through the hub

For each concrete model, define a `twistOf` extracting the twist class from the model's parameters
(via its computed short-form `(A, B)` against the canonical representative), and prove

```
theorem MontgomeryCurve.routesThroughHub (M : MontgomeryCurve F) :
    Nonempty (M.toWeierstrass ≅_F (hub ⟨M.j, twistOf M⟩).toWeierstrass)
```

and likewise `TwistedEdwardsCurve` and (the prime-order quotient) `Ristretto`. This is what makes
"the models are instances of the hub" a *theorem* rather than a docstring. Combined with §3.3 it
also yields, for free, the cross-model statement "two models with the same `(j, twist)` are
`F`-isomorphic", refining the current same-group `crossAddEquiv` story (which only transports the
group, not the curve iso).

### 3.6 Intrinsic `ι` / `Pic⁰` and rigorous uniqueness

Mathlib builds the `AddCommGroup` on `W.Affine.Point` from `ClassGroup (W.CoordinateRing)` — that
is `Pic⁰` on the degree-3 model. The intrinsic layer should:

- Define `ι : W.Point → ClassGroup (W.CoordinateRing)`, `P ↦ [(P) − (O)]`, as the *canonical*
  Abel–Jacobi map (it is, up to Mathlib packaging, the very map used to define the group).
- Prove `ι` is an `AddEquiv` (or that it is the canonical iso forced by `O`), upgrading the old
  hub's `add_forced_of_equiv_additive` from "*if* additive *then* transported" to "the canonical map
  *is* additive, and is the unique iso fixing `O`". Rigidity = "any morphism of elliptic curves is a
  translation composed with a group hom; one fixing `O` is a group hom" gives the uniqueness.
- Expose the hub group as `ι`-defined, so **no model is named** in the group's definition; Weierstrass
  only anchors *existence*. This is the field-level shadow of `E ≅ Pic⁰_{E/S}` + rigidity.

This is `Medium–Hard`: it mostly repackages existing Mathlib (`ClassGroup`, `CoordinateRing`) rather
than building new mathematics, but stating `ι` cleanly and proving canonicity is real work.

---

## 4. Mathlib gaps — what does not exist today

Honest inventory of what must be built, hardest last:

1. **Twist constructions + `j`-invariance.** Mathlib has no `quadraticTwist`/`quarticTwist`/
   `sexticTwist` of a `WeierstrassCurve`, nor lemmas that they preserve `j`. *Build:* the explicit
   formulas of §2.5 as `def`s on `WeierstrassCurve F`, plus `twist_j : (E.quadraticTwist d).j = E.j`
   etc. (`ring`/`field_simp` after expanding `j`). **Difficulty: Easy–Medium.** Note a quadratic
   twist is **not** a `VariableChange F` — the connecting iso `x ↦ x/d, y ↦ y/(d√d)` lives over
   `F(√d)`, not `F`. So it cannot be phrased via Mathlib's `•` action of `VariableChange F`; it is a
   genuine new construction.

2. **Non-isomorphism of distinct twists over `F`.** The statement "`d/d' ∉ (Fˣ)^{n(j)} ⟹ E^{(d)}
   ≇_F E^{(d')}`". *Build:* analyze `VariableChange F` on short forms (§3.3.2). **Difficulty:
   Medium–Hard** (case analysis forcing `r=s=t=0`, then `u^{n(j)} = d/d'`).

3. **`F`-isomorphism ⟺ `VariableChange F`, over a *general* field.** Mathlib's
   `exists_variableChange_of_j_eq` is the **`IsSepClosed`** statement only (verified:
   `IsomOfJ.lean` has `variable {F} [Field F] [IsSepClosed F]`). There is *no* general-field
   "`F`-iso ⟺ related by a `VariableChange F`" classification, and in fact the clean statement is
   "same `j` **and** same twist", i.e. exactly the faithfulness theorem §3.3. The reusable Mathlib
   piece is the *definition* of `≅_F` as `∃ C, C • E = E'` and `variableChange_j`; everything tying
   it to `(j, twist)` over `F` must be built. **Difficulty: Hard — this is the core deliverable.**

4. **`Aut(E)` computation.** A theorem `Aut_{F̄}(E) ≅ μ_{n(j)}` with the order split `{2,4,6}`.
   Mathlib has root-of-unity (`rootsOfUnity`, `IsPrimitiveRoot`) machinery but no `Aut` of an
   elliptic curve as a group object. *Build* either as a genuine `MulEquiv` to `rootsOfUnity n F̄`,
   or — pragmatically — **bypass** it: one does not strictly need `Aut(E)` as a formal object if one
   works directly with the explicit twist formulas and the short-form `VariableChange` analysis
   (items 1–3). **Difficulty: Medium if done abstractly; avoidable.**

5. **`H¹` / Kummer packaging.** Mathlib's Galois-cohomology support is limited; a faithful
   `H¹(Gal, μ_n) ≅ Fˣ/(Fˣ)^n` would be heavy. **Strongly recommended bypass:** do *not* formalize
   `H¹` at all. Define `Twist F j := Fˣ ⧸ (Fˣ)^{n(j)}` *directly* (Kummer's answer), and prove the
   faithfulness theorem by the explicit twist formulas + non-iso arguments (items 1–3). The `H¹`
   framing is then documentation/motivation, not a proof dependency. **Difficulty: Hard if done
   honestly; recommend avoiding.**

**Hardest:** item 3 (general-field iso classification / faithfulness) and item 2 (non-iso of
twists), which together are the substance. Items 1 and the count (§3.4) are comparatively routine.

---

## 5. Special cases and characteristics 2, 3

### 5.1 Extra automorphisms at `j ∈ {0, 1728}` (char ≠ 2, 3)

These are handled within the main programme via the `n(j) ∈ {4, 6}` cases (§2.2), gated by the
root-of-unity conditions `μ₄ ⊂ F` / `μ₆ ⊂ F`. The subtlety is that **over a field missing the root
of unity** the higher twists collapse to the quadratic ones (the count drops to `gcd(n, p−1) = 2`),
so the `toWeierstrass` and faithfulness proofs must respect that the quotient `Fˣ/(Fˣ)^n` already
encodes this collapse correctly (when `n ∤ ` enough of `p−1`, the quotient is automatically smaller).
Recommend implementing **generic `j` first**, then `j = 1728`, then `j = 0`.

### 5.2 Characteristic 2 and 3 are genuinely different

In char 2 and char 3 the short Weierstrass form `y² = x³ + Ax + B` is unavailable, `j = 1728 = 0`
phenomena merge, **supersingular** curves appear, and the automorphism group is much larger:

- char 3, `j = 0` (supersingular): `#Aut` up to **12**.
- char 2, `j = 0` (supersingular): `#Aut` up to **24** (the curve has `Aut` a non-abelian group of
  order 24, related to `SL₂(𝔽₃)`).

The whole cyclic-`μ_n`/Kummer story breaks (`Aut` need not be cyclic or abelian), so
`Twist = Fˣ/(Fˣ)^n` is simply wrong there. Mathlib's `ofJ` *already* special-cases char 2, 3 and
`j ∈ {0,1728}` (see `ModelsWithJ.lean`: `ofJ` branches on `(2:F)=0`, `(3:F)=0`, `j=0`, `j=1728`),
and `IsomOfJ.lean`'s separably-closed proof itself splits into `CharP F 2`, `CharP F 3`, and generic
sub-lemmas — concrete evidence of how much the characteristic matters.

**Recommendation:** scope the first faithful implementation to **char ≠ 2, 3** (the
`[Fact (ringChar F ≠ 2)] [Fact (ringChar F ≠ 3)]` regime, which already covers Curve25519/Ed25519's
`𝔽_{2²⁵⁵−19}`), and **defer char 2, 3** to a clearly separate later effort (different `Aut`,
different twist theory, no Kummer shortcut).

---

## 6. Suggested implementation phases and effort estimate

Ordered, with rough difficulty. The whole thing is research-grade and multi-week; the count is easy,
the faithful classification is the heavy part.

| Phase | Content | Difficulty / effort |
|-------|---------|---------------------|
| **T0** | `n : F → ℕ` (the `{2,4,6}` table) and `Twist F j := Fˣ ⧸ (Fˣ)^{n j}` as a `QuotientGroup`; `EllipticCurveUpToIso F` as the dependent pair. Decide option 1 vs 3 (§3.1). | Easy — a day or two of design. |
| **T1** | Quadratic twist `def` + `j`-invariance (§2.5); quartic/sextic twist defs + `j`-invariance. (§4 item 1.) | Easy–Medium. `ring`/`field_simp`. |
| **T2** | **Count theorem** over `𝔽_p`: `gcd(n j, p−1)` (§3.4). Cyclic-group cardinality only. | Easy. The first concrete payoff. |
| **T3** | Short-form `VariableChange F` analysis: forcing `r=s=t=0`, reducing to `u^{n} = A'/A` (or `B'/B`). Foundation for faithfulness. | Medium. |
| **T4** | **Faithfulness for generic `j`** (`n = 2`, quadratic twists): the full `≅_F ↔ (j, twist)` (§3.3) for `j ≠ 0, 1728`, including the non-iso direction (§4 item 2). | Hard — the core. |
| **T5** | **Special `j`** (`j = 1728`, then `j = 0`): quartic/sextic faithfulness with the root-of-unity gating (§5.1). | Hard. |
| **T6** | `toWeierstrass` well-definedness on the quotient + the iso direction; assemble the full faithfulness theorem. | Medium–Hard (reuses T3–T5). |
| **T7** | **Route one model** (Montgomery) through the hub (§3.5): `twistOf`, `routesThroughHub`. Then Edwards, Ristretto. | Medium per model. |
| **T8** | Intrinsic `ι`/`Pic⁰` + rigorous uniqueness (§3.6), replacing `add_forced_of_equiv_additive`. | Medium–Hard (repackaging Mathlib `ClassGroup`). |
| **T9** | (Deferred, separate effort) char 2, 3: new `Aut`, no Kummer; bespoke twist theory (§5.2). | Research-grade; out of the first version. |

A realistic first milestone is **T0–T4 + T7(Montgomery)**: a faithful hub for generic `j` with one
model routed through it and the count theorem — already strictly better than the dropped `j`-only
hub. T5/T6 complete the special `j`; T8 is the rigidity upgrade; T9 is a future expansion.

---

## 7. References

**Silverman, *The Arithmetic of Elliptic Curves* (2nd ed., GTM 106):**

- **III.10 — Twists.** The explicit quadratic/quartic/sextic twist constructions, the role of
  `Aut(E)`, and the `j ∈ {0, 1728}` exceptional automorphisms (char ≠ 2, 3).
- **X.2 — Galois cohomology and twists (general descent).** The general "forms of an object ↔
  `H¹(Gal, Aut)`" machinery.
- **X.5 — Twists of elliptic curves.** `Twist(E/F) ≅ H¹(Gal(F̄/F), Aut_{F̄} E)`; the
  cyclic-`Aut`/Kummer identification; the per-`j` form count. In particular **Prop. X.5.4** and its
  **Cor. X.5.4.1** (the `(j, d)` description of twists and the `gcd(n(j), q−1)` count over finite
  fields). See also III.10 Prop. 10.1–10.5.
- Appendix A (char 2, 3 automorphism groups of orders 12 / 24; supersingular phenomena).

**Mathlib (`Mathlib/AlgebraicGeometry/EllipticCurve/`):**

- `Weierstrass.lean` — `WeierstrassCurve`, `Δ`, `c₄`, `j`, `IsElliptic`, `EllipticCurve`.
- `VariableChange.lean` — `VariableChange R` (`u, r, s, t`), the `•` action, `variableChange_Δ`,
  `variableChange_j`, `map_variableChange`. The definition of `F`-isomorphism (`∃ C, C • E = E'`).
- `ModelsWithJ.lean` — `ofJ`, `ofJ0`, `ofJ1728`, `ofJNe0Or1728` and `ofJ_j`/`ofJ0_j`/`ofJ1728_j`;
  the char 2, 3 and `j ∈ {0,1728}` branching that this workstream must respect.
- `IsomOfJ.lean` — `exists_variableChange_of_j_eq` (**`[IsSepClosed F]`** — the geometric statement;
  the general-field refinement to `(j, twist)` is the gap this document fills).
- `NormalForms.lean` — short / char-≠-2 / char-2 / char-3 normal forms used by the above.
- `Affine/`, `Projective/`, `Jacobian/` — `Point`, the `AddCommGroup`, `ClassGroup
  (CoordinateRing W)` (`Pic⁰`) underlying §3.6.

**This repo:**

- `FFEC/Curve.lean` *(dropped)* — the unfaithful `j`-only hub this document replaces; its
  `add_forced_of_equiv_additive` is the weak uniqueness lemma to be upgraded in T8.
- `FFEC/Framework.lean` — `GroupTransfer` / `crossAddEquiv` (retained; the same-group transport this
  workstream's `routesThroughHub` refines to a curve-level iso).
- `MODELS.md` — the Montgomery / twisted Edwards / Ristretto model inventory routed in T7.
