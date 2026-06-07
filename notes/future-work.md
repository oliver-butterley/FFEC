# FFEC — future work and deferred workstreams

This document records the major workstreams that are **deliberately out of the current scope**
because they need mathematical infrastructure that does not yet exist in Mathlib (or in this
development), together with *what each unlocks* and *what it would take*. It is the long-term
roadmap for taking FFEC beyond the current deliverable.

## Current deliverable (for context)

FFEC currently provides, **fully proven and axiom-free**:

- The `MontgomeryCurve` and `TwistedEdwardsCurve` models over a general field (`[Field F]
  [DecidableEq F] [NeZero (2 : F)]`), each with an `AddCommGroup` on its points **transported from
  Mathlib's proven Weierstrass group law** via an explicit bijection `pointEquiv` (so associativity
  etc. are reused, never re-proved — in contrast to curve25519-dalek, whose Edwards `add_assoc` is
  `sorry`).
- The explicit twisted-Edwards addition formula, *proven* to agree with the transported group law
  (`addFormula_eq_add`), and the Edwards⇄Montgomery birational bridge.
- The `Examples` layer instantiating Ed25519 / Curve25519 over `𝔽 (2²⁵⁵−19)`, with **no axioms**
  (`p_prime` via the `PrimeCert` dependency, `d` non-square via a Legendre-symbol computation).

The deferred items below are the things this design **cannot** currently reach.

---

## 1. Point counting and the group order (the central gap)

**What is missing.** We have no handle on `#E(𝔽_p)`. There is no `#E = p + 1 − a_p`, no Hasse bound,
no Schoof-style counting. Equivalently, the *cardinality* of the point group is opaque to the
current `j`/discriminant-level development (as noted in the original design: "Tier 3 arithmetic —
`j` cannot see these").

**What this blocks.**
- `#E = 8ℓ` for Ed25519 (cofactor 8, `ℓ = 2²⁵² + 277…` prime) — provable only as a *cardinality*
  statement, which we cannot make.
- The **order of the base point** (`ℓ`). We can define base points (Ed25519's `B`, Curve25519's
  `u = 9`) as concrete on-curve points in `Examples` and *prove they are on the curve*, but their
  defining cryptographic property — order exactly `ℓ` — is unreachable.
- The **prime-order subgroup** / the statement that the cofactor subgroup has order 8 *as a
  structural theorem* (we can only exhibit specific small-order points; see §2).
- Ristretto as a genuine **prime-order quotient** (see §3).

**What would unlock it.** A point-counting / cardinality development: at minimum a certified value
of `#E` for the specific curves (e.g. an external certificate à la `PrimeCert`, or a verified
Schoof/baby-step–giant-step computation), or a general Hasse-interval + counting API in Mathlib.
This is research-grade and is the single most load-bearing piece of missing infrastructure.

---

## 2. Torsion structure

**What we can do now.** The canonical **2-torsion point** is provable *generally* and cheaply from
the explicit addition: Edwards `(0, −1)` and Montgomery `(0, 0)` satisfy `2 • T = 0`, `T ≠ 0`.

**The constraint that shapes everything here.** Our point group is **noncomputable** — it is
transported through Mathlib's `ClassGroup (CoordinateRing W)` construction, which uses `Classical`.
So, unlike curve25519-dalek (whose Edwards group is the *computable* explicit-formula group, letting
them settle the 8-torsion table by `native_decide`), **we cannot `decide`/`native_decide` `n • P =
0`.** We must prove torsion facts *symbolically*, rewriting `n • P` through the explicit
`addFormula`/`add_some`. This is fine for 2-torsion, gets heavy for the Ed25519 4-/8-torsion
(iterated addition on 255-bit coordinates), and does not scale to large `n`.

**Improved approaches (future).**
- A **torsion API**: `E[n]` as an `AddSubgroup`, division polynomials, the cofactor subgroup `E[8]`
  exhibited *structurally* (not just as enumerated points), and `E / E[8]`.
- A **computable parallel model** — the most promising concrete upgrade for order/torsion. The
  linchpin already exists: `addFormula` is the explicit coordinate addition (pure field arithmetic),
  and `addFormula_eq_add` *proves* it equals the (noncomputable) transported group `+`, with
  `addFormula_assoc`/`addFormula_comm` and the identity/inverse coordinate lemmas giving all the
  axioms. Two ways to cash this in:
  1. Make `addFormula` the group instance's actual `add` (and the explicit `neg`/`(0,1)` its `neg`/
     `zero`), proving the axioms by transporting through `pointEquiv` *inside the proofs* via the
     agreement. One instance, which then *computes wherever the field does*.
  2. Keep the current instance and add a *parallel* computable scalar-multiplication (iterate
     `addFormula`), prove `nsmulFormula n P = n • P` via the agreement, and `native_decide` torsion
     on the computable function, transferring the result to the group.

  **The genuine constraint** (this is *why* the group is noncomputable, not an accident): computation
  needs a **computable field**. `addFormula` divides, and an abstract `[Field F]` may have a
  noncomputable inverse (e.g. `ℝ`'s, via `Classical`). So a computable group exists only over a
  *computable* field like `ZMod p` — an **Examples-level** capability, not a property of the general
  `[Field F]` models, which stay noncomputable unavoidably. And since a type carries at most one
  `AddCommGroup` instance, you do not *add* a computable instance beside the general one — you either
  make the single instance's `add` the explicit formula (option 1) or use a parallel function
  (option 2). Either way this yields dalek-style `native_decide` torsion **with our proven
  associativity** (strictly better than dalek, who have decidable torsion but a `sorry`'d
  `add_assoc`). The hard part — the agreement — is done; what remains is small.

---

## 3. Ristretto (prime-order quotient of Ed25519)

Ristretto is the quotient `E(𝔽_p) ⧸ E[8]` (order `ℓ`), with canonical coset representatives chosen
via the even-point invariant and an inverse-square-root encoding.

**Provable core (Option A — feasible now, axiom-free).**
- `IsEven P := IsSquare (1 − y²)`, the doubling-image characterization.
- `2·E ⊆ {IsEven}` — provable (curve25519-dalek proves exactly this direction, ~100-line
  `linear_combination`; reusable). Uses `1 + d` a square + completeness.
- The even points form an `AddSubgroup` (closure via the doubling characterization + `abel`).

**What needs the missing infrastructure.**
- The reverse `{IsEven} ⊆ 2·E` — a **2-descent / 2-isogeny** argument (curve25519-dalek leaves it
  `sorry`).
- **Prime order** of the Ristretto group — needs `#E = 8ℓ` (§1). Note the even subgroup `2·E` itself
  has order `2ℓ` (index 4), *not* `ℓ`, so it is **not** the Ristretto group; the prime-order group
  genuinely requires the cofactor quotient, hence point counting.
- Canonical encode/decode (`compress`/`decompress`) round-trip. (dalek proves only that decompression
  *succeeds* on even points, not the full round-trip.)

So a faithful, prime-order Ristretto is gated on §1 and a 2-descent; the even-subgroup core is the
honest, provable substance to build first when Ristretto is taken up.

---

## 4. Base points

Base points (Ed25519's `B`, Curve25519's `u = 9`) are **instance-specific data**, not part of the
general models, so they belong in `Examples`. On-curve membership is provable (`decide`/`norm_num`);
their order-`ℓ` property is **not** (§1). Add them when the application needs them, with the order
left as a documented, unproven fact (or imported once §1 exists).

---

## 5. Faithful `(j, twist)` abstract-curve hub

The programme to re-center the development on a *faithful* abstract elliptic curve classified by
`(j-invariant, twist)` with full Galois detail — including the quadratic/quartic/sextic twists, the
`gcd(n(j), p−1)` form count, the `j ∈ {0, 1728}` and characteristic 2, 3 cases, and routing the
concrete models through the hub — is written up separately in **[`twist-theory.md`](twist-theory.md)**.
It likewise needs Mathlib infrastructure that does not yet exist (a twist API, the
"`F`-isomorphic ⟺ `VariableChange`" classification, `Aut(E)` computations).

---

## 6. What curve25519-dalek needs from Edwards/Montgomery that FFEC lacks

For the application as the consumer: results dalek's verification relies on at the *math-model*
layer (Edwards/Montgomery — not the implementation-representation layer, which is dalek's own) that
FFEC does not yet provide. First, the flip side worth stating — FFEC already gives dalek something
it *lacks*: a **proven `add_assoc`** (dalek's Edwards associativity is `sorry`).

Gaps, easiest first:

1. **Montgomery x-only ladder identities** (`uADD`, `uDBL`) — *easy, no infrastructure*. The X25519
   Montgomery ladder is verified against the differential relations
   `u(P+Q)·u(P−Q)·(u_P−u_Q)² = (u_P·u_Q − 1)²` and `4·u(2P)·u_P·(u_P²+A·u_P+1) = (u_P²−1)²`.
   FFEC has the full-coordinate `add_some`/`double` but not these `u`-only relations; they are
   derivable from `add_some`/`double` + the curve equation by `field_simp; ring` (dalek's proofs are
   ~60–75 lines, no certificates).

2. **Curve-specific quadratic-character facts** — *easy*. dalek proves `A²−4` and `A−2` non-square,
   `A+2` square for Curve25519 (used in the Edwards↔Montgomery birational map and Ristretto). FFEC
   proves the *general* analogues (`TwistedEdwardsCurve.no_root` = no rational 2-torsion beyond
   `(0,0)`; completeness `¬IsSquare d`), so these mostly specialise out, but the named facts aren't
   all exposed. Adding them is a `legendreSym` + `norm_num` exercise (like `edwardsD_not_square`).

3. **Base points** — *partly easy, partly §1/§4*. The Ed25519 base point `B` and Curve25519 `u = 9`:
   on-curve is trivial to add in `Examples`; their order `ℓ` needs point counting (§1).

4. **Cofactor / small-order torsion** — *needs §2*. The Ed25519 8-torsion (explicit generator,
   `8•G = 0`, `4•G ≠ 0`, the torsion table) used for cofactor clearing and small-subgroup checks.
   dalek does this by `native_decide` on its *computable* group; FFEC needs the **computable-group
   upgrade** (§2) to match, or symbolic torsion proofs.

5. **Scalar multiplication / the ladder as an algorithm** — *needs §2*. `n • P` exists abstractly
   (from the `AddCommGroup`) but is noncomputable; a computable/ladder form for X25519 needs §2.

6. **Ristretto** (prime-order quotient + encode/decode) — *needs §1 + §3*.

Not a math gap but the connection point: dalek's ~11 coordinate/byte representations
(extended/projective/completed/Niels, compressed) attach to the math model via `toPoint`; FFEC
supplies the affine `Point` and the explicit group law they map onto (and `add_mk` matches dalek's
`add_coords` exactly). The representations themselves are the application's, not FFEC's scope.

**Quick wins (no research-gated infrastructure):** items 1 and 2 — the `uADD`/`uDBL` differential
identities and the Curve25519 Legendre facts — could be added immediately and would directly serve
the X25519 and birational-map verification.

---

## Summary: the dependency at the root

Almost everything deferred here funnels through **§1 (point counting / `#E`)**: base-point order,
prime-order subgroups, the cofactor as a structural theorem, and prime-order Ristretto all reduce to
knowing `#E`. The one upgrade that is *independently* valuable and unblocks torsion ergonomics is the
**computable parallel model** of §2. Twists (§5) are a separate axis with their own missing API.
