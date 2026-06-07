# Point models for Edwards / Montgomery / Ristretto — the real situation

Reference distilled from the `curve25519-dalek` Rust crate and its Lean verification
(`/home/oliver/Projects/curve25519-dalek-lean-verify/`, all definitions in `Curve25519Dalek/Types.lean`
and `Curve25519Dalek/Math/{Edwards,Montgomery,Ristretto}/Representation.lean`).

## The big picture

- **Three groups**, all over the **same field** `𝔽 = GF(2²⁵⁵ − 19)`:
  - **Ed25519** — twisted Edwards `a x² + y² = 1 + d x² y²`, `a = −1`, `d = −121665/121666`.
  - **Curve25519** — Montgomery `v² = u³ + A u² + u`, `A = 486662`.
  - **Ristretto** — the prime-order quotient of Ed25519 by its cofactor-8 subgroup.
- The **many "models" are NOT different curves** — they are different *coordinate representations*
  of the same group, chosen for: avoiding field inversions, specific algorithms (ladder, mixed
  addition, precomputed tables), or serialization/canonical encoding.
- This is exactly the "**a model = a choice of coordinates/embedding**" picture, and it is strong
  evidence for the transfer design: one group law, proved once; every representation related by a
  conversion bijection that *transports* it. dalek has ~7 representations for Edwards **alone**, all
  sharing one group law — nobody re-proves associativity per representation.

The representations fall into three kinds:
- **(a) coordinate systems for speed** — projective / extended / completed / Niels; bijective on
  points (modulo `Z ≠ 0`); the group law is rational and these just cache subexpressions / avoid
  inversions.
- **(b) serialization forms** — compressed-Y, Montgomery bytes, compressed Ristretto; encode/decode.
- **(c) a genuine quotient** — Ristretto (coset representatives + canonical encoding); a *different*
  (prime-order) group, needing an "even point" invariant.

---

## Edwards (Ed25519):  `−x² + y² = 1 + d x² y²`

| Model | Coords | Affine recovery | Invariant / role |
|---|---|---|---|
| **AffinePoint** | `(x, y)` | — | the math model; curve eq directly |
| **ProjectivePoint** | `(X:Y:Z)` | `(X/Z, Y/Z)` | `aX²Z² + Y²Z² = Z⁴ + dX²Y²`; avoids inversions |
| **EdwardsPoint** (extended) | `(X:Y:Z:T)` | `(X/Z, Y/Z)` | **`XY = ZT`** (T caches `XY/Z`); the workhorse |
| **CompletedPoint** | `(X:Y:Z:T)` | **`(X/Z, Y/T)`** | `aX²T² + Y²Z² = Z²T² + dX²Y²`; the add/double *output* |
| **ProjectiveNielsPoint** | `(Y+X, Y−X, Z, T2d)` | `((YpX−YmX)/2Z, (YpX+YmX)/2Z)` | `T2d = 2dT`; fast mixed re-addition |
| **AffineNielsPoint** | `(y+x, y−x, 2dxy)` | `((·−·)/2, (·+·)/2)` | precomputed table for fixed-base mul |
| **CompressedEdwardsY** | 32 bytes | decompress (below) | serialization: `y ‖ sign(x)` |

- **Compression:** `y.val + (if is_negative x then 1 else 0)·2²⁵⁵`.
- **Decompression:** read `y`; `x² = (y²−1)/(d y²+1)`; check square; sqrt; apply sign bit.
- **Group law shape:** add/double consume Projective/Extended and produce a **CompletedPoint**, then
  convert back — i.e. the law is a *rational* map factored through the completed model. (No model
  stores a polynomial addition; addition is rational, exactly as in our `scratch.lean`.)

---

## Montgomery (Curve25519):  `v² = u³ + 486662 u² + u`

| Model | Coords | Role |
|---|---|---|
| **MontgomeryPoint** | 32 bytes, **u only** (`v` dropped) | X25519 Diffie–Hellman |
| **Montgomery ProjectivePoint** | `(U:W)`, `u = U/W` | the **XZ Montgomery ladder** (differential add+double) |

- **Birational to Edwards:** `u = (1+y)/(1−y)`,  `y = (u−1)/(u+1)`.
- The identity is the **point at infinity** (not affine); `(0,0)` is the 2-torsion point.
- Only the `u`-coordinate is tracked — the ladder does differential add/double without `v`.

---

## Ristretto (prime-order quotient of Ed25519, cofactor 8)

| Model | Coords | Role |
|---|---|---|
| **RistrettoPoint** | an `EdwardsPoint` `(X:Y:Z:T)` that is a coset representative | group law = Edwards law; equality = coset equality |
| **CompressedRistretto** | 32 bytes, canonical encoding | the Ristretto encode/decode (cofactor elimination) |

- **Even-point characterization:** a point is in the doubling image `2·E` iff `IsSquare(1 − y²)`
  (equivalently `IsSquare(Z² − Y²)` projectively). `RistrettoPoint.IsValid` carries this.
- **Encode (`compress`):** `u1 = (1+y)(1−y)`, `u2 = xy`, inverse-sqrt `I = 1/√(u1·u2²)`, a rotation
  by `±√(−1)` when `is_negative(xy·z⁻¹)`, output `s = |den_inv·(1 − y_final)|`.
- **Decode:** parse `s` (even, `< p`, canonical); `u1 = 1 − a s²`, `u2 = 1 + a s²`; invert the isogeny
  to recover `(x, y)`.
- Ristretto is the one case that is a **genuinely different group** (prime order), not just new
  coordinates — it needs the even-point invariant and a canonical encoding, not merely a conversion.

---

## Group operations per math model (`zero` / `neg` / `add`)

These are the operations on the **mathematical model** of each group (the abstract layer the
implementation representations are described against). All rational; identities/cases as noted.

### Edwards  `a x² + y² = 1 + d x² y²`  (Ed25519: `a = −1`)
- **zero** = `(0, 1)` — affine identity.
- **neg** `(x, y) = (−x, y)`.
- **add** `(x₁,y₁) + (x₂,y₂) = ( (x₁y₂ + y₁x₂)/(1 + d x₁x₂y₁y₂),  (y₁y₂ − a x₁x₂)/(1 − d x₁x₂y₁y₂) )`.
  Complete (single formula, no cases) when `a` is a square and `d` a non-square.

### Montgomery  `B y² = x³ + A x² + x`  (Curve25519: `A = 486662`, `B = 1`)
- **zero** = `∞` (point at infinity; not affine).
- **neg** `(x, y) = (x, −y)`.
- **add**, `P ≠ ±Q`, slope `λ = (y₂ − y₁)/(x₂ − x₁)`:
  `x₃ = B λ² − A − x₁ − x₂`,  `y₃ = λ (x₁ − x₃) − y₁`.
- **double** `P = Q`, slope `λ = (3x₁² + 2A x₁ + 1)/(2B y₁)`:
  `x₃ = B λ² − A − 2x₁`,  `y₃ = λ (x₁ − x₃) − y₁`.
- `P = −Q` (i.e. `x₁ = x₂`, `y₁ = −y₂`) ⇒ `zero = ∞`.

### Ristretto  (prime-order quotient of Edwards, cofactor 8)
The operations are **inherited from Edwards** — Ristretto reuses the Edwards group law on coset
representatives; only the *equality* (mod the cofactor subgroup) and the *canonical encoding* are new.
- **zero** = class of the Edwards identity `(0, 1)`.
- **neg** = Edwards neg on a representative: `(x, y) ↦ (−x, y)`.
- **add** = Edwards add on representatives (well-defined on cosets).
- Equality = Ristretto equivalence (two representatives equal iff they differ by the cofactor
  subgroup); canonical form via encode/decode with the even-point invariant `IsSquare(1 − y²)`.

## Takeaway for the FFEC project

- **Project target = general infrastructure, not just this application.** We build *general* finite-field
  elliptic-curve infrastructure (any prime field `𝔽 p`, arbitrary parameters) that the Ed25519 /
  Curve25519 / Ristretto math models *instantiate*. Targeting only Curve25519 would be too limited;
  the application is one instantiation that the general framework must serve. (Our models being
  stated over `[CommRing R]` / `𝔽 p`, not hard-wired to `2²⁵⁵−19`, already follows this.)
- **Concrete near-term target = three math models + explicit interconversions.** One math model per
  group (Edwards, Montgomery, Ristretto) plus easy, explicit, proven-homomorphic conversion maps
  between them — that is the layer the implementation representations are described against.
- Confirms the architecture: **one group, many coordinate models, related by conversions** — so prove
  the group once (we anchor on Mathlib's Weierstrass) and *transport* to each model via a bijection;
  never re-prove the law per representation.
- Confirms `scratch.lean`'s point: the group law is **rational** in every coordinate model (it
  factors through the completed model / uses inverse-sqrt); the proliferation of models is about
  *speed and encoding*, never about a polynomial group law.
- Three tiers of "model" to keep distinct in our design: **(a)** speed-coordinate systems (bijections,
  pure transport), **(b)** byte encodings (encode/decode, a `≃` with a canonical-form predicate),
  **(c)** the Ristretto-style quotient (a new group = cofactor quotient + canonical reps).
- For us right now: Montgomery + (complete, affine) Edwards are tier-(a)/(b); Ristretto is tier-(c)
  and is correctly deferred — it is not just another coordinate chart.
