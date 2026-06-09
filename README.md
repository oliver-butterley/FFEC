# Finite Field Elliptic Curves

## Rough plan

We restrict to finite fields Fp.

An elliptic curve over Fp is pair: j-invariant, small galois thing

Model (p, curve):
- number of variables n
- mv polynomial (n variables),
- zero (0-point in Fp^(n+1))
- tuple of mv polynomial representing addition,
- mv polynomial representing negation

IsGroupModel (p, curve) extends Model (p, curve):
- validity proofs (all prop valued)

Instance (p, curve, h : IsGroupModel (p, curve)) : AddCommGroup (Model (p, curve)) where
  add := (use model.tuple)
  zero := zero
  ...

Theorem (p, curve, M : Model (p, curve), M' (p, curve)) : IsGroupModel M <-> IsGroupModel M'

Working with points on the curve is key. For this we use the fields of Model

Strategy: avoid reproving group structure of all the other models because we can take from the already proven results about Weierstrass.

Key models:
- Montgomery
- Edwards
- Ristretto
- Weierstrass (already exists in Mathlib)


## Roadmap

1. Make sure that it is true that an elliptic curve can be defined as above (fix the Galois thing)
2. Make sure we have explicit formulae for all the models (for zero/add/etc) in terms of j-invariant
3. Start scaffolding the entire thing

For point 1, the answer is "yes" and is described in [the pdf](K_IsoClasses_EC.pdf) (extracted from Silverman, *The Arithmetic of Elliptic Curves*, Chap X.5). It says that $$\mathbb{F}_p$$-isomorphism classes of elliptic curves over $$\mathbb{F}_p$$ are 1-1 with the set $$\mathbb{F}_p\times \mathbb{F}_p^\times/\sim$$ where  the equivalence relation is described in the pdf (it is fairly explicit). This can be made explicit, and in particular it shows that
* Generic j: two iso classes of curves;
* j = 1728: 4 iso classes if p ≡ 1 (mod 4), else 2 classes
* j = 0: 6 is classes if p ≡ 1 (mod 3), else 2 classes.

The real next step is to connect (the equivalence class of) a pair $$(x,y)\in\mathbb{F}_p\times\mathbb{F}_p^\times$$ to explicit models (i.e. to the coefficients of the  mv polynomial describing it). That being said, before embarking in this I would suggest that we stress-test our strategy, so for the time being let's content ourselves with a wrong/bad choice (like the constant function assigning to each $$(x,y)$$ the same mv polynomial), just to test if, downstream, everything seems to work. If yes, we'll come back to the true link between a pair and a model.
