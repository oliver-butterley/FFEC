import FFEC.Field

/-!
# Framework: the transfer theorem

The single reusable mechanism of the project. The genuinely hard theorem — associativity of the
elliptic-curve group law — is already proven by Mathlib for Weierstrass (as the class group of the
coordinate ring, i.e. `Pic⁰`). We *consume* it: given a bijection from a model's point set to a
group, the entire `AddCommGroup` transports with **no axiom re-proved**, via `Equiv.addCommGroup`.

Two models of the same curve, both transferring to the same reference group, are then canonically
isomorphic (`crossEquiv`); when they transfer to the *same* group, the transported point groups are
canonically additively isomorphic (`crossAddEquiv`), with no addition-formula reasoning.
-/


universe u v

/-- The per-model datum: a bijection from a model's point set `Pt` to a reference group `G`.
By the transfer theorem this is *all* that is supplied per model. -/
structure GroupTransfer (Pt : Type u) (G : Type v) [AddCommGroup G] where
  equiv : Pt ≃ G

variable {Pt Pt' : Type u} {G : Type v} [AddCommGroup G]

/-- **Transfer theorem.** A bijection to a group transports the whole `AddCommGroup`
(associativity, commutativity, inverses) — no axiom re-proved. -/
@[reducible] noncomputable def GroupTransfer.addCommGroup (t : GroupTransfer Pt G) :
    AddCommGroup Pt :=
  t.equiv.addCommGroup

/-- **Cross-model isomorphism (sets).** Two models transferring to the same reference group have
canonically isomorphic point sets. -/
def GroupTransfer.crossEquiv (t : GroupTransfer Pt G) (t' : GroupTransfer Pt' G) : Pt ≃ Pt' :=
  t.equiv.trans t'.equiv.symm

/-- **Cross-model isomorphism (groups).** When two models transfer to the *same* reference group
`G`, their transported point GROUPS are canonically isomorphic — compose Mathlib's transported
additive equivalences (`Equiv.addEquiv`). No addition-formula reasoning is needed: this is exactly
why the same-`G` cross-model group iso is free (in contrast to the general, isomorphism-of-curves
case, which would require proving a variable change preserves the group law). -/
noncomputable def GroupTransfer.crossAddEquiv (t : GroupTransfer Pt G) (t' : GroupTransfer Pt' G) :
    letI := Equiv.add t.equiv; letI := Equiv.add t'.equiv; Pt ≃+ Pt' :=
  letI := Equiv.add t.equiv
  letI := Equiv.add t'.equiv
  (t.equiv.addEquiv).trans (t'.equiv.addEquiv).symm

