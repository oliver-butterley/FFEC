import FFEC.Messy.Edwards.AddFormulaBase

/-! # `addFormula_eq_add`, part 2/3 — the coordinate-match certificates (pieces C and D).
These carry the large `linear_combination` certificates (Singular-computed, `ring`-checked),
isolated here so their heavy compilation does not collide with editing the rest. -/


open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)]

namespace TwistedEdwardsCurve

omit [DecidableEq F] [NeZero (2 : F)] in
/-- `toMontV` factors through `toMontU`: `toMontV x y = toMontU y / x`. Unconditional
(both sides are `(1 + y) / ((1 - y) * x)` after `div_div`). -/
theorem toMontV_eq_toMontU_div (x y : F) : toMontV x y = toMontU y / x := by
  unfold toMontV toMontU; rw [div_div]

/-! ### Singular cofactor certificates

Each lemma below states verbatim the polynomial identity left after `field_simp` at the
corresponding `linear_combination` site in `generic_addX`/`generic_addY`/`generic_addY_secant`,
and discharges it with the externally-computed (Singular `lift`) cofactor, re-checked by `ring`
inside `linear_combination`. Isolating them as standalone polynomial identities keeps the main
proofs as clean dispatch and concentrates the heavy compilation here. The hypotheses are the
curve equations in their `TwistedEdwardsCurve.Equation`-rewritten form. -/

omit [DecidableEq F] [NeZero (2 : F)] in
/-- Cofactor certificate for the **doubling** branch of `generic_addX` (one point after `subst`). -/
private theorem cert_addX_double (E : TwistedEdwardsCurve F) {x₁ y₁ : F}
    (h1 : E.a * x₁ ^ 2 + y₁ ^ 2 = 1 + E.d * x₁ ^ 2 * y₁ ^ 2) :
    4 * (E.a - E.d) * (1 - E.d * y₁ ^ 2 * x₁ ^ 2 + (y₁ ^ 2 - E.a * x₁ ^ 2)) * (1 + y₁) ^ 2 * (1 -
        y₁) ^ 2 * (1 - -1) ^ 2 =
    (1 - E.d * y₁ ^ 2 * x₁ ^ 2 - (y₁ ^ 2 - E.a * x₁ ^ 2)) *
      (x₁ ^ 2 *
              ((1 + y₁) * ((E.a - E.d) * 3 * (1 + y₁) + (1 - y₁) * 2 ^ 2 * (E.a + E.d)) + (E.a -
                  E.d) * (1 - y₁) ^ 2) ^
                2 -
            4 * (1 + y₁) ^ 2 * (1 - y₁) ^ 2 * 2 * (E.a + E.d) * (1 - -1) ^ 2 -
          4 * (E.a - E.d) * (1 + y₁) ^ 3 * (1 - y₁) * (1 - -1) ^ 2 -
        4 * (E.a - E.d) * (1 + y₁) ^ 3 * (1 - y₁) * (1 - -1) ^ 2) := by
  linear_combination
      (-64*E.d^2*x₁^2*y₁^4+64*E.a*E.d*x₁^2*y₁^3-64*E.d^2*x₁^2*y₁^3-16*E.a^2*x₁^2*y₁^2
      +160*E.a*E.d*x₁^2*y₁^2-16*E.d^2*x₁^2*y₁^2-64*E.a^2*x₁^2*y₁+64*E.a*E.d*x₁^2*y₁+16*E.a*y₁^4
      -80*E.d*y₁^4-64*E.a^2*x₁^2+64*E.a*y₁^3-64*E.d*y₁^3+64*E.a*y₁^2+64*E.d*y₁^2-64*E.a*y₁+64*E.d*y₁
      -80*E.a+16*E.d) * h1

omit [DecidableEq F] [NeZero (2 : F)] in
/-- Cofactor certificate for the **secant** branch of `generic_addX`. -/
private theorem cert_addX_secant (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.a * x₁ ^ 2 + y₁ ^ 2 = 1 + E.d * x₁ ^ 2 * y₁ ^ 2)
    (h2 : E.a * x₂ ^ 2 + y₂ ^ 2 = 1 + E.d * x₂ ^ 2 * y₂ ^ 2) :
    4 * (E.a - E.d) * x₁ ^ 2 * x₂ ^ 2 * (1 - E.d * y₁ * y₂ * x₁ * x₂ + (y₁ * y₂ - E.a * x₁ * x₂)) *
        (1 - y₁) * (1 - y₂) *
      ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 =
    4 * (1 - E.d * y₁ * y₂ * x₁ * x₂ - (y₁ * y₂ - E.a * x₁ * x₂)) *
      ((1 - y₂) *
          ((1 - y₁) *
              ((x₂ * (1 + y₁) * (1 - y₂) - x₁ * (1 - y₁) * (1 + y₂)) *
                  (4 * (x₂ * (1 + y₁) * (1 - y₂) - x₁ * (1 - y₁) * (1 + y₂)) +
                    (E.a - E.d) * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) * 0) -
                x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 * 2 * (E.a + E.d))
                    -
            (E.a - E.d) * x₁ ^ 2 * x₂ ^ 2 * (1 + y₁) * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^
                2) -
        (E.a - E.d) * x₁ ^ 2 * x₂ ^ 2 * (1 - y₁) * (1 + y₂) * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 +
            y₂)) ^ 2) := by
  linear_combination
        (16*E.a*x₁*y₁^2*x₂^3*y₂^2-16*E.a*x₁*y₁*x₂^3*y₂^3-48*E.a*x₁*y₁^2*x₂^3*y₂
        -16*E.d*x₁*y₁^2*x₂^3*y₂+64*E.a*x₁*y₁*x₂^3*y₂^2-16*E.a*x₁*x₂^3*y₂^3-16*x₁*y₁^2*x₂*y₂^4
        +16*y₁^2*x₂^2*y₂^4+48*E.a*x₁*y₁^2*x₂^3-96*E.a*x₁*y₁*x₂^3*y₂-16*E.d*x₁*y₁*x₂^3*y₂
        +48*E.a*x₁*x₂^3*y₂^2-16*x₁*y₁^2*x₂*y₂^3-48*y₁^2*x₂^2*y₂^3+48*x₁*y₁*x₂*y₂^4+16*y₁*x₂^2*y₂^4
        +64*E.a*x₁*y₁*x₂^3-48*E.a*x₁*x₂^3*y₂+64*x₁*y₁^2*x₂*y₂^2+48*y₁^2*x₂^2*y₂^2-48*x₁*y₁*x₂*y₂^3
        -64*y₁*x₂^2*y₂^3+16*E.a*x₁*x₂^3+16*x₁*y₁^2*x₂*y₂-16*y₁^2*x₂^2*y₂-32*x₁*y₁*x₂*y₂^2
        +96*y₁*x₂^2*y₂^2-32*x₁*x₂*y₂^3-16*x₂^2*y₂^3-48*x₁*y₁^2*x₂+48*x₁*y₁*x₂*y₂-64*y₁*x₂^2*y₂
        +32*x₁*x₂*y₂^2+48*x₂^2*y₂^2-16*x₁*y₁*x₂+16*y₁*x₂^2+32*x₁*x₂*y₂-48*x₂^2*y₂-32*x₁*x₂+16*x₂^2)
        * h1 +
        (48*E.d*x₁^3*y₁^4*x₂-16*E.a*x₁^3*y₁^3*x₂*y₂-96*E.d*x₁^3*y₁^3*x₂*y₂+16*E.a*x₁^3*y₁^2*x₂*y₂^2
        +48*E.d*x₁^3*y₁^2*x₂*y₂^2-16*E.a*x₁^3*y₁^3*x₂+16*E.d*x₁^3*y₁^3*x₂+64*E.a*x₁^3*y₁^2*x₂*y₂
        +16*E.d*x₁^3*y₁^2*x₂*y₂+16*x₁^2*y₁^4*y₂^2-48*E.a*x₁^3*y₁*x₂*y₂^2-16*E.d*x₁^3*y₁*x₂*y₂^2
        -16*x₁*y₁^4*x₂*y₂^2+32*E.d*x₁^3*y₁^2*x₂+16*x₁^2*y₁^4*y₂-16*E.d*x₁^3*y₁*x₂*y₂
        +48*x₁*y₁^4*x₂*y₂-48*x₁^2*y₁^3*y₂^2-16*x₁*y₁^3*x₂*y₂^2-64*E.a*x₁^3*y₁*x₂-48*x₁*y₁^4*x₂
        -64*x₁^2*y₁^3*y₂+48*E.a*x₁^3*x₂*y₂+48*x₁*y₁^3*x₂*y₂+48*x₁^2*y₁^2*y₂^2+16*x₁*y₁^2*x₂*y₂^2
        -16*x₁^2*y₁^3-16*E.a*x₁^3*x₂-48*x₁*y₁^3*x₂+96*x₁^2*y₁^2*y₂-48*x₁*y₁^2*x₂*y₂-16*x₁^2*y₁*y₂^2
        +16*x₁*y₁*x₂*y₂^2+48*x₁^2*y₁^2+48*x₁*y₁^2*x₂-64*x₁^2*y₁*y₂-48*x₁*y₁*x₂*y₂-48*x₁^2*y₁
        +48*x₁*y₁*x₂+16*x₁^2*y₂+16*x₁^2) * h2

omit [DecidableEq F] [NeZero (2 : F)] in
/-- Cofactor certificate for the `hY2` step (`sum = (0,-1)` leaf) of `generic_addY_secant`. -/
private theorem cert_secant_negY (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.a * x₁ ^ 2 + y₁ ^ 2 = 1 + E.d * x₁ ^ 2 * y₁ ^ 2)
    (h2 : E.a * x₂ ^ 2 + y₂ ^ 2 = 1 + E.d * x₂ ^ 2 * y₂ ^ 2)
    (hsX : x₁ * y₂ + y₁ * x₂ = 0)
    (gsY : y₁ * y₂ - E.a * x₁ * x₂ + 1 - E.d * x₁ * x₂ * y₁ * y₂ = 0) :
    (y₁ + y₂) * ((E.d * x₁ * x₂ * y₁ * y₂) ^ 2 - 1) = 0 := by
  linear_combination (-E.d*x₁*x₂*y₂^3-E.d*x₂^2*y₂^3+E.a*x₂^2*y₂+y₂^3+y₂) * h1 +
      (-E.d*x₁^2*y₁^2*y₂+E.d*x₁^2*y₁*y₂^2+y₂) * h2 +
      (E.d^2*x₁^2*y₁^2*x₂*y₂^2+2*E.a*E.d*x₁^2*y₁*x₂*y₂+E.a*E.d*x₁^2*x₂*y₂^2-E.d*x₁*y₁*y₂^3
      +E.d*y₁*x₂*y₂^3-E.d*x₁*y₁*y₂-E.a*y₁*x₂*y₂-E.a*x₁*y₂^2-E.a*x₁) * hsX +
      (2*E.d*x₁^2*y₁*y₂^2+E.d*x₁*y₁*x₂*y₂^2-E.d*x₁*x₂*y₂^3+E.a*x₁*x₂*y₂-y₁*y₂^2-y₁+y₂) * gsY

omit [DecidableEq F] [NeZero (2 : F)] in
/-- Cofactor certificate for the `sumX ≠ 0` branch of `generic_addY_secant`. -/
private theorem cert_addY_secant (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.a * x₁ ^ 2 + y₁ ^ 2 = 1 + E.d * x₁ ^ 2 * y₁ ^ 2)
    (h2 : E.a * x₂ ^ 2 + y₂ ^ 2 = 1 + E.d * x₂ ^ 2 * y₂ ^ 2) :
    4 ^ 2 * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) *
        ((1 - y₂) *
            ((1 - y₁) *
                (((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) *
                    (4 * ((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) +
                      (E.a - E.d) * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) * 0) -
                  x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 * 2 * (E.a +
                      E.d)) -
              (E.a - E.d) * (1 + y₁) * x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂))
                  ^ 2) -
          (E.a - E.d) * (1 - y₁) * x₁ ^ 2 * (1 + y₂) * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1
              + y₂)) ^ 2) *
      (1 + E.d * y₁ * x₁ * y₂ * x₂) =
    (4 *
          (-(4 *
                (((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) *
                    ((1 - y₂) *
                          ((1 - y₁) *
                              (((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) *
                                  (4 * ((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) +
                                    (E.a - E.d) * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 +
                                        y₂)) * 0) -
                                x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 *
                                    2 * (E.a + E.d)) -
                            (E.a - E.d) * (1 + y₁) * x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 -
                                y₁) * (1 + y₂)) ^ 2) -
                        (E.a - E.d) * (1 - y₁) * x₁ ^ 2 * (1 + y₂) * x₂ ^ 2 *
                          ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 -
                      (E.a - E.d) * (1 + y₁) * x₁ ^ 2 * (1 - y₂) * x₂ ^ 2 *
                        ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2) +
                  (E.a - E.d) * (1 + y₁) * x₁ ^ 2 * (1 - y₂) * x₂ ^ 3 *
                    ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 3)) -
            (E.a - E.d) * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) * 0 *
              ((1 - y₂) *
                  ((1 - y₁) *
                      (((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) *
                          (4 * ((1 + y₁) * (1 - y₂) * x₂ - (1 - y₁) * x₁ * (1 + y₂)) +
                            (E.a - E.d) * x₁ * x₂ * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) * 0)
                                -
                        x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂)) ^ 2 * 2 * (E.a
                            + E.d)) -
                    (E.a - E.d) * (1 + y₁) * x₁ ^ 2 * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 - y₁) * (1
                        + y₂)) ^ 2) -
                (E.a - E.d) * (1 - y₁) * x₁ ^ 2 * (1 + y₂) * x₂ ^ 2 * ((1 + y₁) * (1 - y₂) - (1 -
                    y₁) * (1 + y₂)) ^ 2)) -
        (E.a - E.d) ^ 3 * (1 - y₁) * x₁ ^ 3 * (1 - y₂) * x₂ ^ 3 * ((1 + y₁) * (1 - y₂) - (1 - y₁) *
            (1 + y₂)) ^ 3 * 0) *
      (x₁ * y₂ + y₁ * x₂) := by
  linear_combination
        (-256*E.a*x₁^2*y₁^3*x₂^4*y₂-256*E.d*x₁^2*y₁^3*x₂^4*y₂+512*E.a*x₁^2*y₁^2*x₂^4*y₂^2
        -256*E.a*x₁^2*y₁*x₂^4*y₂^3-128*x₁^2*y₁^3*x₂^2*y₂^4+192*x₁*y₁^3*x₂^3*y₂^4-64*y₁^3*x₂^4*y₂^4
        +64*x₁^2*y₁^2*x₂^2*y₂^5-64*x₁*y₁^2*x₂^3*y₂^5+512*E.a*x₁^2*y₁^3*x₂^4
        -1024*E.a*x₁^2*y₁^2*x₂^4*y₂+512*E.a*x₁^2*y₁*x₂^4*y₂^2-128*x₁^2*y₁^3*x₂^2*y₂^3
        -384*x₁*y₁^3*x₂^3*y₂^3+256*y₁^3*x₂^4*y₂^3+384*x₁^2*y₁^2*x₂^2*y₂^4+256*x₁*y₁^2*x₂^3*y₂^4
        -128*y₁^2*x₂^4*y₂^4-128*x₁^2*y₁*x₂^2*y₂^5-128*x₁*y₁*x₂^3*y₂^5+512*E.a*x₁^2*y₁^2*x₂^4
        -256*E.a*x₁^2*y₁*x₂^4*y₂+640*x₁^2*y₁^3*x₂^2*y₂^2-384*y₁^3*x₂^4*y₂^2-1024*x₁^2*y₁^2*x₂^2*y₂^3
        -256*x₁*y₁^2*x₂^3*y₂^3+512*y₁^2*x₂^4*y₂^3+640*x₁^2*y₁*x₂^2*y₂^4+192*x₁*y₁*x₂^3*y₂^4
        -64*y₁*x₂^4*y₂^4-192*x₁^2*x₂^2*y₂^5-64*x₁*x₂^3*y₂^5+128*x₁^2*y₁^3*x₂^2*y₂
        +384*x₁*y₁^3*x₂^3*y₂+256*y₁^3*x₂^4*y₂+128*x₁^2*y₁^2*x₂^2*y₂^2-128*x₁*y₁^2*x₂^3*y₂^2
        -768*y₁^2*x₂^4*y₂^2-384*x₁^2*y₁*x₂^2*y₂^3+128*x₁*y₁*x₂^3*y₂^3+256*y₁*x₂^4*y₂^3
        +128*x₁^2*x₂^2*y₂^4+128*x₁*x₂^3*y₂^4-512*x₁^2*y₁^3*x₂^2-192*x₁*y₁^3*x₂^3-64*y₁^3*x₂^4
        +960*x₁^2*y₁^2*x₂^2*y₂+320*x₁*y₁^2*x₂^3*y₂+512*y₁^2*x₂^4*y₂-640*x₁^2*y₁*x₂^2*y₂^2
        -256*x₁*y₁*x₂^3*y₂^2-384*y₁*x₂^4*y₂^2+256*x₁^2*x₂^2*y₂^3-512*x₁^2*y₁^2*x₂^2-128*x₁*y₁^2*x₂^3
        -128*y₁^2*x₂^4+512*x₁^2*y₁*x₂^2*y₂+256*y₁*x₂^4*y₂-128*x₁^2*x₂^2*y₂^2-128*x₁*x₂^3*y₂^2
        +64*x₁*y₁*x₂^3-64*y₁*x₂^4-64*x₁^2*x₂^2*y₂+64*x₁*x₂^3*y₂) * h1 +
        (512*E.d*x₁^4*y₁^5*x₂^2-1536*E.d*x₁^4*y₁^4*x₂^2*y₂+1536*E.d*x₁^4*y₁^3*x₂^2*y₂^2
        -512*E.d*x₁^4*y₁^2*x₂^2*y₂^3+512*E.d*x₁^4*y₁^4*x₂^2+256*E.a*x₁^4*y₁^3*x₂^2*y₂
        +64*x₁^3*y₁^5*x₂*y₂^2-512*E.a*x₁^4*y₁^2*x₂^2*y₂^2-512*E.d*x₁^4*y₁^2*x₂^2*y₂^2
        -64*x₁^2*y₁^5*x₂^2*y₂^2+64*x₁^4*y₁^4*y₂^3-192*x₁^3*y₁^4*x₂*y₂^3+256*E.a*x₁^4*y₁*x₂^2*y₂^3
        +256*E.d*x₁^4*y₁*x₂^2*y₂^3+128*x₁^2*y₁^4*x₂^2*y₂^3-512*E.a*x₁^4*y₁^3*x₂^2
        +128*x₁^3*y₁^5*x₂*y₂+1024*E.a*x₁^4*y₁^2*x₂^2*y₂+128*x₁^2*y₁^5*x₂^2*y₂+128*x₁^4*y₁^4*y₂^2
        -256*x₁^3*y₁^4*x₂*y₂^2-512*E.a*x₁^4*y₁*x₂^2*y₂^2-384*x₁^2*y₁^4*x₂^2*y₂^2-256*x₁^4*y₁^3*y₂^3
        +384*x₁^3*y₁^3*x₂*y₂^3+128*x₁^2*y₁^3*x₂^2*y₂^3+64*x₁^3*y₁^5*x₂-512*E.a*x₁^4*y₁^2*x₂^2
        -320*x₁^2*y₁^5*x₂^2+64*x₁^4*y₁^4*y₂-192*x₁^3*y₁^4*x₂*y₂+256*E.a*x₁^4*y₁*x₂^2*y₂
        +896*x₁^2*y₁^4*x₂^2*y₂-512*x₁^4*y₁^3*y₂^2+256*x₁^3*y₁^3*x₂*y₂^2-512*x₁^2*y₁^3*x₂^2*y₂^2
        +384*x₁^4*y₁^2*y₂^3-128*x₁^2*y₁^2*x₂^2*y₂^3-128*x₁^3*y₁^4*x₂-640*x₁^2*y₁^4*x₂^2
        -256*x₁^4*y₁^3*y₂-128*x₁^3*y₁^3*x₂*y₂+384*x₁^2*y₁^3*x₂^2*y₂+768*x₁^4*y₁^2*y₂^2
        +128*x₁^3*y₁^2*x₂*y₂^2+384*x₁^2*y₁^2*x₂^2*y₂^2-256*x₁^4*y₁*y₂^3-384*x₁^3*y₁*x₂*y₂^3
        -128*x₁^2*y₁*x₂^2*y₂^3+256*x₁^2*y₁^3*x₂^2+384*x₁^4*y₁^2*y₂+256*x₁^3*y₁^2*x₂*y₂
        -896*x₁^2*y₁^2*x₂^2*y₂-512*x₁^4*y₁*y₂^2-320*x₁^3*y₁*x₂*y₂^2+576*x₁^2*y₁*x₂^2*y₂^2
        +64*x₁^4*y₂^3+192*x₁^3*x₂*y₂^3+128*x₁^3*y₁^2*x₂+640*x₁^2*y₁^2*x₂^2-256*x₁^4*y₁*y₂
        -512*x₁^2*y₁*x₂^2*y₂+128*x₁^4*y₂^2+128*x₁^3*x₂*y₂^2-64*x₁^3*y₁*x₂+64*x₁^2*y₁*x₂^2+64*x₁^4*y₂
        -64*x₁^3*x₂*y₂) * h2

omit [DecidableEq F] [NeZero (2 : F)] in
/-- Cofactor certificate for the **doubling** branch of `generic_addY` (one point after `subst`). -/
private theorem cert_addY_double (E : TwistedEdwardsCurve F) {x₁ y₁ : F}
    (h1 : E.a * x₁ ^ 2 + y₁ ^ 2 = 1 + E.d * x₁ ^ 2 * y₁ ^ 2) :
    4 ^ 2 * (E.a - E.d) * (1 - E.d * y₁ ^ 2 * x₁ ^ 2 + (y₁ ^ 2 - E.a * x₁ ^ 2)) * (1 + E.d * y₁ ^ 2
        * x₁ ^ 2) *
          (1 + y₁) ^ 3 *
        (1 - y₁) ^ 3 *
      (1 - -1) ^ 3 =
    -(y₁ * (1 - E.d * y₁ ^ 2 * x₁ ^ 2 - (y₁ ^ 2 - E.a * x₁ ^ 2)) * (1 + 1) *
        (x₁ ^ 2 *
              ((1 + y₁) * ((E.a - E.d) * 3 * (1 + y₁) + (1 - y₁) * 2 ^ 2 * (E.a + E.d)) + (E.a -
                  E.d) * (1 - y₁) ^ 2) *
            (x₁ ^ 2 *
                      ((1 + y₁) * ((E.a - E.d) * 3 * (1 + y₁) + (1 - y₁) * 2 ^ 2 * (E.a + E.d)) +
                          (E.a - E.d) * (1 - y₁) ^ 2) ^
                        2 -
                    4 * (1 + y₁) ^ 2 * (1 - y₁) ^ 2 * 2 * (E.a + E.d) * (1 - -1) ^ 2 -
                  4 * (E.a - E.d) * (1 + y₁) ^ 3 * (1 - y₁) * (1 - -1) ^ 2 -
                4 * (E.a - E.d) * (1 + y₁) ^ 3 * (1 - y₁) * (1 - -1) ^ 2 -
              4 * (E.a - E.d) * (1 + y₁) ^ 3 * (1 - y₁) * (1 - -1) ^ 2) +
          4 ^ 2 * (E.a - E.d) * (1 + y₁) ^ 4 * (1 - y₁) ^ 2 * (1 - -1) ^ 3)) := by
  linear_combination
      (-1024*E.d^3*x₁^4*y₁^7+1536*E.a*E.d^2*x₁^4*y₁^6-1536*E.d^3*x₁^4*y₁^6-768*E.a^2*E.d*x₁^4*y₁^5
      +4608*E.a*E.d^2*x₁^4*y₁^5-768*E.d^3*x₁^4*y₁^5-128*E.a*E.d*x₁^2*y₁^8+128*E.d^2*x₁^2*y₁^8
      +128*E.a^3*x₁^4*y₁^4-3456*E.a^2*E.d*x₁^4*y₁^4+3456*E.a*E.d^2*x₁^4*y₁^4-128*E.d^3*x₁^4*y₁^4
      -256*E.a*E.d*x₁^2*y₁^7-768*E.d^2*x₁^2*y₁^7+768*E.a^3*x₁^4*y₁^3-4608*E.a^2*E.d*x₁^4*y₁^3
      +768*E.a*E.d^2*x₁^4*y₁^3-128*E.a^2*x₁^2*y₁^6+1408*E.a*E.d*x₁^2*y₁^6-1280*E.d^2*x₁^2*y₁^6
      +1536*E.a^3*x₁^4*y₁^2-1536*E.a^2*E.d*x₁^4*y₁^2-512*E.a^2*x₁^2*y₁^5+3328*E.a*E.d*x₁^2*y₁^5
      +256*E.d^2*x₁^2*y₁^5+1024*E.a^3*x₁^4*y₁-768*E.a^2*x₁^2*y₁^4-384*E.a*E.d*x₁^2*y₁^4
      +1152*E.d^2*x₁^2*y₁^4-256*E.a*y₁^7+256*E.d*y₁^7-256*E.a^2*x₁^2*y₁^3-3328*E.a*E.d*x₁^2*y₁^3
      +512*E.d^2*x₁^2*y₁^3-640*E.a*y₁^6+640*E.d*y₁^6+896*E.a^2*x₁^2*y₁^2-896*E.a*E.d*x₁^2*y₁^2
      +256*E.a*y₁^5-256*E.d*y₁^5+768*E.a^2*x₁^2*y₁+256*E.a*E.d*x₁^2*y₁+1152*E.a*y₁^4-1152*E.d*y₁^4
      +256*E.a*y₁^3-256*E.d*y₁^3-384*E.a*y₁^2+384*E.d*y₁^2-256*E.a*y₁+256*E.d*y₁-128*E.a+128*E.d) *
      h1

/-- **Piece C** (X-coordinate match): the TwistedEdwardsCurve sum's W-`x` equals Weierstrass `addX`.
Discharge by splitting `y₁ = y₂` / `y₁ ≠ y₂` (so `slope` is concrete), `field_simp`, then
`linear_combination` against `h1, h2`. -/
theorem generic_addX (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    E.toMontgomery.B * toMontU (E.addCoords x₁ y₁ x₂ y₂).2 =
      (E.toMontgomery.toWeierstrass).toAffine.addX (E.toMontgomery.B * toMontU y₁)
        (E.toMontgomery.B * toMontU y₂)
        ((E.toMontgomery.toWeierstrass).toAffine.slope (E.toMontgomery.B * toMontU y₁)
          (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₁ y₁)
          (E.toMontgomery.B ^ 2 * toMontV x₂ y₂)) := by
  obtain ⟨hpos, hneg⟩ := E.denoms_ne_zero h1 h2
  have h1y : (1 : F) - y₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h1 hP))
  have h2y : (1 : F) - y₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h2 hQ))
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  by_cases hx1 : x₁ = 0
  · -- **2-torsion input** `P = (0, -1)`.
    subst hx1
    have hy1 : y₁ = -1 := by
      rw [TwistedEdwardsCurve.Equation] at h1
      rcases mul_eq_zero.mp (show (y₁ - 1) * (y₁ + 1) = 0 by linear_combination h1) with h | h
      · exact absurd (by linear_combination h : y₁ = 1) (fun hh => hP ⟨rfl, hh⟩)
      · linear_combination h
    subst hy1
    have hx2 : x₂ ≠ 0 := by
      intro h; subst h
      rcases mul_eq_zero.mp (show (y₂ - 1) * (y₂ + 1) = 0 by
        rw [TwistedEdwardsCurve.Equation] at h2; linear_combination h2) with h | h
      · exact hQ ⟨rfl, by linear_combination h⟩
      · exact hinv ⟨by ring, by linear_combination h⟩
    have h4ne : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero MontgomeryCurve.two_ne_zero MontgomeryCurve.two_ne_zero
    have hBne : E.toMontgomery.B ≠ 0 := by
      have : E.toMontgomery.B = 4 / (E.a - E.d) := rfl
      rw [this]; exact div_ne_zero h4ne had
    have hU1 : toMontU (-1 : F) = 0 := by unfold toMontU; norm_num
    have hV1 : toMontV (0 : F) (-1) = 0 := by unfold toMontV; norm_num
    have hy2nm1 : y₂ ≠ -1 := by
      intro h; apply hx2
      rw [TwistedEdwardsCurve.Equation, h] at h2
      have : (E.a - E.d) * x₂ ^ 2 = 0 := by linear_combination h2
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have hU2ne : toMontU y₂ ≠ 0 := by
      unfold toMontU; rw [div_ne_zero_iff]
      exact ⟨fun h => hy2nm1 (by linear_combination h), h2y⟩
    have hUUne : E.toMontgomery.B * toMontU (-1 : F) ≠ E.toMontgomery.B * toMontU y₂ := by
      rw [hU1, mul_zero]; exact fun h => (mul_ne_zero hBne hU2ne) h.symm
    rw [WeierstrassCurve.Affine.slope_of_X_ne hUUne]
    have h1y2p : (1 : F) + y₂ ≠ 0 := fun h => hy2nm1 (by linear_combination h)
    rw [hU1, hV1]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, TwistedEdwardsCurve.toMontgomery,
      MontgomeryCurve.toWeierstrass, WeierstrassCurve.Affine.addX,
      toMontU, toMontV, TwistedEdwardsCurve.addCoords]
    field_simp [h1y2p]
    rw [TwistedEdwardsCurve.Equation] at h2
    linear_combination (256 * y₂ ^ 2 + 512 * y₂ + 256) * h2
  by_cases hx2 : x₂ = 0
  · -- **2-torsion input** `Q = (0, -1)`.
    subst hx2
    have hy2 : y₂ = -1 := by
      rw [TwistedEdwardsCurve.Equation] at h2
      rcases mul_eq_zero.mp (show (y₂ - 1) * (y₂ + 1) = 0 by linear_combination h2) with h | h
      · exact absurd (by linear_combination h : y₂ = 1) (fun hh => hQ ⟨rfl, hh⟩)
      · linear_combination h
    subst hy2
    have h4ne : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero MontgomeryCurve.two_ne_zero MontgomeryCurve.two_ne_zero
    have hBne : E.toMontgomery.B ≠ 0 := by
      have : E.toMontgomery.B = 4 / (E.a - E.d) := rfl
      rw [this]; exact div_ne_zero h4ne had
    have hU2 : toMontU (-1 : F) = 0 := by unfold toMontU; norm_num
    have hV2 : toMontV (0 : F) (-1) = 0 := by unfold toMontV; norm_num
    have hy1nm1 : y₁ ≠ -1 := by
      intro h; apply hx1
      rw [TwistedEdwardsCurve.Equation, h] at h1
      have : (E.a - E.d) * x₁ ^ 2 = 0 := by linear_combination h1
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have hU1ne : toMontU y₁ ≠ 0 := by
      unfold toMontU; rw [div_ne_zero_iff]
      exact ⟨fun h => hy1nm1 (by linear_combination h), h1y⟩
    have hUUne : E.toMontgomery.B * toMontU y₁ ≠ E.toMontgomery.B * toMontU (-1 : F) := by
      rw [hU2, mul_zero]; exact mul_ne_zero hBne hU1ne
    rw [WeierstrassCurve.Affine.slope_of_X_ne hUUne]
    have h1y1p : (1 : F) + y₁ ≠ 0 := fun h => hy1nm1 (by linear_combination h)
    rw [hU2, hV2]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, TwistedEdwardsCurve.toMontgomery,
      MontgomeryCurve.toWeierstrass, WeierstrassCurve.Affine.addX,
      toMontU, toMontV, TwistedEdwardsCurve.addCoords]
    field_simp [h1y1p]
    rw [TwistedEdwardsCurve.Equation] at h1
    linear_combination 4 * h1
  by_cases hUU : E.toMontgomery.B * toMontU y₁ = E.toMontgomery.B * toMontU y₂
  · -- **Doubling** `P = Q`: `U₁=U₂ ⟹ y₂=y₁` (injectivity), then `¬inv` + curve ⟹ `x₂=x₁`.
    -- NB: `h4ne`/`hBne` are kept local — in scope they'd make `field_simp` cancel the factor `4`,
    -- changing the cleared polynomial (and breaking the secant branch's pasted certificate).
    have h4ne : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero MontgomeryCurve.two_ne_zero MontgomeryCurve.two_ne_zero
    have hBne : E.toMontgomery.B ≠ 0 := by
      have : E.toMontgomery.B = 4 / (E.a - E.d) := rfl
      rw [this]; exact div_ne_zero h4ne had
    have hVne : E.toMontgomery.B ^ 2 * toMontV x₁ y₁ ≠
        (E.toMontgomery.toWeierstrass).toAffine.negY (E.toMontgomery.B * toMontU y₂)
          (E.toMontgomery.B ^ 2 * toMontV x₂ y₂) :=
      fun hV => E.generic_notWInv h1 h2 hP hQ hinv ⟨hUU, hV⟩
    have hy : y₂ = y₁ := by
      have hUeq : toMontU y₁ = toMontU y₂ := mul_left_cancel₀ hBne hUU
      unfold toMontU at hUeq
      rw [div_eq_div_iff h1y h2y] at hUeq
      have h20 : (2 : F) * (y₂ - y₁) = 0 := by linear_combination -hUeq
      linear_combination (mul_eq_zero.mp h20).resolve_left MontgomeryCurve.two_ne_zero
    subst y₂
    have hy1nm1 : y₁ ≠ -1 := by
      intro h; refine hx1 ?_
      rw [TwistedEdwardsCurve.Equation, h] at h1
      have : (E.a - E.d) * x₁ ^ 2 = 0 := by linear_combination h1
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have ha1' : E.a - E.d * y₁ ^ 2 ≠ 0 := by
      intro h0
      rw [TwistedEdwardsCurve.Equation] at h1
      have e : (E.a - E.d * y₁ ^ 2) * x₁ ^ 2 = 1 - y₁ ^ 2 := by linear_combination h1
      rw [h0, zero_mul] at e
      rcases mul_eq_zero.mp (show (y₁ - 1) * (y₁ + 1) = 0 by linear_combination e) with h | h
      · exact (E.y_ne_one h1 hP) (by linear_combination h)
      · exact hy1nm1 (by linear_combination h)
    have hx : x₂ = x₁ := by
      rw [TwistedEdwardsCurve.Equation] at h1 h2
      have e : (E.a - E.d * y₁ ^ 2) * (x₁ ^ 2 - x₂ ^ 2) = 0 := by linear_combination h1 - h2
      have hsq : x₁ ^ 2 = x₂ ^ 2 := by linear_combination (mul_eq_zero.mp e).resolve_left ha1'
      rcases mul_eq_zero.mp (show (x₂ - x₁) * (x₂ + x₁) = 0 by linear_combination -hsq) with h | h
      · linear_combination h
      · exact absurd ⟨by linear_combination h, rfl⟩ hinv
    subst x₂
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hUU hVne]
    have hy1p : (1 : F) + y₁ ≠ 0 := fun h => hy1nm1 (by linear_combination h)
    have hnegD : (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 ≠ 0 := by
      rw [show (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 = 1 - E.d * x₁ * x₁ * y₁ * y₁ from by ring]
      exact hneg
    have hsumnumD : (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 - (y₁ ^ 2 - E.a * x₁ ^ 2) ≠ 0 := by
      intro hh
      refine (E.y_ne_one (E.addCoords_onCurve h1 h2) (E.generic_sumNeId h1 h2 hinv)) ?_
      simp only [TwistedEdwardsCurve.addCoords]
      rw [div_eq_one_iff_eq (by rw [show (1 : F) - E.d * x₁ * x₁ * y₁ * y₁
        = 1 - E.d * y₁ ^ 2 * x₁ ^ 2 from by ring]; exact hnegD)]
      linear_combination -hh
    simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
        WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.negY, toMontU, toMontV, TwistedEdwardsCurve.addCoords, zero_mul,
      sub_zero, add_zero]
    have h2c : (1 : F) - -1 ≠ 0 := by
      rw [show (1 : F) - -1 = 2 from by ring]; exact MontgomeryCurve.two_ne_zero
    field_simp [hy1p, hsumnumD, hnegD, h2c]
    rw [TwistedEdwardsCurve.Equation] at h1
    -- single-point (doubling) cofactor: dispatch to the isolated certificate lemma.
    exact E.cert_addX_double h1
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hUU]
    have hyne : y₁ ≠ y₂ := fun h => hUU (by rw [h])
    have hneg' : (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ ≠ 0 := by
      rw [show (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ = 1 - E.d * x₁ * x₂ * y₁ * y₂ from by ring]
      exact hneg
    have hslopeden : (1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂) ≠ 0 := by
      rw [show (1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂) = 2 * (y₁ - y₂) from by ring]
      exact mul_ne_zero MontgomeryCurve.two_ne_zero (sub_ne_zero.mpr hyne)
    have hsumnum : (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ - (y₁ * y₂ - E.a * x₁ * x₂) ≠ 0 := by
      intro hh
      refine (E.y_ne_one (E.addCoords_onCurve h1 h2) (E.generic_sumNeId h1 h2 hinv)) ?_
      simp only [TwistedEdwardsCurve.addCoords]
      rw [div_eq_one_iff_eq (by rw [show (1 : F) - E.d * x₁ * x₂ * y₁ * y₂
        = 1 - E.d * y₁ * y₂ * x₁ * x₂ from by ring]; exact hneg')]
      linear_combination -hh
    simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
        WeierstrassCurve.Affine.addX,
      toMontU, toMontV, TwistedEdwardsCurve.addCoords]
    field_simp [hslopeden, hsumnum, hneg']
    rw [TwistedEdwardsCurve.Equation] at h1 h2
    -- Secant-case cofactors: dispatch to the isolated certificate lemma.
    exact E.cert_addX_secant h1 h2
/-- The **secant** case of `generic_addY`. The `sumX ≠ 0` leaf reuses the proven
`generic_addX` (via `toMontV x y = toMontU y / x`, `toMontV_eq_toMontU_div`) to rewrite the
LHS `B² · toMontV sumX sumY` as `B · addX / sumX`, turning the goal into the lower-degree
identity `B · addX = addY · sumX`. This avoids the double-nested `toMontV (sumX, sumY)`
fraction, so the cleared polynomial certificate fits the default heartbeat budget (no bump). -/
theorem generic_addY_secant (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁))
    (hUU : ¬ E.toMontgomery.B * toMontU y₁ = E.toMontgomery.B * toMontU y₂)
    (hx1 : ¬x₁ = 0) (hx2 : ¬x₂ = 0) :
    E.toMontgomery.B ^ 2 * toMontV (E.addCoords x₁ y₁ x₂ y₂).1 (E.addCoords x₁ y₁ x₂ y₂).2 =
      (E.toMontgomery.toWeierstrass).toAffine.addY (E.toMontgomery.B * toMontU y₁)
        (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₁ y₁)
        ((E.toMontgomery.toWeierstrass).toAffine.slope (E.toMontgomery.B * toMontU y₁)
          (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₁ y₁)
          (E.toMontgomery.B ^ 2 * toMontV x₂ y₂)) := by
  obtain ⟨hpos, hneg⟩ := E.denoms_ne_zero h1 h2
  have h1y : (1 : F) - y₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h1 hP))
  have h2y : (1 : F) - y₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h2 hQ))
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  have h4ne : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero MontgomeryCurve.two_ne_zero MontgomeryCurve.two_ne_zero
  have hBne : E.toMontgomery.B ≠ 0 := by
    have : E.toMontgomery.B = 4 / (E.a - E.d) := rfl
    rw [this]; exact div_ne_zero h4ne had
  have hU1m : toMontU (-1 : F) = 0 := by unfold toMontU; norm_num
  have hV1m : toMontV (0 : F) (-1) = 0 := by unfold toMontV; norm_num
  rw [WeierstrassCurve.Affine.slope_of_X_ne hUU]
  have hyne : y₁ ≠ y₂ := fun h => hUU (by rw [h])
  have hneg' : (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ ≠ 0 := by
    rw [show (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ = 1 - E.d * x₁ * x₂ * y₁ * y₂ from by ring]
    exact hneg
  have hslopeden : (1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂) ≠ 0 := by
    rw [show (1 + y₁) * (1 - y₂) - (1 - y₁) * (1 + y₂) = 2 * (y₁ - y₂) from by ring]
    exact mul_ne_zero MontgomeryCurve.two_ne_zero (sub_ne_zero.mpr hyne)
  have hsumnum : (1 : F) - E.d * y₁ * y₂ * x₁ * x₂ - (y₁ * y₂ - E.a * x₁ * x₂) ≠ 0 := by
    intro hh
    refine (E.y_ne_one (E.addCoords_onCurve h1 h2) (E.generic_sumNeId h1 h2 hinv)) ?_
    simp only [TwistedEdwardsCurve.addCoords]
    rw [div_eq_one_iff_eq (by rw [show (1 : F) - E.d * x₁ * x₂ * y₁ * y₂
      = 1 - E.d * y₁ * y₂ * x₁ * x₂ from by ring]; exact hneg')]
    linear_combination -hh
  by_cases hsX : x₁ * y₂ + y₁ * x₂ = 0
  · -- `sum = (0, -1)` via secant. Completeness forces `y₂ = -y₁`, then `sumX = 0 ⟹ x₂ = x₁`;
    -- with `P = (x₁,y₁)`, `Q = (x₁,-y₁)` the identity becomes a single-point `addX = addY = 0`.
    have hSX0 : (E.addCoords x₁ y₁ x₂ y₂).1 = 0 := by
      simp only [TwistedEdwardsCurve.addCoords]; rw [div_eq_zero_iff]; exact Or.inl hsX
    have hSY : (E.addCoords x₁ y₁ x₂ y₂).2 = -1 := by
      have hon := E.addCoords_onCurve h1 h2
      rw [TwistedEdwardsCurve.Equation, hSX0] at hon
      have hne1 : (E.addCoords x₁ y₁ x₂ y₂).2 ≠ 1 :=
        E.y_ne_one (E.addCoords_onCurve h1 h2) (E.generic_sumNeId h1 h2 hinv)
      rcases mul_eq_zero.mp (show ((E.addCoords x₁ y₁ x₂ y₂).2 - 1)
          * ((E.addCoords x₁ y₁ x₂ y₂).2 + 1) = 0 by linear_combination hon) with h | h
      · exact absurd (by linear_combination h) hne1
      · linear_combination h
    have gsY : y₁ * y₂ - E.a * x₁ * x₂ + 1 - E.d * x₁ * x₂ * y₁ * y₂ = 0 := by
      have ht := hSY; simp only [TwistedEdwardsCurve.addCoords] at ht
      rw [div_eq_iff hneg] at ht; linear_combination ht
    have hY2 : y₂ = -y₁ := by
      have hfac : (y₁ + y₂) * ((E.d * x₁ * x₂ * y₁ * y₂) ^ 2 - 1) = 0 := by
        rw [TwistedEdwardsCurve.Equation] at h1 h2
        exact E.cert_secant_negY h1 h2 hsX gsY
      rcases mul_eq_zero.mp hfac with h | h
      · linear_combination h
      · exact absurd (by linear_combination h) (E.lam_sq_ne_one h1 h2)
    subst hY2
    have hy1ne : y₁ ≠ 0 := fun h => hyne (by rw [h]; ring)
    have hx21 : x₂ = x₁ := by
      rcases mul_eq_zero.mp (show y₁ * (x₂ - x₁) = 0 by linear_combination hsX) with h | h
      · exact absurd h hy1ne
      · linear_combination h
    subst x₂
    have hAX0 : (E.toMontgomery.toWeierstrass).toAffine.addX (E.toMontgomery.B * toMontU y₁)
        (E.toMontgomery.B * toMontU (-y₁))
        ((E.toMontgomery.B ^ 2 * toMontV x₁ y₁ - E.toMontgomery.B ^ 2 * toMontV x₁ (-y₁)) /
          (E.toMontgomery.B * toMontU y₁ - E.toMontgomery.B * toMontU (-y₁))) = 0 := by
      have hC := E.generic_addX h1 h2 hP hQ hinv
      rw [hSY, hU1m, mul_zero, WeierstrassCurve.Affine.slope_of_X_ne hUU] at hC
      exact hC.symm
    rw [hSX0, show toMontV (0 : F) (E.addCoords x₁ y₁ x₁ (-y₁)).2 = 0 from by simp [toMontV],
      mul_zero]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY]
    rw [hAX0]
    simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
        WeierstrassCurve.Affine.negY,
      toMontU, toMontV, mul_zero, sub_zero]
    field_simp [hslopeden]
    ring
  · have hsumXnum : x₁ * y₂ + y₁ * x₂ ≠ 0 := hsX
    -- `sumX ≠ 0` (its numerator is `hsumXnum`, its denominator `1 + λ` is `hpos`).
    have hsX0 : (E.addCoords x₁ y₁ x₂ y₂).1 ≠ 0 := by
      simp only [TwistedEdwardsCurve.addCoords]; exact div_ne_zero hsumXnum hpos
    -- `generic_addX` (with the same secant slope) gives `B · toMontU sumY = addX`.
    have hC := E.generic_addX h1 h2 hP hQ hinv
    rw [WeierstrassCurve.Affine.slope_of_X_ne hUU] at hC
    -- Reshape the LHS: `B² · toMontV sumX sumY = B · (B · toMontU sumY) / sumX = B · addX / sumX`.
    rw [toMontV_eq_toMontU_div, mul_div_assoc', show E.toMontgomery.B ^ 2 = E.toMontgomery.B *
        E.toMontgomery.B from by ring,
      mul_assoc, hC]
    -- Now `B · addX / sumX = addY`; clear `sumX` (nonzero) → `B · addX = addY · sumX`.
    rw [div_eq_iff hsX0]
    simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
        WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      toMontU, toMontV, TwistedEdwardsCurve.addCoords]
    have hsX2 : y₂ * x₁ + y₁ * x₂ ≠ 0 := by
      rw [show y₂ * x₁ + y₁ * x₂ = x₁ * y₂ + y₁ * x₂ by ring]; exact hsumXnum
    have hpos' : (1 : F) + E.d * y₁ * x₁ * y₂ * x₂ ≠ 0 := by
      rw [show (1 : F) + E.d * y₁ * x₁ * y₂ * x₂ = 1 + E.d * x₁ * x₂ * y₁ * y₂ by ring]; exact hpos
    field_simp [hslopeden, hsumnum, hneg', hsumXnum, hsX2, hpos, hpos']
    rw [TwistedEdwardsCurve.Equation] at h1 h2
    exact E.cert_addY_secant h1 h2


/-- **Piece D** (Y-coordinate match): the TwistedEdwardsCurve sum's W-`y` equals Weierstrass
`addY`. -/
theorem generic_addY (E : TwistedEdwardsCurve F) {x₁ y₁ x₂ y₂ : F}
    (h1 : E.Equation x₁ y₁) (h2 : E.Equation x₂ y₂)
    (hP : ¬(x₁ = 0 ∧ y₁ = 1)) (hQ : ¬(x₂ = 0 ∧ y₂ = 1)) (hinv : ¬(x₂ = -x₁ ∧ y₂ = y₁)) :
    E.toMontgomery.B ^ 2 * toMontV (E.addCoords x₁ y₁ x₂ y₂).1 (E.addCoords x₁ y₁ x₂ y₂).2 =
      (E.toMontgomery.toWeierstrass).toAffine.addY (E.toMontgomery.B * toMontU y₁)
        (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₁ y₁)
        ((E.toMontgomery.toWeierstrass).toAffine.slope (E.toMontgomery.B * toMontU y₁)
          (E.toMontgomery.B * toMontU y₂) (E.toMontgomery.B ^ 2 * toMontV x₁ y₁)
          (E.toMontgomery.B ^ 2 * toMontV x₂ y₂)) := by
  obtain ⟨hpos, hneg⟩ := E.denoms_ne_zero h1 h2
  have h1y : (1 : F) - y₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h1 hP))
  have h2y : (1 : F) - y₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm (E.y_ne_one h2 hQ))
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  have h4ne : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero MontgomeryCurve.two_ne_zero MontgomeryCurve.two_ne_zero
  have hBne : E.toMontgomery.B ≠ 0 := by
    have : E.toMontgomery.B = 4 / (E.a - E.d) := rfl
    rw [this]; exact div_ne_zero h4ne had
  have hU1m : toMontU (-1 : F) = 0 := by unfold toMontU; norm_num
  have hV1m : toMontV (0 : F) (-1) = 0 := by unfold toMontV; norm_num
  by_cases hx1 : x₁ = 0
  · -- **2-torsion input** `P = (0, -1)`; sum `= (-x₂, -y₂)`, so `sumX = -x₂ ≠ 0`.
    subst hx1
    have hy1 : y₁ = -1 := by
      rw [TwistedEdwardsCurve.Equation] at h1
      rcases mul_eq_zero.mp (show (y₁ - 1) * (y₁ + 1) = 0 by linear_combination h1) with h | h
      · exact absurd (by linear_combination h : y₁ = 1) (fun hh => hP ⟨rfl, hh⟩)
      · linear_combination h
    subst hy1
    have hx2 : x₂ ≠ 0 := by
      intro h; subst h
      rcases mul_eq_zero.mp (show (y₂ - 1) * (y₂ + 1) = 0 by
        rw [TwistedEdwardsCurve.Equation] at h2; linear_combination h2) with h | h
      · exact hQ ⟨rfl, by linear_combination h⟩
      · exact hinv ⟨by ring, by linear_combination h⟩
    have hy2nm1 : y₂ ≠ -1 := by
      intro h; apply hx2
      rw [TwistedEdwardsCurve.Equation, h] at h2
      have : (E.a - E.d) * x₂ ^ 2 = 0 := by linear_combination h2
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have h1y2p : (1 : F) + y₂ ≠ 0 := fun h => hy2nm1 (by linear_combination h)
    have hU2ne : toMontU y₂ ≠ 0 := by
      unfold toMontU; rw [div_ne_zero_iff]
      exact ⟨fun h => hy2nm1 (by linear_combination h), h2y⟩
    have hUUne : E.toMontgomery.B * toMontU (-1 : F) ≠ E.toMontgomery.B * toMontU y₂ := by
      rw [hU1m, mul_zero]; exact fun h => (mul_ne_zero hBne hU2ne) h.symm
    rw [WeierstrassCurve.Affine.slope_of_X_ne hUUne, hU1m, hV1m]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, TwistedEdwardsCurve.toMontgomery,
      MontgomeryCurve.toWeierstrass, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, toMontU, toMontV,
      TwistedEdwardsCurve.addCoords]
    field_simp [h1y2p, hx2]
    rw [TwistedEdwardsCurve.Equation] at h2
    linear_combination (-4096 * x₂ * y₂ ^ 3 - 12288 * x₂ * y₂ ^ 2 - 12288 * x₂ * y₂ - 4096 * x₂) *
        h2
  by_cases hx2 : x₂ = 0
  · -- **2-torsion input** `Q = (0, -1)`; sum `= (-x₁, -y₁)`, so `sumX = -x₁ ≠ 0`.
    subst hx2
    have hy2 : y₂ = -1 := by
      rw [TwistedEdwardsCurve.Equation] at h2
      rcases mul_eq_zero.mp (show (y₂ - 1) * (y₂ + 1) = 0 by linear_combination h2) with h | h
      · exact absurd (by linear_combination h : y₂ = 1) (fun hh => hQ ⟨rfl, hh⟩)
      · linear_combination h
    subst hy2
    have hy1nm1 : y₁ ≠ -1 := by
      intro h; apply hx1
      rw [TwistedEdwardsCurve.Equation, h] at h1
      have : (E.a - E.d) * x₁ ^ 2 = 0 := by linear_combination h1
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have h1y1p : (1 : F) + y₁ ≠ 0 := fun h => hy1nm1 (by linear_combination h)
    have hU1ne : toMontU y₁ ≠ 0 := by
      unfold toMontU; rw [div_ne_zero_iff]
      exact ⟨fun h => hy1nm1 (by linear_combination h), h1y⟩
    have hUUne : E.toMontgomery.B * toMontU y₁ ≠ E.toMontgomery.B * toMontU (-1 : F) := by
      rw [hU1m, mul_zero]; exact mul_ne_zero hBne hU1ne
    rw [WeierstrassCurve.Affine.slope_of_X_ne hUUne, hU1m, hV1m]
    simp only [mul_zero, zero_mul, sub_zero, add_zero, TwistedEdwardsCurve.toMontgomery,
      MontgomeryCurve.toWeierstrass, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, toMontU, toMontV,
      TwistedEdwardsCurve.addCoords]
    field_simp [h1y1p, hx1]
    rw [TwistedEdwardsCurve.Equation] at h1
    linear_combination (-4) * h1
  by_cases hUU : E.toMontgomery.B * toMontU y₁ = E.toMontgomery.B * toMontU y₂
  · -- **Doubling** `P = Q`.
    have hVne : E.toMontgomery.B ^ 2 * toMontV x₁ y₁ ≠
        (E.toMontgomery.toWeierstrass).toAffine.negY (E.toMontgomery.B * toMontU y₂)
          (E.toMontgomery.B ^ 2 * toMontV x₂ y₂) :=
      fun hV => E.generic_notWInv h1 h2 hP hQ hinv ⟨hUU, hV⟩
    have hy : y₂ = y₁ := by
      have hUeq : toMontU y₁ = toMontU y₂ := mul_left_cancel₀ hBne hUU
      unfold toMontU at hUeq
      rw [div_eq_div_iff h1y h2y] at hUeq
      have h20 : (2 : F) * (y₂ - y₁) = 0 := by linear_combination -hUeq
      linear_combination (mul_eq_zero.mp h20).resolve_left MontgomeryCurve.two_ne_zero
    subst y₂
    have hy1nm1 : y₁ ≠ -1 := by
      intro h; refine hx1 ?_
      rw [TwistedEdwardsCurve.Equation, h] at h1
      have : (E.a - E.d) * x₁ ^ 2 = 0 := by linear_combination h1
      exact (pow_eq_zero_iff (by norm_num)).mp ((mul_eq_zero.mp this).resolve_left had)
    have ha1' : E.a - E.d * y₁ ^ 2 ≠ 0 := by
      intro h0
      rw [TwistedEdwardsCurve.Equation] at h1
      have e : (E.a - E.d * y₁ ^ 2) * x₁ ^ 2 = 1 - y₁ ^ 2 := by linear_combination h1
      rw [h0, zero_mul] at e
      rcases mul_eq_zero.mp (show (y₁ - 1) * (y₁ + 1) = 0 by linear_combination e) with h | h
      · exact (E.y_ne_one h1 hP) (by linear_combination h)
      · exact hy1nm1 (by linear_combination h)
    have hx : x₂ = x₁ := by
      rw [TwistedEdwardsCurve.Equation] at h1 h2
      have e : (E.a - E.d * y₁ ^ 2) * (x₁ ^ 2 - x₂ ^ 2) = 0 := by linear_combination h1 - h2
      have hsq : x₁ ^ 2 = x₂ ^ 2 := by linear_combination (mul_eq_zero.mp e).resolve_left ha1'
      rcases mul_eq_zero.mp (show (x₂ - x₁) * (x₂ + x₁) = 0 by linear_combination -hsq) with h | h
      · linear_combination h
      · exact absurd ⟨by linear_combination h, rfl⟩ hinv
    subst x₂
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hUU hVne]
    have hy1p : (1 : F) + y₁ ≠ 0 := fun h => hy1nm1 (by linear_combination h)
    have hnegD : (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 ≠ 0 := by
      rw [show (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 = 1 - E.d * x₁ * x₁ * y₁ * y₁ from by ring]
      exact hneg
    have h2c : (1 : F) - -1 ≠ 0 := by
      rw [show (1 : F) - -1 = 2 from by ring]; exact MontgomeryCurve.two_ne_zero
    by_cases hy10 : y₁ = 0
    · -- `2P = (0, -1)`: `sumX = 0`, so `toMontV(0,·)=0` and LHS `= 0`; show `addY = 0`.
      subst hy10
      have hsX0 : (E.addCoords x₁ (0 : F) x₁ 0).1 = 0 := by simp [TwistedEdwardsCurve.addCoords]
      rw [hsX0]
      simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
          WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
        toMontU, toMontV, TwistedEdwardsCurve.addCoords, mul_zero, zero_mul, sub_zero, add_zero,
            div_zero,
        zero_div]
      field_simp
      rw [TwistedEdwardsCurve.Equation] at h1
      linear_combination (512 * E.a ^ 2 * x₁ ^ 2 - 128 * E.a + 128 * E.d) * h1
    · -- `sumX = 2 x₁ y₁ / (1+λ) ≠ 0`.
      have hsumnumD : (1 : F) - E.d * y₁ ^ 2 * x₁ ^ 2 - (y₁ ^ 2 - E.a * x₁ ^ 2) ≠ 0 := by
        intro hh
        refine (E.y_ne_one (E.addCoords_onCurve h1 h2) (E.generic_sumNeId h1 h2 hinv)) ?_
        simp only [TwistedEdwardsCurve.addCoords]
        rw [div_eq_one_iff_eq (by rw [show (1 : F) - E.d * x₁ * x₁ * y₁ * y₁
          = 1 - E.d * y₁ ^ 2 * x₁ ^ 2 from by ring]; exact hnegD)]
        linear_combination -hh
      simp only [TwistedEdwardsCurve.toMontgomery, MontgomeryCurve.toWeierstrass,
          WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
        toMontU, toMontV, TwistedEdwardsCurve.addCoords, zero_mul, sub_zero, add_zero]
      have h11 : (1 : F) + 1 ≠ 0 := by
        rw [show (1 : F) + 1 = 2 by ring]; exact MontgomeryCurve.two_ne_zero
      field_simp [hy1p, hsumnumD, hnegD, h2c, hy10, h11]
      rw [TwistedEdwardsCurve.Equation] at h1
      exact E.cert_addY_double h1
  · exact E.generic_addY_secant h1 h2 hP hQ hinv hUU hx1 hx2


end TwistedEdwardsCurve
