import FEC.Montgomery.Equiv
import FEC.Framework

/-!
# Montgomery point group (transported)

The Montgomery point group is obtained by transporting Mathlib's Weierstrass group along the
canonical `pointEquiv`. NO group axioms are re-proved — this is the transfer theorem in action.
-/

namespace FEC

open WeierstrassCurve

variable {p : ℕ} [Fact p.Prime] [Fact (2 < p)]

/-- The Montgomery point group, transported from Weierstrass via `pointEquiv`. -/
noncomputable instance (M : Montgomery (𝔽 p)) : AddCommGroup M.Point :=
  M.pointEquiv.addCommGroup

-- Architectural stress test: the full pipeline composes and the group instance resolves.
noncomputable example (M : Montgomery (𝔽 p)) : AddCommGroup M.Point := inferInstance

end FEC
