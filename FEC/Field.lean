import Mathlib

/-!
# The base finite field `𝔽 p`

The target field for the whole development is the finite field `𝔽 p = ZMod p` for a prime `p`.
Per the project's "relative over a ring `R`, group over fields" decision, most *definitions* are
stated over an arbitrary `[CommRing R]`; the *point group* specializes to `𝔽 p` (a field).
-/


/-- The finite field `𝔽 p = ZMod p` for a prime `p`. -/
abbrev 𝔽 (p : ℕ) [Fact p.Prime] := ZMod p

-- Sanity: the field / decidability instances resolve under `[Fact p.Prime]`.
example (p : ℕ) [Fact p.Prime] : Field (𝔽 p) := inferInstance
example (p : ℕ) [Fact p.Prime] : DecidableEq (𝔽 p) := inferInstance

