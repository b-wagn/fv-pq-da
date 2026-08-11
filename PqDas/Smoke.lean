/-
Phase 0 smoke test: confirm that VCVio imports work from this package and that
the core idioms we rely on (`ProbComp`, uniform sampling `$ᵗ`, probability
notation `Pr[= _ | _]`, and the commitment binding experiment) elaborate.
This file is deleted once Phase 1 starts.
-/
import VCVio.CryptoFoundations.CommitmentScheme

open OracleComp ENNReal

namespace PqDas.Smoke

variable {PP M C D : Type} [DecidableEq M]

/-- Monadic probabilistic computations and uniform sampling elaborate. -/
def coinFlip : ProbComp Bool := do
  let b ← $ᵗ Bool
  return b

/-- VCVio's binding experiment and the probability notation elaborate. -/
noncomputable def smokeBindingAdvantage (cs : CommitmentScheme PP M C D)
    (A : CommitmentScheme.BindingAdv PP M C D) : ℝ≥0∞ :=
  Pr[= true | cs.bindingExp A]

end PqDas.Smoke
