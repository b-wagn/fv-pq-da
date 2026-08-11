/-
# Position-binding of the scheme

Position-binding of the erasure code commitment scheme reduces directly to
position-binding of the underlying vector commitment (Foundations of Data
Availability Sampling, eprint 2023/1079, Lemma 13). The reduction receives a
vector-commitment key, samples the argument system's crs itself, simulates the
random-oracle world for the adversary, and forwards the adversary's output
with the proof component stripped: the scheme's verification is the argument
verification *and* the vector-commitment verification, so any pair of openings
breaking position-binding of the scheme in particular breaks position-binding
of the vector commitment.
-/
import PqDas.Target.Scheme

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- Reduction (an explicit PPT algorithm): a position-binding adversary
against the scheme becomes one against the vector commitment. It samples the
crs itself, simulates the random oracle lazily, and strips the proof from the
commitment. -/
noncomputable def posBindingReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.PosBindingAdv Λ n CkVC ComVC Opn := fun ckVC => do
  let crs ← ps.setup
  let (com, i, x, τ, x', τ') ← simulateRom (A (ckVC, crs))
  return (com.1, i, x, τ, x', τ')

/-- **Position-binding of the scheme**, by reduction to position-binding of
the vector commitment via `posBindingReduction`. -/
theorem scheme_positionBinding [DecidableEq Λ] [DecidableEq ComVC] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Pr[= true | (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
        C vc chk ps).posBindingExp (roRuntime ComVC L) A] ≤
      Pr[= true | vc.posBindingExp (posBindingReduction ps A)] := by
  sorry

end PqDas
