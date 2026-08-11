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
  unfold ErasureCodeCommitment.posBindingExp VectorCommitment.posBindingExp
    posBindingReduction
  rw [← evalDist_simulateRom, probOutput_evalDist]
  dsimp only [scheme]
  simp only [monad_norm, simulateRom]
  -- Peel the two lifted setup samplings on both sides.
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun ckVC _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun crs _ => ?_
  -- Split off the adversary's simulated run on both sides: the game threads
  -- the adversary's final oracle cache into verification, the reduction
  -- discards it.
  rw [simulateRomWithCache_bind, bind_simulateRomWithCache]
  refine probOutput_bind_mono fun out _ => ?_
  obtain ⟨⟨com, i, x, τ, x', τ'⟩, cache⟩ := out
  -- Evaluate the two verification queries; their answers `l`, `l'` are
  -- irrelevant to the vector-commitment part of the win condition.
  simp only [monad_norm, simulateRomWithCache_query_bind, simulateRomWithCache_pure]
  by_cases hwin : (decide (x ≠ x') && vc.verify ckVC com.1 i x τ
      && vc.verify ckVC com.1 i x' τ') = true
  · exact hwin ▸ le_of_le_of_eq probOutput_le_one (probOutput_pure_self _).symm
  · refine le_trans (le_of_eq (probOutput_eq_zero_of_not_mem_support ?_)) zero_le
    intro hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨y, _, hmem⟩ := hmem
    rw [mem_support_bind_iff] at hmem
    obtain ⟨y', _, hmem⟩ := hmem
    simp only [support_pure, Set.mem_singleton_iff] at hmem
    grind

end PqDas
