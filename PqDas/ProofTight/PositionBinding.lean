/-
# Position-binding of the tight scheme

Position-binding of the tight scheme reduces directly to position-binding of
the underlying vector commitment, exactly as for the original scheme
(`Proof/PositionBinding.lean`). The reduction receives a vector-commitment key,
samples both reference strings itself, simulates the random-oracle world for
the adversary, and forwards the adversary's output with the two proofs
stripped.
-/
import PqDas.Target.TightScheme

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs₀ Proof₀ Crs₁ Proof₁ : Type}

/-- Reduction (an explicit PPT algorithm): a position-binding adversary
against the tight scheme becomes one against the vector commitment. It samples
both reference strings itself, simulates the random oracle lazily, and strips
the proofs from the commitment. -/
noncomputable def tightPosBindingReduction [DecidableEq ComVC] [DecidableEq Proof₀]
    [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    VectorCommitment.PosBindingAdv Λ n CkVC ComVC Opn := fun ckVC => do
  let crs₀ ← ps₀.setup
  let crs₁ ← ps₁.setup
  let (com, i, x, τ, x', τ') ← simulateRom (A (ckVC, crs₀, crs₁))
  return (com.1, i, x, τ, x', τ')

/-- **Position-binding of the tight scheme**, by reduction to position-binding
of the vector commitment via `tightPosBindingReduction`. -/
theorem tightScheme_positionBinding [DecidableEq Λ] [DecidableEq ComVC]
    [DecidableEq Proof₀] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    Pr[= true | (tightScheme (m := OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
        C vc chk ps₀ ps₁).posBindingExp (roRuntime (ComVC × Proof₀) L) A] ≤
      Pr[= true | vc.posBindingExp (tightPosBindingReduction ps₀ ps₁ A)] := by
  unfold ErasureCodeCommitment.posBindingExp VectorCommitment.posBindingExp
    tightPosBindingReduction
  rw [← evalDist_simulateRom, probOutput_evalDist]
  dsimp only [tightScheme]
  simp only [monad_norm, simulateRom]
  -- Peel the three lifted setup samplings on both sides.
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun ckVC _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun crs₀ _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun crs₁ _ => ?_
  -- Split off the adversary's simulated run on both sides: the game threads
  -- the adversary's final oracle cache into verification, the reduction
  -- discards it.
  rw [simulateRomWithCache_bind, bind_simulateRomWithCache]
  refine probOutput_bind_mono fun out _ => ?_
  obtain ⟨⟨com, i, x, τ, x', τ'⟩, cache⟩ := out
  -- Evaluate the two verification queries; their answers are irrelevant to
  -- the vector-commitment part of the win condition.
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
