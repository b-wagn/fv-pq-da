/-
# Generalizations of VCVio's fork lemmas (upstream candidates)

Lemmas that belong upstream in VCVio: the focused-answer collision bound of
`OracleComp/Constructions/Fork.lean` generalized from the collision predicate
(`ans₁ = ans₂`, bounded by `1/|Range|`) to an arbitrary predicate on the first
completion's output and the second completion's focused answer, bounded by any
pointwise bound `δ` on the predicate against a fresh uniform query. The proof
is the same three steps: rewrite the fork as a second completion, drop the
guard, and apply `probEvent_answer_ofFreeM_complete` (which is already fully
general in the predicate).
-/
import VCVio.CryptoFoundations.ReplayFork

open OracleSpec ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The second focused answer of a located fork satisfies a predicate
parameterized by the (fixed) first output with probability at most any bound
`δ` that holds for the predicate against one fresh uniform query. Any
additional guard on the first output only tightens the event.

Generalizes `probEvent_focusCollision_ofFreeM_fork_le` (recovered with
`Q x a := (firstAnswer = a)` and `δ := (Fintype.card (spec.Range i))⁻¹`). -/
theorem probEvent_focusPredicate_ofFreeM_fork_le [spec.DecidableEq] [IsUniformSpec spec]
    {main : OracleComp spec α} {i : ι} {n : Nat} {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop)
    (Q : α → spec.Range i → Prop) {δ : ℝ≥0∞}
    (hQ : ∀ x : α, Pr[fun ans => Q x ans | (query i : OracleComp spec (spec.Range i))] ≤ δ) :
    Pr[fun view => Q (PFunctor.FreeM.output main view.firstPath) view.secondAnswer ∧
        accept (PFunctor.FreeM.output main view.firstPath) |
          OracleComp.ofFreeM located.fork] ≤ δ := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, probEvent_ofFreeM_map]
  exact (probEvent_mono fun completion _ h => h.1).trans <|
    (probEvent_answer_ofFreeM_complete located.occurrence
      (fun a => Q (PFunctor.FreeM.output main located.completion.path) a)).trans_le
      (hQ _)

end OracleComp
