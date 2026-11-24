/-
# Code-binding of the tight scheme

Code-binding of the tight scheme (`Target/TightScheme.lean`), without
rewinding. The bound is a plain sum:

  `Pr[code-binding] ≤ ε_ks₀ + ε_ks₁ + ε_coll + ε_wpb + (Q + 1) * δ`

where `ε_ks₀`, `ε_ks₁` are knowledge-soundness advantages against the two
argument systems, `ε_coll` and `ε_wpb` are a commit-collision and a weak
position-binding advantage against the vector commitment, `Q` bounds the
adversary's random-oracle queries, and `δ` is the soundness of the code
checker. Compare `Proof/CorollaryCodeBinding.lean`, where the collision
advantage and `δ` appear under a square root and multiplied by `Q`.

Given a code-binding adversary, run it and let `(comVC, π₀, π₁)` be the
commitment it outputs, `l = H(comVC, π₀)` the check randomness, `c₀` the vector
extracted from `π₀` and `c₁` the vector extracted from `π₁`. Decompose the
winning event:

* if `π₀` verifies but `c₀` does not commit to `comVC`, the run breaks
  knowledge soundness of the first argument system (`tightKs₀Reduction`);
* otherwise, if `c₀` is a codeword, then since no codeword is consistent with
  the adversary's opened symbols, some opening disagrees with `c₀` while
  verifying against `comVC = vc.commit ckVC c₀`: this breaks weak
  position-binding (`tightWpbReduction`);
* otherwise `c₀` is not a codeword. If `π₁` verifies but `c₁` does not satisfy
  the relation, the run breaks knowledge soundness of the second argument
  system (`tightKs₁Reduction`);
* otherwise `c₁` commits to `comVC` and passes the code check on `l`. If
  `c₀ ≠ c₁`, the two vectors are a collision for the deterministic commit
  (`tightCollReduction`): a straight-line reduction, with no rewinding;
* otherwise `c₀ = c₁`, so the non-codeword `c₀` passes the code check on
  `l = H(comVC, π₀)`. But for fixed keys `c₀` is a function of the oracle input
  `(comVC, π₀)`, so it was fixed before `l` was sampled; by soundness of the code checker and
  a union bound over the oracle queries this has probability at most
  `(Q + 1) * δ` (`SparseRelation.probOutput_challenge_le`).

The first four cases are handled by explicit reductions that reproduce the
code-binding experiment's distribution; the last case is bounded directly.
-/
import PqDas.Target.TightScheme
import PqDas.ProofTight.SparseRelation

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace PqDas

open CommittedSoundness (HashQueryBound)

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs₀ Proof₀ Crs₁ Proof₁ : Type}

/-- The adversary's continuation shared by the reductions below: run the
code-binding adversary, then query the oracle once more on the pair
(commitment, first proof) it output (a cache hit if the adversary already
queried it), obtaining the check randomness that verification would use. -/
def tightRunWithChallenge
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn)
    (ck : CkVC × Crs₀ × Crs₁) :
    OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L))
      (((ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) × L) := do
  let out ← A ck
  let l ← HasQuery.query (spec := ((ComVC × Proof₀) →ₒ L)) (out.1.1, out.1.2.1)
  return (out, l)

/-- Reduction to knowledge soundness of the first argument system (an explicit
PPT algorithm): sample the vector-commitment key and the second reference
string, simulate the random-oracle world for the code-binding adversary, and
output the statement `(ckVC, comVC)` together with the adversary's first
proof. -/
noncomputable def tightKs₀Reduction [DecidableEq ComVC] [DecidableEq Proof₀]
    [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn) {chk : CodeChecker Λ n L}
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC) Crs₀ Proof₀ := fun crs₀ => do
  let ckVC ← vc.setup
  let crs₁ ← ps₁.setup
  let (com, _) ← simulateRom (A (ckVC, crs₀, crs₁))
  return ((ckVC, com.1), com.2.1)

/-- Reduction to knowledge soundness of the second argument system (an
explicit PPT algorithm): sample the vector-commitment key and the first
reference string, simulate the random-oracle world for the code-binding
adversary, and output the statement `(ckVC, comVC, l)` together with the
adversary's second proof. -/
noncomputable def tightKs₁Reduction [DecidableEq ComVC] [DecidableEq Proof₀]
    [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC × L) Crs₁ Proof₁ := fun crs₁ => do
  let ckVC ← vc.setup
  let crs₀ ← ps₀.setup
  let ((com, _), l) ← simulateRom (tightRunWithChallenge A (ckVC, crs₀, crs₁))
  return ((ckVC, com.1, l), com.2.2)

/-- Reduction to collision resistance of the vector commitment's `commit` (an
explicit algorithm *without rewinding*, efficient if both extractors are):
sample both reference strings, simulate the random-oracle world for the
code-binding adversary, and output the two vectors extracted from its two
proofs. -/
noncomputable def tightCollReduction [DecidableEq ComVC] [DecidableEq Proof₀]
    [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (ext₀ : Nark.Extractor (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀)
    (ext₁ : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁)
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    VectorCommitment.CollisionAdv Λ n CkVC := fun ckVC => do
  let crs₀ ← ps₀.setup
  let crs₁ ← ps₁.setup
  let ((com, _), l) ← simulateRom (tightRunWithChallenge A (ckVC, crs₀, crs₁))
  return (ext₀ crs₀ (ckVC, com.1) com.2.1, ext₁ crs₁ (ckVC, com.1, l) com.2.2)

/-- Reduction to weak position-binding (an explicit algorithm, efficient if the
first extractor is): sample both reference strings, simulate the random-oracle world for the code-binding
adversary, extract the vector `c₀` from its first proof, and search its
openings for one whose symbol disagrees with `c₀`. If none disagrees the
reduction has lost anyway and outputs a dummy tuple. -/
noncomputable def tightWpbReduction [NeZero n] [DecidableEq Λ] [DecidableEq ComVC]
    [DecidableEq Proof₀] [SampleableType L] [Inhabited Opn]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (ext₀ : Nark.Extractor (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀)
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) :
    VectorCommitment.WeakPosBindingAdv Λ n CkVC Opn := fun ckVC => do
  let crs₀ ← ps₀.setup
  let crs₁ ← ps₁.setup
  let (com, openings) ← simulateRom (A (ckVC, crs₀, crs₁))
  let c := ext₀ crs₀ (ckVC, com.1) com.2.1
  match openings.find? (fun p => decide (p.2.1 ≠ c p.1)) with
  | some p => return (c, p.1, p.2.1, p.2.2)
  | none => return (c, 0, c 0, default)

/-! ### Proof of code-binding

As in `Proof/CodeBinding.lean`, all experiments are aligned on a shared
prefix: sample the three keys, run the adversary in the simulated
random-oracle world, and query the oracle once on the pair (commitment, first
proof) it output (`challengedRun`). Each experiment's winning condition is a
deterministic Boolean function of the prefix outcome, the game's bit implies
one of five bits (`gameWinBit_implies`), and a pointwise union bound over the
shared prefix concludes. Four of the five bits are winning bits of explicit
reductions; the fifth is bounded by `(Q + 1) * δ`. -/

section codeBindingProof

set_option linter.unusedSectionVars false

/-- Union bound over a shared prefix, for five alternatives. -/
private lemma probOutput_bind_le_add₅ {α : Type} (oa : ProbComp α)
    (f g₁ g₂ g₃ g₄ g₅ : α → ProbComp Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] ≤
        Pr[= true | g₁ x] + Pr[= true | g₂ x] + Pr[= true | g₃ x] +
          Pr[= true | g₄ x] + Pr[= true | g₅ x]) :
    Pr[= true | oa >>= f] ≤
      Pr[= true | oa >>= g₁] + Pr[= true | oa >>= g₂] + Pr[= true | oa >>= g₃] +
        Pr[= true | oa >>= g₄] + Pr[= true | oa >>= g₅] := by
  simp only [probOutput_bind_eq_tsum]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support oa
  · rw [← mul_add, ← mul_add, ← mul_add, ← mul_add]
    exact mul_le_mul_right (h x hx) _
  · simp [probOutput_eq_zero_of_not_mem_support hx]

/-- Five-way Boolean union bound for `pure` computations. -/
private lemma probOutput_pure_bool_le_or₅ (win b₁ b₂ b₃ b₄ b₅ : Bool)
    (h : win = true → b₁ = true ∨ b₂ = true ∨ b₃ = true ∨ b₄ = true ∨ b₅ = true) :
    Pr[= true | (pure win : ProbComp Bool)] ≤
      Pr[= true | (pure b₁ : ProbComp Bool)] + Pr[= true | (pure b₂ : ProbComp Bool)] +
        Pr[= true | (pure b₃ : ProbComp Bool)] + Pr[= true | (pure b₄ : ProbComp Bool)] +
          Pr[= true | (pure b₅ : ProbComp Bool)] := by
  cases win <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> cases b₅ <;> simp_all

/-- Simulating a `mapM` whose every step queries the oracle at the same point
`q`, starting from a cache that already answers `q` with `l`: every query is a
cache hit, so the verdicts are computed by a plain `map` at answer `l` and the
cache is unchanged. (Copy of the private lemma of `Proof/CodeBinding.lean`.) -/
private lemma simulateRomWithCache_mapM_query_hit {X : Type} [DecidableEq X]
    [SampleableType L] {α β : Type} {q : X} {cache : (X →ₒ L).QueryCache} {l : L}
    (h : cache q = some l) (g : α → L → Bool) (xs : List α)
    (k : List Bool → OracleComp (unifSpec + (X →ₒ L)) β) :
    simulateRomWithCache cache
        (xs.mapM (fun p => HasQuery.query (spec := (X →ₒ L)) q >>=
          fun l' => pure (g p l')) >>= k) =
      simulateRomWithCache cache (k (xs.map fun p => g p l)) := by
  induction xs generalizing k with
  | nil => rw [List.mapM_nil, pure_bind, List.map_nil]
  | cons p ps ih =>
      rw [List.mapM_cons, List.map_cons]
      simp only [bind_assoc, pure_bind]
      rw [simulateRomWithCache_query_bind, randomOracle_run_hit h, pure_bind]
      exact ih _

variable [Nonempty Γ] [Fintype Γ] [DecidableEq Λ] [DecidableEq ComVC]
  [DecidableEq Proof₀] [SampleableType L] [NeZero n] [Inhabited Opn]
  (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L)
  (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
  (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
  (ext₀ : Nark.Extractor (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀)
  (ext₁ : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁)
  (A : ErasureCodeCommitment.CodeBindingAdv
    (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
    Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn)

/-- The prefix shared by all experiments, with the challenge query appended:
sample the three keys, run the adversary in the simulated random-oracle world,
then query the oracle once on the pair (commitment, first proof) of its output
(a cache hit if the adversary already queried it). -/
private noncomputable def challengedRun :
    ProbComp (CkVC × Crs₀ × Crs₁ ×
      ((ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) × L) := do
  let ckVC ← vc.setup
  let crs₀ ← ps₀.setup
  let crs₁ ← ps₁.setup
  let z ← (simulateQ (romImpl (ComVC × Proof₀) L) (A (ckVC, crs₀, crs₁))).run ∅
  let x ← ((randomOracle : QueryImpl ((ComVC × Proof₀) →ₒ L)
      (StateT (((ComVC × Proof₀) →ₒ L).QueryCache) ProbComp))
        (z.1.1.1, z.1.1.2.1)).run z.2
  return (ckVC, crs₀, crs₁, z.1, x.1)

/-- The code-binding game's winning bit as a function of the shared prefix
outcome: all openings verify (each verification's oracle query returns the
pinned challenge) and no codeword is consistent with the opened symbols. -/
private def gameWinBit (ckVC : CkVC) (crs₀ : Crs₀) (crs₁ : Crs₁)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  ((out.2.map fun p => ps₀.verify crs₀ (ckVC, out.1.1) out.1.2.1 &&
      ps₁.verify crs₁ (ckVC, out.1.1, l) out.1.2.2 &&
      vc.verify ckVC out.1.1 p.1 p.2.1 p.2.2).all id) &&
    !decide (C.Consistent (out.2.map fun p => (p.1, p.2.1)))

/-- Winning bit of the first knowledge-soundness reduction. -/
private def ks₀WinBit (ckVC : CkVC) (crs₀ : Crs₀)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) : Bool :=
  ps₀.verify crs₀ (ckVC, out.1.1) out.1.2.1 &&
    !commitRel vc (ckVC, out.1.1) (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1)

/-- Winning bit of the second knowledge-soundness reduction. -/
private def ks₁WinBit (ckVC : CkVC) (crs₁ : Crs₁)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  ps₁.verify crs₁ (ckVC, out.1.1, l) out.1.2.2 &&
    !schemeRel vc chk (ckVC, out.1.1, l) (ext₁ crs₁ (ckVC, out.1.1, l) out.1.2.2)

/-- Winning bit of the collision reduction: the two extracted vectors differ
but have the same commitment. -/
private def collWinBit (ckVC : CkVC) (crs₀ : Crs₀) (crs₁ : Crs₁)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  decide (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 ≠
      ext₁ crs₁ (ckVC, out.1.1, l) out.1.2.2) &&
    decide (vc.commit ckVC (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1) =
      vc.commit ckVC (ext₁ crs₁ (ckVC, out.1.1, l) out.1.2.2))

/-- Winning bit of the weak position-binding reduction. -/
private def wpbWinBit (ckVC : CkVC) (crs₀ : Crs₀)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) : Bool :=
  match out.2.find? fun p =>
      decide (p.2.1 ≠ ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 p.1) with
  | some p => decide (p.2.1 ≠ ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 p.1) &&
      vc.verify ckVC (vc.commit ckVC (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1))
        p.1 p.2.1 p.2.2
  | none => decide (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 0 ≠
        ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 0) &&
      vc.verify ckVC (vc.commit ckVC (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1)) 0
        (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 0) default

/-- The remaining bad event: the vector extracted from the first proof is a
non-codeword that passes the code check on the challenge. No reduction is
attached to this bit; its probability is bounded directly. -/
private def chkWinBit (ckVC : CkVC) (crs₀ : Crs₀)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) (l : L) : Bool :=
  decide (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1 ∉ C.code) &&
    chk.check l (ext₀ crs₀ (ckVC, out.1.1) out.1.2.1)

/-- Pointwise event decomposition: whenever the game's winning bit is set, one
of the five bits is set (see the file header for the case analysis). -/
private lemma gameWinBit_implies (ckVC : CkVC) (crs₀ : Crs₀) (crs₁ : Crs₁)
    (out : (ComVC × Proof₀ × Proof₁) × List (Fin n × Λ × Opn)) (l : L)
    (h : gameWinBit C vc chk ps₀ ps₁ ckVC crs₀ crs₁ out l = true) :
    ks₀WinBit vc ps₀ ext₀ ckVC crs₀ out = true ∨
      ks₁WinBit vc chk ps₁ ext₁ ckVC crs₁ out l = true ∨
      collWinBit vc ext₀ ext₁ ckVC crs₀ crs₁ out l = true ∨
      wpbWinBit vc ext₀ ckVC crs₀ out = true ∨
      chkWinBit C chk ext₀ ckVC crs₀ out l = true := by
  obtain ⟨⟨comVC, π₀, π₁⟩, openings⟩ := out
  simp only [gameWinBit, Bool.and_eq_true, List.all_eq_true, List.mem_map,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨hall, hncons⟩ := h
  have hver : ∀ p ∈ openings, ps₀.verify crs₀ (ckVC, comVC) π₀ = true ∧
      ps₁.verify crs₁ (ckVC, comVC, l) π₁ = true ∧
      vc.verify ckVC comVC p.1 p.2.1 p.2.2 = true := by
    intro p hp
    have := hall _ ⟨p, hp, rfl⟩
    simpa [Bool.and_eq_true, and_assoc] using this
  have hne : openings ≠ [] := by
    rintro rfl
    exact hncons ⟨Classical.arbitrary _, by simp⟩
  obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil openings hne
  have hps₀ : ps₀.verify crs₀ (ckVC, comVC) π₀ = true := (hver p₀ hp₀).1
  have hps₁ : ps₁.verify crs₁ (ckVC, comVC, l) π₁ = true := (hver p₀ hp₀).2.1
  cases hrel₀ : commitRel vc (ckVC, comVC) (ext₀ crs₀ (ckVC, comVC) π₀) with
  | false => exact Or.inl (by simp [ks₀WinBit, hps₀, hrel₀])
  | true =>
      have hcommit₀ : vc.commit ckVC (ext₀ crs₀ (ckVC, comVC) π₀) = comVC := by
        simpa [commitRel] using hrel₀
      by_cases hcode : ext₀ crs₀ (ckVC, comVC) π₀ ∈ C.code
      · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        have hbad : ∃ p ∈ openings, p.2.1 ≠ ext₀ crs₀ (ckVC, comVC) π₀ p.1 := by
          by_contra hno
          push Not at hno
          obtain ⟨m, hm⟩ := hcode
          refine hncons ⟨m, fun pr hpr => ?_⟩
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpr
          rw [hm]
          exact (hno p hp).symm
        have hfind : (openings.find? fun p =>
            decide (p.2.1 ≠ ext₀ crs₀ (ckVC, comVC) π₀ p.1)).isSome := by
          rw [List.find?_isSome]
          obtain ⟨p, hp, hne'⟩ := hbad
          exact ⟨p, hp, decide_eq_true hne'⟩
        obtain ⟨p₁, hfind⟩ := Option.isSome_iff_exists.mp hfind
        have hpred := List.find?_some hfind
        have hv : vc.verify ckVC comVC p₁.1 p₁.2.1 p₁.2.2 = true :=
          (hver p₁ (List.mem_of_find?_eq_some hfind)).2.2
        simp only [wpbWinBit, hfind]
        rw [hcommit₀]
        simp [hpred, hv]
      · cases hrel₁ : schemeRel vc chk (ckVC, comVC, l)
            (ext₁ crs₁ (ckVC, comVC, l) π₁) with
        | false => exact Or.inr (Or.inl (by simp [ks₁WinBit, hps₁, hrel₁]))
        | true =>
            rw [schemeRel, Bool.and_eq_true, decide_eq_true_eq] at hrel₁
            obtain ⟨hcommit₁, hchk₁⟩ := hrel₁
            by_cases heq : ext₀ crs₀ (ckVC, comVC) π₀ = ext₁ crs₁ (ckVC, comVC, l) π₁
            · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
              have hchk₀ : chk.check l (ext₀ crs₀ (ckVC, comVC) π₀) = true := by
                rw [heq]
                exact hchk₁
              simp [chkWinBit, hcode, hchk₀]
            · refine Or.inr (Or.inr (Or.inl ?_))
              have hcc : vc.commit ckVC (ext₀ crs₀ (ckVC, comVC) π₀) =
                  vc.commit ckVC (ext₁ crs₁ (ckVC, comVC, l) π₁) :=
                hcommit₀.trans hcommit₁.symm
              simp [collWinBit, heq, hcc]

/-- Alignment of the code-binding game with the challenged shared prefix. If
the adversary opens nothing the game cannot win (the empty list is
consistent); otherwise the game's first verification query is the challenge
query, and all further verification queries are cache hits. -/
private lemma game_le_challengedRun :
    Pr[= true | (tightScheme (m := OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
        C vc chk ps₀ ps₁).codeBindingExp C (roRuntime (ComVC × Proof₀) L) A] ≤
      Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (gameWinBit C vc chk ps₀ ps₁ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] := by
  unfold ErasureCodeCommitment.codeBindingExp challengedRun
  rw [← evalDist_simulateRom, probOutput_evalDist]
  dsimp only [tightScheme]
  simp only [monad_norm, simulateRom]
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun ckVC _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun crs₀ _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine probOutput_bind_mono fun crs₁ _ => ?_
  rw [simulateRomWithCache_bind]
  refine probOutput_bind_mono fun z _ => ?_
  obtain ⟨⟨⟨comVC, π₀, π₁⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rcases openings with _ | ⟨p₀, rest⟩
  · have hcons : C.Consistent [] := ⟨Classical.arbitrary _, by simp⟩
    refine le_trans (le_of_eq ?_) zero_le
    simp [hcons]
  · cases hc : cache₁ (comVC, π₀) with
    | some l₀ =>
        rw [randomOracle_run_hit hc, pure_bind]
        rw [simulateRomWithCache_mapM_query_hit hc, simulateRomWithCache_pure]
        simp [gameWinBit]
    | none =>
        rw [List.mapM_cons]
        simp only [bind_assoc, pure_bind]
        rw [simulateRomWithCache_query_bind, randomOracle_run_miss hc]
        simp only [bind_assoc, pure_bind]
        refine probOutput_bind_mono fun r _ => ?_
        rw [simulateRomWithCache_mapM_query_hit
            (QueryCache.cacheQuery_self cache₁ (comVC, π₀) r),
          simulateRomWithCache_pure]
        simp [gameWinBit]

/-- Alignment of the first knowledge-soundness experiment with the challenged
shared prefix. The reduction does not need the challenge, so the prefix's
challenge query is simply dropped. -/
private lemma challengedRun_ks₀_le :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (ks₀WinBit vc ps₀ ext₀ w.1 w.2.1 w.2.2.2.1)] ≤
      Pr[= true | ps₀.knowledgeSoundnessExp ext₀ (tightKs₀Reduction vc ps₁ A)] := by
  unfold challengedRun Nark.knowledgeSoundnessExp tightKs₀Reduction
  simp only [monad_norm, simulateRom]
  refine le_trans (le_of_eq (probOutput_bind_bind_swap vc.setup ps₀.setup _ true)) ?_
  refine probOutput_bind_mono fun crs₀ _ => ?_
  refine probOutput_bind_mono fun ckVC _ => ?_
  refine probOutput_bind_mono fun crs₁ _ => ?_
  rw [bind_simulateRomWithCache]
  refine probOutput_bind_mono fun z _ => ?_
  obtain ⟨⟨⟨comVC, π₀, π₁⟩, openings⟩, cache₁⟩ := z
  rw [probOutput_bind_const]
  refine le_trans (mul_le_of_le_one_left zero_le tsub_le_self) ?_
  simp [ks₀WinBit]

/-- Alignment of the second knowledge-soundness experiment with the challenged
shared prefix (after commuting the key samplings). -/
private lemma challengedRun_ks₁_le :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (ks₁WinBit vc chk ps₁ ext₁ w.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] ≤
      Pr[= true | ps₁.knowledgeSoundnessExp ext₁ (tightKs₁Reduction vc ps₀ A)] := by
  unfold challengedRun Nark.knowledgeSoundnessExp tightKs₁Reduction tightRunWithChallenge
  simp only [monad_norm, simulateRom]
  refine le_trans (le_of_eq (probOutput_bind_congr fun ckVC _ =>
    probOutput_bind_bind_swap ps₀.setup ps₁.setup _ true)) ?_
  refine le_trans (le_of_eq (probOutput_bind_bind_swap vc.setup ps₁.setup _ true)) ?_
  refine probOutput_bind_mono fun crs₁ _ => ?_
  refine probOutput_bind_mono fun ckVC _ => ?_
  refine probOutput_bind_mono fun crs₀ _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine probOutput_bind_mono fun z _ => ?_
  obtain ⟨⟨⟨comVC, π₀, π₁⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rw [simulateRomWithCache_query_bind]
  simp only [simulateRomWithCache_pure, bind_assoc, pure_bind]
  refine probOutput_bind_mono fun x _ => ?_
  simp [ks₁WinBit]

/-- Alignment of the collision experiment with the challenged shared prefix. -/
private lemma challengedRun_coll_le :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (collWinBit vc ext₀ ext₁ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] ≤
      Pr[= true | vc.collisionExp (tightCollReduction ps₀ ps₁ ext₀ ext₁ A)] := by
  unfold challengedRun VectorCommitment.collisionExp tightCollReduction
    tightRunWithChallenge
  simp only [monad_norm, simulateRom]
  refine probOutput_bind_mono fun ckVC _ => ?_
  refine probOutput_bind_mono fun crs₀ _ => ?_
  refine probOutput_bind_mono fun crs₁ _ => ?_
  rw [simulateRomWithCache_bind]
  simp only [bind_assoc]
  refine probOutput_bind_mono fun z _ => ?_
  obtain ⟨⟨⟨comVC, π₀, π₁⟩, openings⟩, cache₁⟩ := z
  simp only [monad_norm]
  rw [simulateRomWithCache_query_bind]
  simp only [simulateRomWithCache_pure, bind_assoc, pure_bind]
  refine probOutput_bind_mono fun x _ => ?_
  simp [collWinBit]

/-- Alignment of the weak position-binding experiment with the challenged
shared prefix. The reduction does not need the challenge, so the prefix's
challenge query is simply dropped. -/
private lemma challengedRun_wpb_le :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (wpbWinBit vc ext₀ w.1 w.2.1 w.2.2.2.1)] ≤
      Pr[= true | vc.weakPosBindingExp (tightWpbReduction ps₀ ps₁ ext₀ A)] := by
  unfold challengedRun VectorCommitment.weakPosBindingExp tightWpbReduction
  simp only [monad_norm, simulateRom]
  refine probOutput_bind_mono fun ckVC _ => ?_
  refine probOutput_bind_mono fun crs₀ _ => ?_
  refine probOutput_bind_mono fun crs₁ _ => ?_
  rw [bind_simulateRomWithCache]
  refine probOutput_bind_mono fun z _ => ?_
  obtain ⟨⟨⟨comVC, π₀, π₁⟩, openings⟩, cache₁⟩ := z
  rw [probOutput_bind_const]
  refine le_trans (mul_le_of_le_one_left zero_le tsub_le_self) ?_
  simp only [wpbWinBit, ne_eq, decide_not]
  cases hfind : openings.find? fun p =>
      !decide (p.2.1 = ext₀ crs₀ (ckVC, comVC) π₀ p.1) with
  | some p₁ => simp
  | none => simp

/-- A fixed vector that is a non-codeword passes the code check on a fresh
uniform challenge with probability at most `δ`. -/
private lemma probEvent_noncodeword_check_le {δ : ℝ≥0∞} (hSound : chk.Sound C δ)
    (c : Fin n → Λ) :
    Pr[fun l : L => c ∉ C.code ∧ chk.check l c = true | ($ᵗ L : ProbComp L)] ≤ δ := by
  by_cases hin : c ∈ C.code
  · refine le_of_eq_of_le (probEvent_eq_zero fun l _ h => h.1 hin) zero_le
  · refine le_trans (probEvent_mono fun l _ h => h.2) ?_
    have h2 : Pr[fun l : L => chk.check l c = true | ($ᵗ L : ProbComp L)] =
        Pr[= true | (fun l => chk.check l c) <$> ($ᵗ L : ProbComp L)] := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    rw [h2]
    exact hSound c hin

/-- The remaining bad event has probability at most `(Q + 1) * δ`: the vector
extracted from the first proof is, for fixed keys, a function of the oracle
input, so the relation "non-codeword passing the check" between oracle inputs and outputs is
`δ`-sparse. -/
private lemma challengedRun_chk_le {δ : ℝ≥0∞} (hSound : chk.Sound C δ) {Q : ℕ}
    (hA : ∀ ck, HashQueryBound (A ck) Q) :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (chkWinBit C chk ext₀ w.1 w.2.1 w.2.2.2.1 w.2.2.2.2)] ≤
      ((Q : ℝ≥0∞) + 1) * δ := by
  unfold challengedRun
  simp only [monad_norm]
  rw [← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun ckVC _ => ?_
  refine probEvent_bind_le_of_forall_le fun crs₀ _ => ?_
  refine probEvent_bind_le_of_forall_le fun crs₁ _ => ?_
  rw [probEvent_eq_eq_probOutput]
  exact SparseRelation.probOutput_challenge_le
    (R := fun (q : ComVC × Proof₀) (l : L) =>
      ext₀ crs₀ (ckVC, q.1) q.2 ∉ C.code ∧ chk.check l (ext₀ crs₀ (ckVC, q.1) q.2) = true)
    (fun q => probEvent_noncodeword_check_le C chk hSound _)
    (A (ckVC, crs₀, crs₁)) Q (hA _)
    (fun out => (out.1.1, out.1.2.1))
    (fun out l => chkWinBit C chk ext₀ ckVC crs₀ out l)
    (fun out l h => by simpa [chkWinBit] using h)

/-- Union bound over the challenged shared prefix, via the pointwise event
decomposition `gameWinBit_implies`. -/
private lemma challengedRun_split :
    Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
        pure (gameWinBit C vc chk ps₀ ps₁ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] ≤
      Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
          pure (ks₀WinBit vc ps₀ ext₀ w.1 w.2.1 w.2.2.2.1)] +
        Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
          pure (ks₁WinBit vc chk ps₁ ext₁ w.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] +
        Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
          pure (collWinBit vc ext₀ ext₁ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)] +
        Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
          pure (wpbWinBit vc ext₀ w.1 w.2.1 w.2.2.2.1)] +
        Pr[= true | challengedRun vc chk ps₀ ps₁ A >>= fun w =>
          pure (chkWinBit C chk ext₀ w.1 w.2.1 w.2.2.2.1 w.2.2.2.2)] :=
  probOutput_bind_le_add₅ _ _ _ _ _ _ _ fun w _ =>
    probOutput_pure_bool_le_or₅ _ _ _ _ _ _
      (gameWinBit_implies C vc chk ps₀ ps₁ ext₀ ext₁ w.1 w.2.1 w.2.2.1 w.2.2.2.1 w.2.2.2.2)

end codeBindingProof

/-- **Code-binding of the tight scheme**, with a tight bound: for a
code-binding adversary making at most `Q` random-oracle queries, with a
`δ`-sound code checker,

`Pr[code-binding] ≤ ε_ks₀ + ε_ks₁ + ε_coll + ε_wpb + (Q + 1) * δ`

where `ε_ks₀`, `ε_ks₁`, `ε_coll`, `ε_wpb` are the success probabilities of the
explicit reductions against knowledge soundness of the two argument systems,
collision resistance of the vector commitment's deterministic commit, and weak
position-binding of the vector commitment. None of the reductions rewinds the
adversary.

The hypothesis `Nonempty Γ` rules out a degenerate vacuous win, exactly as in
`scheme_codeBinding`. -/
theorem tightScheme_codeBinding [Nonempty Γ] [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [DecidableEq Proof₀] [SampleableType L] [NeZero n]
    [Inhabited Opn] {δ : ℝ≥0∞}
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (ext₀ : Nark.Extractor (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀)
    (ext₁ : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁)
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) {Q : ℕ}
    (hSound : chk.Sound C δ) (hA : ∀ ck, HashQueryBound (A ck) Q) :
    Pr[= true | (tightScheme (m := OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
        C vc chk ps₀ ps₁).codeBindingExp C (roRuntime (ComVC × Proof₀) L) A] ≤
      Pr[= true | ps₀.knowledgeSoundnessExp ext₀ (tightKs₀Reduction vc ps₁ A)] +
      Pr[= true | ps₁.knowledgeSoundnessExp ext₁ (tightKs₁Reduction vc ps₀ A)] +
      Pr[= true | vc.collisionExp (tightCollReduction ps₀ ps₁ ext₀ ext₁ A)] +
      Pr[= true | vc.weakPosBindingExp (tightWpbReduction ps₀ ps₁ ext₀ A)] +
      ((Q : ℝ≥0∞) + 1) * δ := by
  refine le_trans (game_le_challengedRun C vc chk ps₀ ps₁ A) ?_
  refine le_trans (challengedRun_split C vc chk ps₀ ps₁ ext₀ ext₁ A) ?_
  exact add_le_add (add_le_add (add_le_add (add_le_add
    (challengedRun_ks₀_le vc chk ps₀ ps₁ ext₀ A)
    (challengedRun_ks₁_le vc chk ps₀ ps₁ ext₁ A))
    (challengedRun_coll_le vc chk ps₀ ps₁ ext₀ ext₁ A))
    (challengedRun_wpb_le vc chk ps₀ ps₁ ext₀ A))
    (challengedRun_chk_le C vc chk ps₀ ps₁ ext₀ A hSound hA)

/-- **Code-binding of the tight scheme, from primitive assumptions only**: as
`tightScheme_codeBinding`, but with the commit-collision and weak
position-binding terms replaced by position-binding of the vector commitment
(via the explicit reductions of `Assumptions/VectorCommitment.lean`), assuming
perfect completeness of the vector commitment:

`Pr[code-binding] ≤ ε_ks₀ + ε_ks₁ + ε_pb + ε'_pb + (Q + 1) * δ`. -/
theorem tightScheme_codeBinding_posBinding [Nonempty Γ] [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [DecidableEq Proof₀] [SampleableType L] [NeZero n]
    [Inhabited Opn] {δ : ℝ≥0∞}
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))
    (ext₀ : Nark.Extractor (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀)
    (ext₁ : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁)
    (A : ErasureCodeCommitment.CodeBindingAdv
      (OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
      Λ n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁) Opn) {Q : ℕ}
    (hvc : vc.PerfectlyComplete) (hSound : chk.Sound C δ)
    (hA : ∀ ck, HashQueryBound (A ck) Q) :
    Pr[= true | (tightScheme (m := OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
        C vc chk ps₀ ps₁).codeBindingExp C (roRuntime (ComVC × Proof₀) L) A] ≤
      Pr[= true | ps₀.knowledgeSoundnessExp ext₀ (tightKs₀Reduction vc ps₁ A)] +
      Pr[= true | ps₁.knowledgeSoundnessExp ext₁ (tightKs₁Reduction vc ps₀ A)] +
      Pr[= true | vc.posBindingExp
        ((tightCollReduction ps₀ ps₁ ext₀ ext₁ A).toPosBindingAdv vc)] +
      Pr[= true | vc.posBindingExp
        ((tightWpbReduction ps₀ ps₁ ext₀ A).toPosBindingAdv vc)] +
      ((Q : ℝ≥0∞) + 1) * δ := by
  refine le_trans (tightScheme_codeBinding C vc chk ps₀ ps₁ ext₀ ext₁ A hSound hA) ?_
  have hc := VectorCommitment.collisionExp_le_posBindingExp vc hvc
    (tightCollReduction ps₀ ps₁ ext₀ ext₁ A)
  have hw := VectorCommitment.weakPosBindingExp_le_posBindingExp vc hvc
    (tightWpbReduction ps₀ ps₁ ext₀ A)
  gcongr

end PqDas
