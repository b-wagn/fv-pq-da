/-
# Code-binding of the scheme

Code-binding of the erasure code commitment scheme, by reduction to three
assumptions (compare Foundations of Data Availability Sampling,
eprint 2023/1079, Lemma 14, which treats the variant where the argument system
proves exact code membership):

* knowledge soundness of the argument system,
* hardness of the non-interactive committed soundness game (which encapsulates
  the interplay between the code checker and the oracle-derived randomness;
  bounded separately), and
* weak position-binding of the vector commitment.

Given a code-binding adversary, run it and extract a witness `c` from the
proof it output, using the argument system's straightline extractor at the
statement `(ckVC, comVC, H(comVC))`. Decompose the winning event:

* if extraction fails (the proof verifies but the extracted witness does not
  satisfy the relation), the run breaks knowledge soundness (`ksReduction`);
* if extraction succeeds but `c` is not a codeword, then `c` passes the code
  check on randomness `H(comVC)` and commits to `comVC` — a win in the
  non-interactive committed soundness game (`csReduction`);
* if extraction succeeds and `c` is a codeword, then since no codeword is
  consistent with the adversary's opened symbols, some opened `(i, x, τ)` has
  `x ≠ c i`, and `τ` is a valid opening of the honest commitment
  `comVC = vc.commit ckVC c` — breaking weak position-binding
  (`wpbReduction`).

All three reductions are explicit algorithms; each reproduces the code-binding
experiment's distribution exactly (simulating the random-oracle world
internally where needed), so the union bound is a sum of their winning
probabilities.
-/
import PqDas.Target.Scheme
import PqDas.Proof.CommittedSoundness

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- The adversary's continuation shared by the reductions below: run the
code-binding adversary, then query the oracle once more on the commitment it
output (a cache hit if the adversary already queried it), obtaining the check
randomness that the scheme's verification would use. -/
def runWithChallenge
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn)
    (ck : CkVC × Crs) :
    OracleComp (unifSpec + (ComVC →ₒ L))
      (((ComVC × Proof) × List (Fin n × Λ × Opn)) × L) := do
  let out ← A ck
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) out.1.1
  return (out, l)

/-- Reduction to knowledge soundness (an explicit PPT algorithm): sample the
vector-commitment key, simulate the random-oracle world for the code-binding
adversary, and output the statement `(ckVC, comVC, l)` together with the
adversary's proof. -/
noncomputable def ksReduction [DecidableEq ComVC] [SampleableType L]
    (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Nark.KnowledgeSoundnessAdv (CkVC × ComVC × L) Crs Proof := fun crs => do
  let ckVC ← vc.setup
  let ((com, _), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  return ((ckVC, com.1, l), com.2)

/-- Reduction to the non-interactive committed soundness game (an explicit PPT
algorithm): sample the crs, relay the code-binding adversary's oracle access,
and output the vector-commitment part of its commitment together with the
extracted witness. -/
noncomputable def csReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    NiCsAdv Λ n CkVC ComVC L := fun ckVC => do
  let crs ← liftM ps.setup
  let (com, _) ← A (ckVC, crs)
  let l ← HasQuery.query (spec := (ComVC →ₒ L)) com.1
  return (com.1, ext crs (ckVC, com.1, l) com.2)

/-- Reduction to weak position-binding (an explicit PPT algorithm): sample the
crs, simulate the random-oracle world for the code-binding adversary, extract
the witness `c` from its proof, and search its openings for one whose symbol
disagrees with `c`. If none disagrees the reduction has lost anyway and
outputs a dummy tuple. -/
noncomputable def wpbReduction [NeZero n] [DecidableEq Λ] [DecidableEq ComVC]
    [SampleableType L] [Inhabited Opn]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.WeakPosBindingAdv Λ n CkVC Opn := fun ckVC => do
  let crs ← ps.setup
  let ((com, openings), l) ← simulateRom (runWithChallenge A (ckVC, crs))
  let c := ext crs (ckVC, com.1, l) com.2
  match openings.find? (fun p => decide (p.2.1 ≠ c p.1)) with
  | some p => return (c, p.1, p.2.1, p.2.2)
  | none => return (c, 0, c 0, default)

/-- **Code-binding of the scheme**, by reduction to knowledge soundness of the
argument system, the non-interactive committed soundness game, and weak
position-binding of the vector commitment, via the three explicit reductions
above.

The hypothesis `Nonempty Γ` rules out a degenerate vacuous win: if there were
no messages at all, the empty list of openings would be inconsistent with the
(empty) code without the adversary ever producing a verifying proof or
opening. -/
theorem scheme_codeBinding [Nonempty Γ] [Fintype Γ] [DecidableEq Λ]
    [DecidableEq ComVC] [SampleableType L] [NeZero n] [Inhabited Opn]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (ext : Nark.Extractor (CkVC × ComVC × L) (Fin n → Λ) Crs Proof)
    (A : ErasureCodeCommitment.CodeBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    Pr[= true | (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
        C vc chk ps).codeBindingExp C (roRuntime ComVC L) A] ≤
      Pr[= true | ps.knowledgeSoundnessExp ext (ksReduction vc A)] +
      Pr[= true | niCommittedSoundnessExp C vc chk (csReduction ps ext A)] +
      Pr[= true | vc.weakPosBindingExp (wpbReduction ps ext A)] := by
  sorry

end PqDas
