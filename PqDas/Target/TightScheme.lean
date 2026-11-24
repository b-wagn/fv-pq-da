/-
# The tight scheme: extract before the challenge

A variant of the erasure code commitment of `Target/Scheme.lean` whose
code-binding proof needs no rewinding, and is therefore tight in the
position-binding advantage of the vector commitment.

In the original scheme the check randomness is `l = H(comVC)`, and the only
argument of knowledge is produced *after* `l` is known. A cheating committer
may therefore choose its vector after seeing `l`; the security proof has to
rewind, which costs a square root and a factor in the number of random-oracle
queries.

Here the committer additionally proves knowledge of the committed vector
*before* the check randomness exists, and that proof is hashed:

* encode the message, `c := C.encode msg`, and commit, `comVC := vc.commit ckVC c`;
* prove knowledge of a `c` that commits to `comVC`, giving `π₀`
  (relation `commitRel`);
* derive the check randomness `l := H(comVC, π₀)`;
* prove knowledge of a `c` that commits to `comVC` and passes `chk.check l c`,
  giving `π₁` (relation `schemeRel`, exactly as in the original scheme);
* output `(comVC, π₀, π₁)`.

Verification recomputes `l` from `(comVC, π₀)`, checks both proofs, and then
the vector-commitment opening.

Since the knowledge extractor of the first argument system is a function of
`(crs₀, (ckVC, comVC), π₀)`, the vector extracted from `π₀` is determined by
the keys and the random-oracle input `(comVC, π₀)`, hence fixed before `l` is
sampled. The
price is a second proof: both `π₀` and `π₁` prove a statement involving the
vector commitment.

The two argument systems may be different (they prove different relations and
have independent reference strings). As in the original scheme, neither has
access to the random oracle `H`.
-/
import PqDas.Target.Scheme

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs₀ Proof₀ Crs₁ Proof₁ : Type}

/-- The relation proven by the first argument of knowledge of the tight
scheme. The statement is a commitment key and a commitment; the witness is a
vector `c` that commits to the given commitment. No check randomness is
involved: this proof is produced before the randomness is derived. -/
def commitRel [DecidableEq ComVC] (vc : VectorCommitment Λ n CkVC ComVC Opn) :
    CkVC × ComVC → (Fin n → Λ) → Bool := fun stmt c =>
  decide (vc.commit stmt.1 c = stmt.2)

/-- The tight erasure code commitment scheme, built from an erasure code `C`,
a vector commitment `vc`, a code checker `chk`, an argument of knowledge `ps₀`
for `commitRel vc`, and an argument of knowledge `ps₁` for `schemeRel vc chk`,
in any ambient monad `m` providing uniform sampling and a random oracle from
pairs (commitment, first proof) to check randomness.

The commitment key is `(ckVC, crs₀, crs₁)`, a commitment is `(comVC, π₀, π₁)`,
and the opening state is the codeword itself. -/
def tightScheme {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    [HasQuery ((ComVC × Proof₀) →ₒ L) m] [DecidableEq ComVC]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
    (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk)) :
    ErasureCodeCommitment m Γ Λ k n (CkVC × Crs₀ × Crs₁) (ComVC × Proof₀ × Proof₁)
      (Fin n → Λ) Opn where
  setup := do
    let ckVC ← (monadLift vc.setup : m CkVC)
    let crs₀ ← (monadLift ps₀.setup : m Crs₀)
    let crs₁ ← (monadLift ps₁.setup : m Crs₁)
    return (ckVC, crs₀, crs₁)
  commit := fun ck msg => do
    let c := C.encode msg
    let comVC := vc.commit ck.1 c
    let π₀ := ps₀.prove ck.2.1 (ck.1, comVC) c
    let l ← HasQuery.query (spec := ((ComVC × Proof₀) →ₒ L)) (comVC, π₀)
    let π₁ := ps₁.prove ck.2.2 (ck.1, comVC, l) c
    return ((comVC, π₀, π₁), c)
  openAt := fun ck c i => pure (vc.openAt ck.1 c i)
  verify := fun ck com i x τ => do
    let l ← HasQuery.query (spec := ((ComVC × Proof₀) →ₒ L)) (com.1, com.2.1)
    return (ps₀.verify ck.2.1 (ck.1, com.1) com.2.1 &&
      ps₁.verify ck.2.2 (ck.1, com.1, l) com.2.2 && vc.verify ck.1 com.1 i x τ)

/-! ### Completeness -/

section completeness

variable [DecidableEq ComVC] [DecidableEq Proof₀] [SampleableType L]
  (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
  (chk : CodeChecker Λ n L)
  (ps₀ : Nark (CkVC × ComVC) (Fin n → Λ) Crs₀ Proof₀ (commitRel vc))
  (ps₁ : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs₁ Proof₁ (schemeRel vc chk))

/-- **Completeness of the tight scheme**: if the vector commitment is
perfectly complete, the code checker is complete for `C`, and both argument
systems are perfectly complete, then the tight scheme is a perfectly complete
erasure code commitment for `C` under the fresh-random-oracle semantics.

The honest execution queries the oracle only on `(comVC, π₀)`: first in
`commit` (a cache miss, answered by a fresh uniform `l`) and then in `verify`
(a cache hit, returning the same `l`). -/
theorem tightScheme_perfectlyComplete (hvc : vc.PerfectlyComplete)
    (hchk : chk.Complete C) (hps₀ : ps₀.PerfectlyComplete)
    (hps₁ : ps₁.PerfectlyComplete) :
    (tightScheme (m := OracleComp (unifSpec + ((ComVC × Proof₀) →ₒ L)))
        C vc chk ps₀ ps₁).PerfectlyComplete C (roRuntime (ComVC × Proof₀) L) := by
  intro msg i
  rw [← evalDist_simulateRom, probOutput_evalDist]
  dsimp only [tightScheme]
  simp only [monad_norm, simulateRom]
  refine le_antisymm probOutput_le_one ?_
  rw [show (1 : ℝ≥0∞) = 1 - 0 from (tsub_zero 1).symm]
  rw [simulateRomWithCache_liftM_bind]
  refine SignatureAlg.le_probOutput_bind_of_forall_support _ _ fun ckVC hck => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine SignatureAlg.le_probOutput_bind_of_forall_support _ _ fun crs₀ hcrs₀ => ?_
  rw [simulateRomWithCache_liftM_bind]
  refine SignatureAlg.le_probOutput_bind_of_forall_support _ _ fun crs₁ hcrs₁ => ?_
  rw [simulateRomWithCache_query_bind,
    randomOracle_run_miss (QueryCache.empty_apply _)]
  simp only [bind_assoc, pure_bind]
  refine SignatureAlg.le_probOutput_bind_of_forall_support _ _ fun l _ => ?_
  have hhit := QueryCache.cacheQuery_self (∅ : ((ComVC × Proof₀) →ₒ L).QueryCache)
    (vc.commit ckVC (C.encode msg),
      ps₀.prove crs₀ (ckVC, vc.commit ckVC (C.encode msg)) (C.encode msg)) l
  rw [simulateRomWithCache_query_bind, randomOracle_run_hit hhit, pure_bind,
    simulateRomWithCache_pure]
  have hrel₀ : commitRel vc (ckVC, vc.commit ckVC (C.encode msg)) (C.encode msg) = true := by
    simp [commitRel]
  have hrel₁ : schemeRel vc chk (ckVC, vc.commit ckVC (C.encode msg), l) (C.encode msg) =
      true := by
    simp [schemeRel, hchk _ (C.encode_mem_code msg) l]
  have hpv₀ := hps₀ crs₀ hcrs₀ _ _ hrel₀
  have hpv₁ := hps₁ crs₁ hcrs₁ _ _ hrel₁
  have hvv := hvc ckVC hck (C.encode msg) i
  simp [hpv₀, hpv₁, hvv]

end completeness

end PqDas
