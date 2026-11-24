/-
# A random oracle rarely hits a sparse relation

The one probabilistic ingredient of the tight code-binding proof, stated
independently of the scheme. Let `R : X → L → Prop` be a relation between
random-oracle inputs and outputs that is *`δ`-sparse*: for every fixed input
`x`, a uniformly random output `l` satisfies `R x l` with probability at most
`δ`. Then a computation that makes at most `Q` random-oracle queries and then
names an input `x` satisfies `R x (H x)` with probability at most
`(Q + 1) * δ` (`probOutput_challenge_le`).

The proof is a union bound over the fresh oracle answers. Call a cache *hit*
if it contains a pair `(x, l)` with `R x l`:

* a cache that is not hit stays not hit under uniform sampling and under
  cache hits of the oracle;
* a cache miss on `x` samples a fresh uniform `l`, which makes the cache hit
  only if `R x l`, an event of probability at most `δ`.

So after `Q` queries the cache is hit with probability at most `Q * δ`
(`probEvent_cacheHits_run_le`), and one more query on the named input costs
one more `δ` (`probEvent_randomOracle_run_le`).

In the application `X` is the type of pairs (commitment, first proof), and
`R (com, π₀) l` says that the vector extracted from `π₀` is a non-codeword
passing the code check on `l`. Sparseness is then exactly soundness of the
code checker, because, once the keys are fixed, the extracted vector is a
function of the oracle input.
-/
import PqDas.RomRuntime
import PqDas.Proof.CommittedSoundness.Fork

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace PqDas

namespace SparseRelation

open CommittedSoundness (HashQueryBound hashQueryBound_query_bind_iff)

variable {X L : Type}

/-- A random-oracle cache is *hit* by the relation `R` if it records an
input/output pair in the relation. -/
def CacheHits (R : X → L → Prop) (cache : (X →ₒ L).QueryCache) : Prop :=
  ∃ x l, cache x = some l ∧ R x l

/-- The empty cache is not hit. -/
lemma not_cacheHits_empty (R : X → L → Prop) :
    ¬ CacheHits R (∅ : (X →ₒ L).QueryCache) := by
  rintro ⟨x, l, h, -⟩
  exact Option.some_ne_none l (h.symm.trans (QueryCache.empty_apply x))

/-- Recording a pair outside the relation in a cache that is not hit gives a
cache that is not hit. -/
lemma not_cacheHits_cacheQuery [DecidableEq X] {R : X → L → Prop}
    {cache : (X →ₒ L).QueryCache} {x : X} {r : L}
    (hc : ¬ CacheHits R cache) (hr : ¬ R x r) :
    ¬ CacheHits R (cache.cacheQuery x r) := by
  rintro ⟨x', l, hx', hR⟩
  by_cases hxx : x' = x
  · subst hxx
    rw [QueryCache.cacheQuery_self] at hx'
    obtain rfl := Option.some.inj hx'
    exact hr hR
  · rw [QueryCache.cacheQuery_of_ne cache r hxx] at hx'
    exact hc ⟨x', l, hx', hR⟩

variable [DecidableEq X] [SampleableType L]

/-- One random-oracle query on a cache that is not hit returns an answer in the
relation with probability at most `δ`: a cache hit returns a recorded answer,
which is outside the relation; a miss returns a fresh uniform answer. -/
lemma probEvent_randomOracle_run_le {R : X → L → Prop} {δ : ℝ≥0∞}
    (hR : ∀ x, Pr[fun l => R x l | ($ᵗ L : ProbComp L)] ≤ δ)
    {cache : (X →ₒ L).QueryCache} (hc : ¬ CacheHits R cache) (x : X) :
    Pr[fun z : L × (X →ₒ L).QueryCache => R x z.1 |
      ((randomOracle : QueryImpl (X →ₒ L)
        (StateT ((X →ₒ L).QueryCache) ProbComp)) x).run cache] ≤ δ := by
  cases hx : cache x with
  | some v =>
      rw [randomOracle_run_hit hx]
      refine le_of_eq_of_le (probEvent_eq_zero fun z hz h => ?_) zero_le
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hc ⟨x, v, hx, h⟩
  | none =>
      rw [randomOracle_run_miss hx]
      refine le_trans (probEvent_bind_le_probEvent (p := fun r => R x r)
        fun r _ hr => ?_) (hR x)
      refine probEvent_eq_zero fun z hz h => ?_
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hr h

/-- **Union bound over the oracle answers.** Simulating a computation with at
most `Q` random-oracle queries, starting from a cache that is not hit, ends in
a hit cache with probability at most `Q * δ`. -/
theorem probEvent_cacheHits_run_le {R : X → L → Prop} {δ : ℝ≥0∞}
    (hR : ∀ x, Pr[fun l => R x l | ($ᵗ L : ProbComp L)] ≤ δ)
    {α : Type} (oa : OracleComp (unifSpec + (X →ₒ L)) α) (Q : ℕ)
    (hQ : HashQueryBound oa Q)
    (cache : (X →ₒ L).QueryCache) (hc : ¬ CacheHits R cache) :
    Pr[fun z : α × (X →ₒ L).QueryCache => CacheHits R z.2 |
      (simulateQ (romImpl X L) oa).run cache] ≤ (Q : ℝ≥0∞) * δ := by
  induction oa using OracleComp.inductionOn generalizing Q cache with
  | pure a =>
      refine le_of_eq_of_le (probEvent_eq_zero fun z hz h => ?_) zero_le
      rw [simulateQ_pure] at hz
      change z ∈ support (pure (a, cache) : ProbComp _) at hz
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hc h
  | query_bind t mx ih =>
      rw [hashQueryBound_query_bind_iff] at hQ
      obtain ⟨hpos, hrest⟩ := hQ
      rw [simulateQ_query_bind, StateT.run_bind]
      cases t with
      | inl i =>
          refine probEvent_bind_le_of_forall_le fun us hus => ?_
          have hus2 : us.2 = cache := by
            simp [romImpl, QueryImpl.add_apply_inl, unifFwdImpl, support_map] at hus
            obtain ⟨u, rfl⟩ := hus
            rfl
          rw [hus2]
          exact ih us.1 Q (hrest us.1) cache hc
      | inr x =>
          have hpos' : 0 < Q := hpos
          have hQ1 : ((Q - 1 : ℕ) : ℝ≥0∞) + 1 = (Q : ℝ≥0∞) := by
            exact_mod_cast Nat.sub_add_cancel hpos'
          change Pr[fun z : α × (X →ₒ L).QueryCache => CacheHits R z.2 |
            ((randomOracle : QueryImpl (X →ₒ L)
              (StateT ((X →ₒ L).QueryCache) ProbComp)) x).run cache >>= fun p =>
                (simulateQ (romImpl X L) (mx p.1)).run p.2] ≤ (Q : ℝ≥0∞) * δ
          cases hx : cache x with
          | some v =>
              rw [randomOracle_run_hit hx, pure_bind]
              refine le_trans (ih v (Q - 1) (hrest v) cache hc) ?_
              exact mul_le_mul' (by exact_mod_cast Nat.sub_le Q 1) le_rfl
          | none =>
              rw [randomOracle_run_miss hx]
              simp only [bind_assoc, pure_bind]
              refine le_trans (probEvent_bind_le_probEvent_add (p := fun r => R x r)
                (ε := ((Q - 1 : ℕ) : ℝ≥0∞) * δ) fun r _ hr => ?_) ?_
              · exact ih r (Q - 1) (hrest r) _ (not_cacheHits_cacheQuery hc hr)
              · calc Pr[fun r => R x r | ($ᵗ L : ProbComp L)] + ((Q - 1 : ℕ) : ℝ≥0∞) * δ
                    ≤ δ + ((Q - 1 : ℕ) : ℝ≥0∞) * δ := add_le_add (hR x) le_rfl
                  _ = (Q : ℝ≥0∞) * δ := by
                      rw [← hQ1, add_mul, one_mul, add_comm]

/-- **A random oracle rarely hits a sparse relation.** Run a computation with
at most `Q` random-oracle queries from the empty cache, then query the oracle
once more on an input `f a` computed from its output `a`. Any Boolean verdict
`g a l` that implies `R (f a) l` for the answer `l` holds with probability at
most `(Q + 1) * δ`. -/
theorem probOutput_challenge_le {R : X → L → Prop} {δ : ℝ≥0∞}
    (hR : ∀ x, Pr[fun l => R x l | ($ᵗ L : ProbComp L)] ≤ δ)
    {α : Type} (oa : OracleComp (unifSpec + (X →ₒ L)) α) (Q : ℕ)
    (hQ : HashQueryBound oa Q)
    (f : α → X) (g : α → L → Bool) (hg : ∀ a l, g a l = true → R (f a) l) :
    Pr[= true | (simulateQ (romImpl X L) oa).run ∅ >>= fun z =>
      ((randomOracle : QueryImpl (X →ₒ L)
          (StateT ((X →ₒ L).QueryCache) ProbComp)) (f z.1)).run z.2 >>= fun x =>
        (pure (g z.1 x.1) : ProbComp Bool)] ≤ ((Q : ℝ≥0∞) + 1) * δ := by
  rw [← probEvent_eq_eq_probOutput]
  refine le_trans (probEvent_bind_le_probEvent_add
    (p := fun z : α × (X →ₒ L).QueryCache => CacheHits R z.2) (ε := δ)
    fun z _ hz => ?_) ?_
  · refine le_trans ?_ (probEvent_randomOracle_run_le hR hz (f z.1))
    rw [bind_pure_comp, probEvent_map]
    exact probEvent_mono fun x _ hx => hg _ _ hx
  · calc Pr[fun z : α × (X →ₒ L).QueryCache => CacheHits R z.2 |
          (simulateQ (romImpl X L) oa).run ∅] + δ
        ≤ (Q : ℝ≥0∞) * δ + δ :=
          add_le_add (probEvent_cacheHits_run_le hR oa Q hQ ∅ (not_cacheHits_empty R)) le_rfl
      _ = ((Q : ℝ≥0∞) + 1) * δ := by rw [add_mul, one_mul]

end SparseRelation

end PqDas
