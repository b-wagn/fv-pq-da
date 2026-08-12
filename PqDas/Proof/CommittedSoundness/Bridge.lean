/-
# Bridge between the two formulations of the committed soundness game

`niCommittedSoundnessExp` interprets the game with the caching random oracle
implemented directly over plain probabilistic computations (`romImpl`,
cf. `RomRuntime`). The forking analysis instead uses `CommittedSoundness.runTrace`, where
the same caching logic (`CommittedSoundness.roImpl`) draws its fresh answers from a
*counted* challenge oracle of the wrapped spec, interpreted uniformly. This
file proves the two agree: the simulations differ only in where the uniform
entropy is drawn from, so the value distributions coincide
(`evalDist_fst_run_wrapped`).

The one-step helpers below are continuation-parameterized: each states how a
single simulated query composed with an arbitrary continuation unfolds, so
that rewriting never mixes differently-spelled (definitionally equal) range
types.
-/
import PqDas.Proof.CommittedSoundness.Fork

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section bridge

variable [DecidableEq ComVC] [SampleableType L] [Fintype L] [Inhabited L]

/-- Uniform interpretation of the counted challenge oracle. Opt-in per
`IsUniformSpec`'s design; combined with the ambient `unifSpec` instance this
interprets the whole wrapped spec uniformly. -/
noncomputable scoped instance : IsUniformSpec ((Unit →ₒ L) : OracleSpec Unit) :=
  IsUniformSpec.ofFintypeInhabited _

/-! #### One-step unfolding helpers -/

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_run_query_bind {α : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (mx : (unifSpec + (ComVC →ₒ L)).Range t → OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (st : SimState ComVC L) :
    (simulateQ (unifForward ComVC L + roImpl ComVC L)
        (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= mx)).run st =
      ((unifForward ComVC L + roImpl ComVC L) t).run st >>= fun x =>
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (mx x.1)).run x.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_run_query_bind {α : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (mx : (unifSpec + (ComVC →ₒ L)).Range t → OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (cache : (ComVC →ₒ L).QueryCache) :
    simulateRomWithCache cache (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= mx) =
      ((romImpl ComVC L) t).run cache >>= fun x =>
        simulateRomWithCache x.2 (mx x.1) := by
  simp only [simulateRomWithCache, simulateQ_query_bind, StateT.run'_eq, StateT.run_bind,
    map_bind]
  rfl

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_inl {β : Type} (i : ℕ) (st : SimState ComVC L)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inl i) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run st >>= K =
      (query (spec := wrappedSpec L) (Sum.inl i)) >>= fun u => K (u, st) := by
  simp only [QueryImpl.add_apply_inl, unifForward]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_step_inl {β : Type} (i : ℕ) (cache : (ComVC →ₒ L).QueryCache)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inl i) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inl i)).run cache >>= K =
      (query (spec := unifSpec) i) >>= fun u => K (u, cache) := by
  simp only [romImpl, QueryImpl.add_apply_inl]
  rfl

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_hit {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC} {v : L}
    (h : cache com = some v)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (cache, log) >>= K =
      K (v, cache, log) := by
  show (roImpl ComVC L com).run (cache, log) >>= K = _
  rw [roImpl_run_hit h, pure_bind]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_step_hit {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {v : L} (h : cache com = some v)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inr com)).run cache >>= K = K (v, cache) := by
  show ((randomOracle : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) com).run cache >>= K = _
  rw [randomOracle_run_hit h, pure_bind]
  rfl

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_miss {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC}
    (h : cache com = none)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (cache, log) >>= K =
      (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp (wrappedSpec L) L) >>=
        fun u => K (u, cache.cacheQuery com u, log ++ [com]) := by
  show (roImpl ComVC L com).run (cache, log) >>= K = _
  simp only [roImpl, StateT.run_bind, StateT.run_get, pure_bind, h, StateT.run_set,
    bind_assoc, StateT.run_monadLift]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_step_miss {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} (h : cache com = none)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inr com)).run cache >>= K =
      ($ᵗ L) >>= fun u => K (u, cache.cacheQuery com u) := by
  show ((randomOracle : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) com).run cache >>= K = _
  simp only [randomOracle, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get,
    pure_bind, h, uniformSampleImpl, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.run_lift, StateT.run_modifyGet, bind_assoc]
  rfl

/-- The two caching simulations of a computation in the adversary's oracle
world — drawing fresh answers from the wrapped spec's counted challenge
oracle (left) or from plain uniform sampling (right) — produce identically
distributed values, for any common initial cache and any initial log. -/
theorem evalDist_fst_run_wrapped {α : Type}
    (prog : OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (cache : (ComVC →ₒ L).QueryCache) (log : List ComVC) :
    𝒟[Prod.fst <$> (simulateQ (unifForward ComVC L + roImpl ComVC L) prog).run (cache, log)] =
      𝒟[simulateRomWithCache cache prog] := by
  induction prog using OracleComp.inductionOn generalizing cache log with
  | pure x =>
      simp [simulateRomWithCache, simulateQ_pure, StateT.run_pure, StateT.run'_eq]
  | query_bind t mx ih =>
      rw [wrapped_run_query_bind, rom_run_query_bind, map_bind]
      cases t with
      | inl i =>
          rw [wrapped_step_inl, rom_step_inl, evalDist_bind, evalDist_bind]
          refine Eq.trans (bind_congr fun u => ih u cache log) ?_
          rfl
      | inr com =>
          cases hcache : cache com with
          | some v =>
              rw [wrapped_step_hit hcache, rom_step_hit hcache]
              exact ih v cache log
          | none =>
              rw [wrapped_step_miss hcache, rom_step_miss hcache, evalDist_bind,
                evalDist_bind]
              simp only [evalDist_liftM, evalDist_uniformSample,
                OracleQuery.cont_query, OracleQuery.input_query]
              refine Eq.trans
                (bind_congr fun u => ih u (cache.cacheQuery com u) (log ++ [com])) ?_
              show (do
                  let u ← (liftM (PMF.map (@id L) (PMF.uniformOfFintype L)) : SPMF L)
                  𝒟[simulateRomWithCache (cache.cacheQuery com u) (mx u)]) = _
              rw [PMF.map_id]

/-- The winning probability of the non-interactive committed soundness game is
the expectation, over the commitment key, of the probability that the recorded
trace of the wrapped game wins. -/
theorem probOutput_niCommittedSoundnessExp_eq_tsum [Fintype Γ] [DecidableEq Λ]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) :
    Pr[= true | niCommittedSoundnessExp C vc chk A] =
      ∑' ckVC : CkVC, Pr[= ckVC | vc.setup] *
        Pr[fun t => t.win = true | runTrace C vc chk A ckVC] := by
  unfold niCommittedSoundnessExp
  rw [← evalDist_simulateRom, probOutput_evalDist]
  simp only [simulateRom]
  rw [show (do
      let ckVC ← (liftM vc.setup : OracleComp (unifSpec + (ComVC →ₒ L)) CkVC)
      let (com, c) ← A ckVC
      let l ← HasQuery.query (spec := (ComVC →ₒ L)) com
      return (decide (c ∉ C.code) && chk.check l c && decide (vc.commit ckVC c = com))) =
    (liftM vc.setup : OracleComp (unifSpec + (ComVC →ₒ L)) CkVC) >>= fun ckVC =>
      winOn C vc chk ckVC <$> wrappedAdv A ckVC from by
    simp only [wrappedAdv, winOn, map_bind, monad_norm, Function.comp_apply]]
  rw [simulateRomWithCache_liftM_bind, probOutput_bind_eq_tsum]
  refine tsum_congr fun ckVC => ?_
  refine congrArg _ ?_
  rw [simulateRomWithCache_map, probOutput_map]
  refine (probEvent_congr' (fun out _ => Iff.rfl)
    (evalDist_fst_run_wrapped (wrappedAdv A ckVC) ∅ []).symm).trans ?_
  rw [probEvent_map]
  unfold runTrace
  rw [show (do
      let (out, st) ← StateT.run
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)) (∅, [])
      pure { com := out.1, vec := out.2.1, chal := out.2.2, roCache := st.1,
             queryLog := st.2, win := winOn C vc chk ckVC out }) =
    (fun z => (⟨z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2, winOn C vc chk ckVC z.1⟩ :
        Trace Λ n ComVC L)) <$>
      (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)).run (∅, [])
    from by simp only [map_eq_bind_pure_comp]; rfl]
  rw [probEvent_map]
  rfl

end bridge

end CommittedSoundness

end PqDas
