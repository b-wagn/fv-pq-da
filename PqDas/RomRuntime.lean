/-
# Random-oracle runtime

The semantics of computations in the random-oracle world used throughout this
development: the ambient monad `OracleComp (unifSpec + (ComVC →ₒ L))` provides
uniform sampling and a random oracle from (vector-commitment) commitments to
check randomness. `roRuntime` observes such computations as subdistributions,
interpreting the oracle as a fresh lazily-sampled random oracle: queries that
hit the cache return the cached value, misses are answered by fresh uniform
sampling and cached. The cache-parametric variant `roRuntimeWithCache` is the
hook for programming the oracle in reductions. Mirrors VCVio's
`FiatShamir.runtimeWithCache`.

`simulateRom` runs the same simulation as a plain probabilistic computation
(rather than observing it as a subdistribution); reductions use it to
internally simulate the random-oracle world for an adversary. By construction
the two agree: `evalDist_simulateRomWithCache`.
-/
import VCVio.OracleComp.HasQuery.Morphism
import VCVio.OracleComp.ProbCompLift
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

open OracleComp OracleSpec ENNReal

namespace PqDas

section runtime

variable (ComVC L : Type) [DecidableEq ComVC] [SampleableType L]

/-- Runtime bundle for the random-oracle world, starting from a fixed initial
cache: random-oracle queries that hit the cache return the cached value,
misses are answered by fresh uniform sampling and cached. -/
noncomputable def roRuntimeWithCache (cache : (ComVC →ₒ L).QueryCache) :
    ProbCompRuntime (OracleComp (unifSpec + (ComVC →ₒ L))) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (ComVC →ₒ L) (StateT ((ComVC →ₒ L).QueryCache) ProbComp)))
    cache
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Runtime bundle for the random-oracle world: a fresh random oracle (empty
initial cache). -/
noncomputable def roRuntime : ProbCompRuntime (OracleComp (unifSpec + (ComVC →ₒ L))) :=
  roRuntimeWithCache ComVC L ∅

variable {ComVC L}

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, lazily simulating the oracle starting from the given cache.
Reductions use this to simulate the random-oracle world for an adversary. -/
noncomputable def simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache) {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  (simulateQ (unifFwdImpl (ComVC →ₒ L) + (randomOracle :
    QueryImpl (ComVC →ₒ L) (StateT ((ComVC →ₒ L).QueryCache) ProbComp))) oa).run' cache

/-- Run a computation in the random-oracle world as a plain probabilistic
computation, with a fresh random oracle. -/
noncomputable def simulateRom {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) : ProbComp α :=
  simulateRomWithCache ∅ oa

/-- The simulation and the runtime semantics agree: observing `simulateRom` as
a subdistribution is the same as observing the original computation through
the runtime. -/
lemma evalDist_simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache) {α : Type}
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) :
    𝒟[simulateRomWithCache cache oa] = (roRuntimeWithCache ComVC L cache).evalDist oa := rfl

/-- Fresh-oracle case of `evalDist_simulateRomWithCache`. -/
lemma evalDist_simulateRom {α : Type} (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) :
    𝒟[simulateRom oa] = (roRuntime ComVC L).evalDist oa := rfl

end runtime

end PqDas
