# Formally Verified Security of Post-Quantum DAS

Proving security of the PQ DAS scheme from [this post](https://ethresear.ch/t/leanda-design-and-benchmark/25642) in Lean4. Code comments refer to the [Foundations paper](https://eprint.iacr.org/2023/1079.pdf) from time to time.

More details and explanation can be found here: TBD

*Disclaimer.* The lean code here proves statements about an abstract scheme, under assumptions about abstract building blocks. In particular, it does not prove security of any production implementation and can never replace proper audit of future implementations.

## Building

```
lake build                    # everything (first build downloads the mathlib cache)
lake build PqDas.AxiomCheck   # re-run the axiom audit
```

Toolchain: Lean `v4.32.2`, mathlib `v4.32.2`, VCVio pinned in
`lake-manifest.json`.

## Assumptions on building blocks

| Building block | Lean | Security notion | Reference |
|---|---|---|---|
| Erasure code | `ErasureCode` (`Assumptions/ErasureCode.lean`) | — (only the encoding map is needed) | Foundations §6 |
| Vector commitment, deterministic commit/open | `VectorCommitment` (`Assumptions/VectorCommitment.lean`) | `PerfectlyComplete`, `posBindingExp` (position-binding) | Foundations Defs 15, 16 |
| Code checker (probabilistic membership check) | `CodeChecker` (`Assumptions/CodeChecker.lean`) | `Complete`, `Sound` (`δ`-soundness; counting form `sound_iff_card_le`) | new primitive |
| Non-interactive argument of knowledge, straightline extractor | `Nark` (`Assumptions/Nark.lean`) | `PerfectlyComplete`, `knowledgeSoundnessExp` | Foundations Defs 17, 18 |
| Random oracle | `RomRuntime.lean` (`roRuntime`: lazily sampled, cache shared between adversary and scheme) | — | — |

Derived notions proven from position-binding (+ perfect completeness), used
by the code-binding proof (`Assumptions/VectorCommitment.lean`):

- `weakPosBindingExp_le_posBindingExp` — opening an honest commitment to a
  wrong symbol;
- `collisionExp_le_posBindingExp` — two distinct vectors with the same
  (deterministic) commitment.

## Main theorems

All in namespace `PqDas`; success probabilities are concrete `ℝ≥0∞`
quantities, never asymptotic. `Q` denotes a bound on the adversary's
random-oracle queries, `δ` the checker's soundness, `L` the checker's
randomness domain.

| Theorem | Statement (informal) | File |
|---|---|---|
| `scheme_perfectlyComplete` | the scheme is a perfectly complete erasure code commitment | `Target/Scheme.lean` |
| `scheme_positionBinding` | `Pr[pos-bind] ≤ ε_pb(VC)` | `Proof/PositionBinding.lean` |
| `scheme_codeBinding` | `Pr[code-bind] ≤ ε_ks + ε_nics + ε_wpb` | `Proof/CodeBinding.lean` |
| `CommittedSoundness.niCommittedSoundness_forking_bound` | `acc·(acc/(Q+1) − 1/\|L\|) ≤ ε_coll + δ` for the non-interactive committed soundness game | `Proof/CommittedSoundness/ForkingBound.lean` |
| `scheme_codeBinding_concrete` | `(Pr[code-bind] − (ε_ks + ε_wpb))² ≤ (Q+2)·(ε_coll + δ + 1/\|L\|)` | `Proof/CorollaryCodeBinding.lean` |
| `scheme_codeBinding_concrete_posBinding` | as above with `ε_wpb`, `ε_coll` replaced by position-binding of the VC | `Proof/CorollaryCodeBinding.lean` |

The committed soundness game (`Proof/CommittedSoundness/Defs.lean`) isolates
the main technical difficulty.

## Reductions

Every reduction is an explicit, standalone algorithm, so that its efficiency
can be checked by *human* inspection.

| Reduction | Breaks | From | File |
|---|---|---|---|
| `posBindingReduction` | VC position-binding | scheme position-binding adversary | `Proof/PositionBinding.lean` |
| `ksReduction` | knowledge soundness | code-binding adversary | `Proof/CodeBinding.lean` |
| `csReduction` | NI committed soundness | code-binding adversary | `Proof/CodeBinding.lean` |
| `wpbReduction` | VC weak position-binding | code-binding adversary | `Proof/CodeBinding.lean` |
| `CommittedSoundness.forkCollisionReduction` | VC commit collision | NI committed soundness adversary (rewinds via `contextFork`) | `Proof/CommittedSoundness/ForkingBound.lean` |
| `WeakPosBindingAdv.toPosBindingAdv`, `CollisionAdv.toPosBindingAdv` | VC position-binding | weak-PB / collision adversaries | `Assumptions/VectorCommitment.lean` |


## Axioms
To check which axioms are used, run `lake lean PqDas/AxiomCheck.lean`.

Current output:

```
'PqDas.scheme_positionBinding'                                    : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding'                                        : [propext, Classical.choice, Quot.sound]
'PqDas.CommittedSoundness.niCommittedSoundness_forking_bound'     : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_perfectlyComplete'                                  : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding_concrete'                               : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding_concrete_posBinding'                    : [propext, Classical.choice, Quot.sound]
```

There are no `sorry`s and no custom axioms anywhere in the project.


## License
Apache License.