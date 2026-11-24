# Formally Verified Security of Post-Quantum DAS

Proving security of the PQ DAS scheme from [this post](https://ethresear.ch/t/leanda-design-and-benchmark/25642) in Lean4. Code comments and README refer to the [Foundations paper](https://eprint.iacr.org/2023/1079.pdf) from time to time.

More details and explanation can be found [here](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746).

*Disclaimer.* The lean code here proves statements about an abstract scheme, under assumptions about abstract building blocks. In particular, it does not prove security of any production implementation and can never replace proper audit of future implementations.

## Building

```
lake build                              # everything (first build downloads the mathlib cache)
lake build PqDas.AxiomCheck             # re-run the axiom audit
lake build PqDas.ProofTight.AxiomCheck  # build and audit the tight variant (see below)
```

The tight variant (`Target/TightScheme.lean`, `ProofTight/`) is not imported by
the root module `PqDas.lean`, so plain `lake build` does not compile it; the
third command does.

Toolchain: Lean `v4.32.2`, mathlib `v4.32.2`, VCVio pinned in
`lake-manifest.json`.

## Assumptions on building blocks

| Building block | Lean | Security notion | Reference |
|---|---|---|---|
| Erasure code | `ErasureCode` (`Assumptions/ErasureCode.lean`) | — (only the encoding map is needed) | Foundations §6 |
| Vector commitment, deterministic commit/open | `VectorCommitment` (`Assumptions/VectorCommitment.lean`) | `PerfectlyComplete`, `posBindingExp` (position-binding) | Foundations Defs 15, 16 |
| Code checker (probabilistic membership check) | `CodeChecker` (`Assumptions/CodeChecker.lean`) | `Complete`, `Sound` (`δ`-soundness; counting form `sound_iff_card_le`) | new primitive |
| Non-interactive argument of knowledge, straightline extractor | `Nark` (`Assumptions/Nark.lean`) | `PerfectlyComplete`, `knowledgeSoundnessExp` | Foundations Defs 17, 18 |
| Random oracle | `roRuntime` (`RomRuntime.lean`) | — | — |

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


## A variant with a tight code-binding proof

The code-binding bound above loses a square root and a factor `Q`, because the
only argument of knowledge is produced after the check randomness is known and
the proof has to rewind. `Target/TightScheme.lean` defines a variant in which
the committer proves knowledge of the committed vector *before* the check
randomness exists, and that proof is hashed:

* `comVC := vc.commit ckVC c`, as before;
* `π₀` proves knowledge of a `c` committing to `comVC` (relation `commitRel`);
* `l := H(comVC, π₀)`;
* `π₁` proves knowledge of a `c` committing to `comVC` and passing
  `chk.check l c` (relation `schemeRel`, unchanged);
* the commitment is `(comVC, π₀, π₁)`; verification recomputes `l` and checks
  both proofs and the opening.

The vector extracted from `π₀` is a function of the keys and the oracle input
`(comVC, π₀)`, hence fixed before `l` is sampled, and no rewinding is needed.
The cost is a second proof: both `π₀` and `π₁` prove a statement about the
vector commitment.

Additional building block: a second argument of knowledge, for `commitRel`
(same `Nark` interface, own reference string and extractor). All other
building blocks, definitions and security notions are reused unchanged.

| Theorem | Statement (informal) | File |
|---|---|---|
| `tightScheme_perfectlyComplete` | the tight scheme is a perfectly complete erasure code commitment | `Target/TightScheme.lean` |
| `tightScheme_positionBinding` | `Pr[pos-bind] ≤ ε_pb(VC)` | `ProofTight/PositionBinding.lean` |
| `SparseRelation.probOutput_challenge_le` | a `Q`-query adversary finds `x` with `R x (H x)` with probability `≤ (Q+1)·δ`, for any `δ`-sparse relation `R` | `ProofTight/SparseRelation.lean` |
| `tightScheme_codeBinding` | `Pr[code-bind] ≤ ε_ks₀ + ε_ks₁ + ε_coll + ε_wpb + (Q+1)·δ` | `ProofTight/CodeBinding.lean` |
| `tightScheme_codeBinding_posBinding` | as above with `ε_coll`, `ε_wpb` replaced by position-binding of the VC (assuming the VC is perfectly complete) | `ProofTight/CodeBinding.lean` |

| Reduction | Breaks | From | File |
|---|---|---|---|
| `tightPosBindingReduction` | VC position-binding | tight-scheme position-binding adversary | `ProofTight/PositionBinding.lean` |
| `tightKs₀Reduction` | knowledge soundness of the first argument | code-binding adversary | `ProofTight/CodeBinding.lean` |
| `tightKs₁Reduction` | knowledge soundness of the second argument | code-binding adversary | `ProofTight/CodeBinding.lean` |
| `tightCollReduction` | VC commit collision | code-binding adversary (no rewinding) | `ProofTight/CodeBinding.lean` |
| `tightWpbReduction` | VC weak position-binding | code-binding adversary | `ProofTight/CodeBinding.lean` |

The term `(Q+1)·δ` has no reduction attached; it is a union bound over the
random-oracle queries, using soundness of the code checker.

The two code-binding theorems assume that the checker is `δ`-sound, that the
adversary makes at most `Q` random-oracle queries for every key, and (as for
the original scheme) `Nonempty Γ`, `NeZero n` and `Inhabited Opn`.
`tightCollReduction` and `tightWpbReduction` call the extractors, so they are
efficient only if the extractors are.

*Caveat.* The tightness relies on the modeling of knowledge soundness in
`Assumptions/Nark.lean`: the extractor is a function of `(crs, stmt, π)` alone.
For an argument system whose extractor additionally reads the prover's
random-oracle queries, the vector must be extractable at the time `(comVC, π₀)`
is hashed; this is not covered here.


## Axioms
To check which axioms are used, run `lake lean PqDas/AxiomCheck.lean`
(and `lake lean PqDas/ProofTight/AxiomCheck.lean` for the tight variant).

Current output:

```
'PqDas.scheme_positionBinding'                                    : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding'                                        : [propext, Classical.choice, Quot.sound]
'PqDas.CommittedSoundness.niCommittedSoundness_forking_bound'     : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_perfectlyComplete'                                  : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding_concrete'                               : [propext, Classical.choice, Quot.sound]
'PqDas.scheme_codeBinding_concrete_posBinding'                    : [propext, Classical.choice, Quot.sound]
```

Tight variant:

```
'PqDas.tightScheme_perfectlyComplete'                             : [propext, Classical.choice, Quot.sound]
'PqDas.tightScheme_positionBinding'                               : [propext, Classical.choice, Quot.sound]
'PqDas.SparseRelation.probOutput_challenge_le'                    : [propext, Classical.choice, Quot.sound]
'PqDas.tightScheme_codeBinding'                                   : [propext, Classical.choice, Quot.sound]
'PqDas.tightScheme_codeBinding_posBinding'                        : [propext, Classical.choice, Quot.sound]
```

There are no `sorry`s and no custom axioms anywhere in the project.


## License
Apache License.
