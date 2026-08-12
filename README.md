# Formally Verified Security of Post-Quantum DAS

Proving security of the PQ DAS scheme from [this post](https://ethresear.ch/t/leanda-design-and-benchmark/25642) in Lean4. Code comments refer to the [Foundations paper](https://eprint.iacr.org/2023/1079.pdf) from time to time.

More details and explanation can be found here: TBD

*Disclaimer.* The lean code here proves statements about an abstract scheme, under assumptions about abstract building blocks. In particular, it does not prove security of any production implementation and can never replace proper audit of future implementations.

## Building

Run `lake build`.

To check which axioms are used, run `lake lean PqDas/AxiomCheck.lean`.

## License
Apache License.