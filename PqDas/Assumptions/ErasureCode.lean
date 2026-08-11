/-
# Erasure codes

We abstract an erasure code as a plain encoding function and define the code as
the image of the encoding map. This is all the security proofs of the erasure
code commitment scheme need: reconstruction-style properties (e.g., "any `k`
symbols uniquely determine the codeword") only matter when compiling an erasure
code commitment into a full data availability sampling scheme, which is not
formalized here. Compare Foundations of Data Availability Sampling
(eprint 2023/1079), Section 6.
-/
import VCVio.CryptoFoundations.CommitmentScheme

namespace PqDas

/-- An erasure code with message alphabet `Γ`, code alphabet `Λ`, message
length `k`, and code length `n`, given by its encoding function. -/
structure ErasureCode (Γ Λ : Type) (k n : ℕ) where
  /-- The encoding function of the code. -/
  encode : (Fin k → Γ) → (Fin n → Λ)

namespace ErasureCode

variable {Γ Λ : Type} {k n : ℕ}

/-- The code itself: the set of codewords, i.e. the image of `encode`. -/
def code (C : ErasureCode Γ Λ k n) : Set (Fin n → Λ) := Set.range C.encode

/-- Codeword membership is decidable for finite alphabets. This is used to
state the winning conditions of security games as `Bool`s. -/
instance decidableMemCode (C : ErasureCode Γ Λ k n) [Fintype Γ] [DecidableEq Λ] :
    DecidablePred (· ∈ C.code) := fun c =>
  decidable_of_iff (∃ m, C.encode m = c) Set.mem_range

@[simp]
lemma encode_mem_code (C : ErasureCode Γ Λ k n) (m : Fin k → Γ) :
    C.encode m ∈ C.code := Set.mem_range_self m

end ErasureCode

end PqDas
