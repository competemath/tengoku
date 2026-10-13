/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.P.Cobham.Defs
public import Tengoku.Complexitylib.Complexitylib.Classes.P.Defs
public import Tengoku.Complexitylib.Complexitylib.Encoding.Pairing
public import Tengoku

/-!
# Fixed-arity inputs for Cobham's characterization

`FP` is defined for unary string functions, while Cobham's algebra is inherently
multi-arity. This module gives the public, auditable bridge: `encodeVec` packs a
fixed-arity argument vector into one string, `vectorLength` measures its unencoded
size, and `FPn` asks a unary `FP` function to agree on the encoded vectors.

The nested pairing has an arity-dependent constant overhead. It is injective, and
for every fixed arity its encoded length is linear in `vectorLength`.

## Main definitions and results

- `Cobham.encodeVec` — nested-pairing tuple encoding, head component last
- `Cobham.vectorLength` — sum of the component lengths
- `Cobham.encodeVec_injective` — tuple encoding loses no information
- `Cobham.encodeVec_length_le` — fixed-arity linear length bound
- `Cobham.FPn` — polynomial time on encoded argument vectors
-/

@[expose] public section

namespace Complexity

namespace Cobham

/-- Encode an argument vector as a single bitstring by nested pairing, with the
head component placed in the verbatim suffix:
`encodeVec ![] = []` and `encodeVec (x ::ᵥ v) = pair (encodeVec v) x`. -/
def encodeVec : {n : ℕ} → (Fin n → List Bool) → List Bool
  | 0, _ => []
  | _ + 1, v => pair (encodeVec (Fin.tail v)) (v 0)

/--
@isnad1 id=eq.0h1v.s4.d45a06953cbf from=translated src=- shape=7a20c624 vocab=d7bcb70e
-/
@[simp] theorem encodeVec_zero (v : Fin 0 → List Bool) : encodeVec v = [] := rfl

/--
@isnad1 id=eq.0h2v.s6.0167963237e0 from=translated src=- shape=402d1a3f vocab=28ec8ebd
-/
@[simp] theorem encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    encodeVec v = pair (encodeVec (Fin.tail v)) (v 0) := rfl

/-- The arity-one encoding is the single component placed in the verbatim suffix
of an empty block: `encodeVec ![x] = pair [] x`.
@isnad1 id=eq.0h1v.s5.89d17c183bf1 from=translated src=- shape=8feb2704 vocab=86bb46ff
-/
theorem encodeVec_one (v : Fin 1 → List Bool) : encodeVec v = pair [] (v 0) := by
  simp [encodeVec]

/-- The sum of the component lengths of a fixed-arity input vector. -/
def vectorLength {n : ℕ} (v : Fin n → List Bool) : ℕ :=
  ∑ i, (v i).length

/--
@isnad1 id=eq.0h1v.s4.0e4691efeaba from=translated src=- shape=4665241e vocab=b71dce8e
-/
@[simp] theorem vectorLength_zero (v : Fin 0 → List Bool) : vectorLength v = 0 := by
  simp [vectorLength]

/--
@isnad1 id=eq.0h2v.s6.18c844f2983b from=translated src=- shape=aaf2c48e vocab=80735690
-/
@[simp] theorem vectorLength_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    vectorLength v = (v 0).length + vectorLength (Fin.tail v) := by
  rw [vectorLength, Fin.sum_univ_succ, vectorLength]
  rfl

/-- Exact recursive length law for the nested tuple encoding.
@isnad1 id=eq.0h2v.s7.ed95b8fcdd92 from=translated src=- shape=ed269b0c vocab=d68fa402
-/
theorem encodeVec_length_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    (encodeVec v).length =
      2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length := by
  simp [encodeVec_succ]

/-- `encodeVec` is injective at every arity.
@isnad1 id=injectiv.0h1v.s3.ac33073d92a3 from=translated src=- shape=368e654b vocab=2b21f2d8
-/
theorem encodeVec_injective {n : ℕ} : Function.Injective (@encodeVec n) := by
  induction n with
  | zero =>
      intro v w _
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      intro v w h
      rw [encodeVec_succ, encodeVec_succ] at h
      obtain ⟨htail, hhead⟩ := pair_inj h
      have htail' : Fin.tail v = Fin.tail w := ih htail
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hhead
      · exact congrFun htail' j

/-- For fixed arity `n`, the nested encoding has length linear in the sum of the
component lengths. The explicit coefficient also records that this is not a
uniform-in-arity linear bound.
@isnad1 id=le.0h2v.s6.61220c9e986f from=translated src=- shape=370d0810 vocab=005c5715
-/
theorem encodeVec_length_le {n : ℕ} (v : Fin n → List Bool) :
    (encodeVec v).length ≤ 2 ^ n * (vectorLength v + 2 * n) := by
  induction n with
  | zero =>
      simp [encodeVec, vectorLength]
  | succ n ih =>
      rw [encodeVec_length_succ, vectorLength_succ]
      have hp : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
      have h2 := Nat.mul_le_mul_left 2 (ih (Fin.tail v))
      calc
        2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length
            ≤ 2 * (2 ^ n * (vectorLength (Fin.tail v) + 2 * n)) +
                2 + (v 0).length := by omega
        _ ≤ 2 ^ (n + 1) *
              ((v 0).length + vectorLength (Fin.tail v) + 2 * (n + 1)) := by
            rw [pow_succ]
            nlinarith

/-- **Multi-arity polynomial time.** A function of an argument vector is `FPn`
when some genuine unary `FP` function computes it on encoded vectors. -/
def FPn {n : ℕ} (f : (Fin n → List Bool) → List Bool) : Prop :=
  ∃ g, g ∈ FP ∧ ∀ v, g (encodeVec v) = f v

end Cobham

end Complexity
