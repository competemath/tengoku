import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The sets T0, T1, T2 in LN97 Lemma 6.45

For a positive divisor `m | q-1`, LN97 sets

    g = f^((q-1)/m)

and partitions the field into

* `T0 = {c | f(c)=0}`,
* `T1 = {c | g(c)=1}`,
* `T2 = {c | g(c)^(m-1)+...+g(c)+1=0}`.

This file fixes the finite-set notation used in Theorem 6.53.
-/

/-- The exponent `(q-1)/m` used in Lemma 6.45.-/
def stepanovPowerExponent (m q : ℕ) : ℕ := (q - 1) / m

/-- `g = f^((q-1)/m)`.-/
noncomputable def stepanovG (m : ℕ) (f : Polynomial F) : Polynomial F :=
  f ^ stepanovPowerExponent m (Fintype.card F)

/-- `T0`: zeros of `f`.-/
noncomputable def stepanovT0 (f : Polynomial F) : Finset F := by
  classical
  exact Finset.univ.filter (fun c => eval c f = 0)

/-- `T1`: points where `g(c)=1`.-/
noncomputable def stepanovT1 (m : ℕ) (f : Polynomial F) : Finset F := by
  classical
  exact Finset.univ.filter
    (fun c => eval c (stepanovG m f) = 1)

/-- Geometric-series polynomial `1+X+...+X^(m-1)`.-/
noncomputable def geometricPolynomial (m : ℕ) : Polynomial F :=
  ∑ i ∈ Finset.range m, X ^ i

/-- `T2`: points where the geometric-series factor vanishes at `g(c)`.-/
noncomputable def stepanovT2 (m : ℕ) (f : Polynomial F) : Finset F := by
  classical
  exact Finset.univ.filter
    (fun c => eval (eval c (stepanovG m f)) (geometricPolynomial (F := F) m) = 0)

@[simp] theorem mem_stepanovT0 (f : Polynomial F) (c : F) :
    c ∈ stepanovT0 f ↔ eval c f = 0 := by
  classical
  simp [stepanovT0]

@[simp] theorem mem_stepanovT1 (m : ℕ) (f : Polynomial F) (c : F) :
    c ∈ stepanovT1 m f ↔ eval c (stepanovG m f) = 1 := by
  classical
  simp [stepanovT1]

@[simp] theorem mem_stepanovT2 (m : ℕ) (f : Polynomial F) (c : F) :
    c ∈ stepanovT2 m f ↔
      eval (eval c (stepanovG m f)) (geometricPolynomial (F := F) m) = 0 := by
  classical
  simp [stepanovT2]

end LN97
end MagicSquares
