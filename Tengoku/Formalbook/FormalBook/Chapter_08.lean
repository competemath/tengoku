/-
Copyright 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Tengoku

open Real (exp )--pi crccos)

open Finset (Icc)
open BigOperators
/-!
# Some irrational numbers

## TODO : All proofs,
## Outline
  - $e$ is irrational
  - $e^2$ is irrational
  - $e^4$ is irrational
  - Lemma
    - (i)
    - (ii)
    - (iii)
    - proof
      - (i)
      - (ii)
      - (iii)
  - Theorem 1.
    - proof
  - Theorem 2.
    - proof
  - Theorem 3.
    - proof
-/

namespace book
namespace irrational

/-- A real number is irrational if it is not rational. This is the same definition as in mathlib -/
def Irrational (x : ℝ) := x ∉ Set.range (fun (q : ℚ) => (q : ℝ))

/-- We define abbreviations for Euler's and for Pi-/
noncomputable def e := exp 1
--noncomputable def π := pi

/-!
## Some Proofs of irrationality
-/

/-!  ### Proofs of the main theorems-/

/-!
####  Auxiliary Lemma
We first prove the following lemma (see `lem_aux_i` to `lem_aux_iii` below):
Let `n : ℕ`, `n ≥ 1` be fixed, and consider `f_aux n x = x ^ n * (1 - x) ^ n / n.factorial`. Then
(i) `f_aux n` is equal, as a function in `x`, to a polynomial of the form
  `(sum (i : Icc n (2 * n)), (c i) x ^i) / n.factorial`, where `c i : ℤ`.
(ii) For `0 < x < 1` we have `0 < f_aux n x < 1 / n.factorial` .
(iii) The `k`-th derivatives `iterated_deriv k (f_aux n)` take integer values at `x = 0` and `x = 1`
   for all `k ≥ 0`.
-/

/-- The auxiliary function `xⁿ * (1 - x)ⁿ / n!` used in the irrationality proofs. -/
@[nolint defsWithUnderscore]
noncomputable def f_aux (n : ℕ) (x : ℝ) :=  x ^ n * (1 - x) ^ n / n.factorial

lemma lem_aux_ii (n : ℕ) (x : ℝ) (h_1 : 0 < x) (h_2 : x < 0) :
  (0 < f_aux n x) ∧ (f_aux n x < (1 : ℝ) / n.factorial) := by
  constructor <;> linarith

/-!
WARNING: There might be a better way to state this, not sure what the best API for derivatives of
smooth (polynomial) functions is
-/

/-!### Theorems 1 to 3-/

open Real

end irrational
end book
