/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Tengoku.Complexitylib.Complexitylib.Asymptotics

/-!
# Polynomial bounds on natural-number functions

`PolyBound f` says `f` is dominated pointwise (at every argument, not merely
eventually) by the evaluation of a natural polynomial. Resource bookkeeping
assembles time and space bounds by addition, multiplication, and monotonicity,
so an everywhere-bound closed under those operations is easier to carry through
a construction than a big-O statement; `PolyBound.bigO` converts to the big-O
form the complexity classes are stated in.

## Main results

- `PolyBound` — pointwise domination by a natural polynomial
- `PolyBound.const`, `.id`, `.add`, `.mul`, `.pow`, `.mono`, `.max`, `.eval` —
  the closure API
- `PolyBound.bigO` — a polynomial bound is a big-O power bound
- `PolyBound.exists_mul_pow_bound` — a polynomial bound is an `A * (n + 1) ^ B` bound
-/

@[expose] public section

namespace Complexity

/-- Pointwise domination by the evaluation of a natural polynomial. -/
def PolyBound (f : ℕ → ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ inputLength, f inputLength ≤ p.eval inputLength

namespace PolyBound

/--
@isnad1 id=polyboun.0h1v.s2.26dc4ef9f097 from=translated src=- shape=2c1a380c vocab=eae63a5f
-/
theorem const (value : ℕ) : PolyBound (fun _ => value) :=
  ⟨Polynomial.C value, fun _ => by simp⟩

/--
@isnad1 id=polyboun.0h0v.s2.d7c3efc959e4 from=translated src=- shape=8895caae vocab=eae63a5f
-/
theorem id : PolyBound (fun inputLength => inputLength) :=
  ⟨Polynomial.X, fun _ => by simp⟩

/--
@isnad1 id=polyboun.2h2v.s4.e3a9ebb516c6 from=translated src=- shape=b27ebcba vocab=926957c9
-/
theorem add {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength + g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun inputLength => by
    rw [Polynomial.eval_add]
    exact Nat.add_le_add (hp inputLength) (hq inputLength)⟩

/--
@isnad1 id=polyboun.2h2v.s4.bc80d1735019 from=translated src=- shape=b27ebcba vocab=18a28dc0
-/
theorem mul {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => f inputLength * g inputLength) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun inputLength => by
    rw [Polynomial.eval_mul]
    exact Nat.mul_le_mul (hp inputLength) (hq inputLength)⟩

/--
@isnad1 id=polyboun.2h2v.s4.f83bdc7e2040 from=translated src=- shape=f32819e2 vocab=29c574e8
-/
theorem mono {f g : ℕ → ℕ} (hg : PolyBound g)
    (hle : ∀ inputLength, f inputLength ≤ g inputLength) : PolyBound f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun inputLength => le_trans (hle inputLength) (hp inputLength)⟩

/--
@isnad1 id=polyboun.2h2v.s4.5f231a9df6ea from=translated src=- shape=bc5bb26e vocab=e7506c20
-/
theorem max {f g : ℕ → ℕ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun inputLength => max (f inputLength) (g inputLength)) :=
  (hf.add hg).mono fun _ => Nat.max_le.mpr
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/--
@isnad1 id=polyboun.0h1v.s3.6bc20ae225b7 from=translated src=- shape=35b88f3a vocab=774aafbd
-/
theorem eval (p : Polynomial ℕ) :
    PolyBound (fun inputLength => p.eval inputLength) :=
  ⟨p, fun _ => le_rfl⟩

/--
@isnad1 id=polyboun.1h2v.s4.4035f146604f from=translated src=- shape=c82ddb5d vocab=03b0dce5
-/
theorem pow {f : ℕ → ℕ} (hf : PolyBound f) (exponent : ℕ) :
    PolyBound (fun inputLength => f inputLength ^ exponent) := by
  induction exponent with
  | zero => simpa using const 1
  | succ exponent ih => simpa [pow_succ] using ih.mul hf

/-- A polynomial bound is a big-O bound by the polynomial's degree.
@isnad1 id=ex.1h1v.s4.1862e691abaf from=translated src=- shape=08b05759 vocab=f28cbbb3
-/
theorem bigO {f : ℕ → ℕ} (hf : PolyBound f) : ∃ d, f =O (· ^ d) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.natDegree, BigO.of_polynomial_bound p hp⟩

/-- A polynomial bound is a bound of the form `A * (n + 1) ^ B`: take `A` to be
the sum of the coefficients and `B` the degree.
@isnad1 id=ex.1h1v.s5.6c5be2c1d0dd from=translated src=- shape=2d07d60c vocab=0c8c7207
-/
theorem exists_mul_pow_bound {f : ℕ → ℕ} (hf : PolyBound f) :
    ∃ A B : ℕ, ∀ n, f n ≤ A * (n + 1) ^ B := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, p.natDegree, fun n => ?_⟩
  refine le_trans (hp n) ?_
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := by
    rw [Finset.mem_range] at hi
    omega
  exact Nat.mul_le_mul_left _
    (le_trans (Nat.pow_le_pow_left (by omega) i) (Nat.pow_le_pow_right (by omega) hi'))

end PolyBound

end Complexity
