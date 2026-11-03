/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RecursionStepNeg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — the recursion state of the Puiseux root construction

To iterate the Puiseux construction we package the per-step invariant into a `RecState`: a
polynomial `Q` together with an odd `mult` such that `o(Q.coeff mult) = 0`, `o(Q.coeff i) > 0` for
`i < mult`, and `o(Q.coeff i) ≥ 0` for all `i` — exactly the order structure produced by Lemma
2.95. From `P` (odd degree, nonzero constant term) the first step bootstraps into a `RecState`
(`exists_initial_RecState`); from a `RecState` with nonzero constant term the negative-slope step
produces the next one with non-increasing multiplicity and `β > 0` (`RecState.exists_next`). The
barrier is `Q.coeff 0 = 0`. -/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R]

/-- **A valid recursion state**: a recentered polynomial `poly` with the order structure of Lemma
2.95 for the odd multiplicity `mult`.-/
structure RecState (R : Type*) [Field R] where
  /-- The current (recentered) polynomial `Pᵢ`.-/
  poly : Polynomial (PuiseuxSeries R)
  /-- The current multiplicity `rᵢ` (odd, non-increasing along the recursion).-/
  mult : ℕ
  /-- `rᵢ` is odd.-/
  odd_mult : Odd mult
  /-- Column `rᵢ` is at height `0`: `o(b_{rᵢ}) = 0`.-/
  coeff_mult_order : puiseuxOrder R (poly.coeff mult) = (0 : WithTop ℚ)
  /-- Columns below `rᵢ` are strictly positive: `o(b_i) > 0` for `i < rᵢ`.-/
  coeff_lt_order : ∀ i, i < mult → 0 < puiseuxOrder R (poly.coeff i)
  /-- All columns are nonnegative: `o(b_i) ≥ 0`.-/
  coeff_ge_order : ∀ i, (0 : WithTop ℚ) ≤ puiseuxOrder R (poly.coeff i)

variable [IsRealClosed R]

/-- **One continuation step.** From a valid state with nonzero constant term, the negative-slope
step produces the next valid state, with non-increasing multiplicity, `β > 0`, and the order jump
`o(Pᵢ(ε^ξ(x + y))) > β`.
@isnad1 id=ex.1h2v.s13.d78c78f80bf5 from=translated src=- shape=9ea390d3 vocab=dce9834d
-/
theorem RecState.exists_next (s : RecState R) (h0 : s.poly.coeff 0 ≠ 0) :
    ∃ (x : R) (ξ β : ℚ) (A B : ℕ × ℚ) (s' : RecState R),
      x ≠ 0 ∧ s'.mult ≤ s.mult ∧ 0 < β ∧ 0 < ξ ∧ s'.poly = substPoly s.poly x ξ β ∧
      A.1 < B.1 ∧ B.1 ≤ s.mult ∧
      puiseuxOrder R (s.poly.coeff A.1) = (A.2 : WithTop ℚ) ∧
      puiseuxOrder R (s.poly.coeff B.1) = (B.2 : WithTop ℚ) ∧
      ξ = -(newtonSlope A B) ∧ β = A.2 + (A.1 : ℚ) * ξ ∧
      s'.mult = (charPoly s.poly A B).rootMultiplicity x ∧
      (∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
        (β : WithTop ℚ) <
          puiseuxOrder R (s.poly.eval (puiseuxMonomial ξ * (constPuiseux x + y)))) := by
  obtain ⟨x, ξ, β, A, B, hx0, hABlt, hBr, hβpos, hξpos, hcolA, hcolB, hξeq, hβeq, hodd', hrle, ha1,
      ha2, ha3, hb⟩ :=
    recursion_step_neg s.odd_mult h0 s.coeff_mult_order s.coeff_lt_order s.coeff_ge_order
  exact ⟨x, ξ, β, A, B,
    { poly := substPoly s.poly x ξ β, mult := (charPoly s.poly A B).rootMultiplicity x,
      odd_mult := hodd', coeff_mult_order := ha3, coeff_lt_order := ha2, coeff_ge_order := ha1 },
    hx0, hrle, hβpos, hξpos, rfl, hABlt, hBr, hcolA, hcolB, hξeq, hβeq, rfl, hb⟩

/-- Bundled output of one continuation step: the new root coefficient `x`, exponent increment `ξ`,
order increment `β`, the chosen edge `edgeA edgeB`, the next state, and the step's properties.-/
structure StepResult (s : RecState R) where
  x : R
  xi : ℚ
  beta : ℚ
  edgeA : ℕ × ℚ
  edgeB : ℕ × ℚ
  next : RecState R
  x_ne : x ≠ 0
  mult_le : next.mult ≤ s.mult
  beta_pos : 0 < beta
  xi_pos : 0 < xi
  next_poly : next.poly = substPoly s.poly x xi beta
  edge_lt : edgeA.1 < edgeB.1
  edge_le : edgeB.1 ≤ s.mult
  colA : puiseuxOrder R (s.poly.coeff edgeA.1) = (edgeA.2 : WithTop ℚ)
  colB : puiseuxOrder R (s.poly.coeff edgeB.1) = (edgeB.2 : WithTop ℚ)
  xi_eq : xi = -(newtonSlope edgeA edgeB)
  beta_eq : beta = edgeA.2 + (edgeA.1 : ℚ) * xi
  next_mult_eq : next.mult = (charPoly s.poly edgeA edgeB).rootMultiplicity x
  order_jump : ∀ y : PuiseuxSeries R, 0 < puiseuxOrder R y →
    (beta : WithTop ℚ) <
      puiseuxOrder R (s.poly.eval (puiseuxMonomial xi * (constPuiseux x + y)))

/--
@isnad1 id=nonempty.1h2v.s10.bb8de172054d from=translated src=- shape=3952698b vocab=42cd5c16
-/
theorem RecState.nonempty_stepResult (s : RecState R) (h0 : s.poly.coeff 0 ≠ 0) :
    Nonempty (StepResult s) := by
  obtain ⟨x, ξ, β, A, B, s', hx0, hrle, hβpos, hξpos, hpoly, hABlt, hBr, hcolA, hcolB, hξeq, hβeq,
    hmeq, hb⟩ := s.exists_next h0
  exact ⟨⟨x, ξ, β, A, B, s', hx0, hrle, hβpos, hξpos, hpoly, hABlt, hBr, hcolA, hcolB, hξeq, hβeq,
    hmeq, hb⟩⟩

open Classical in
/-- One step of the recursion as a total function: at the barrier `coeff 0 = 0` it returns junk and
freezes the state; otherwise it returns a chosen `StepResult`'s data and next state.-/
noncomputable def RecState.step (s : RecState R) : R × ℚ × ℚ × RecState R :=
  if h : s.poly.coeff 0 = 0 then (0, 0, 0, s)
  else
    let sr := Classical.choice (s.nonempty_stepResult h)
    (sr.x, sr.xi, sr.beta, sr.next)

/-- Away from the barrier, `step` returns the data of a genuine `StepResult`.
@isnad1 id=ex.1h2v.s10.39c5eaa6e960 from=translated src=- shape=8498af45 vocab=2137c824
-/
theorem RecState.step_spec (s : RecState R) (h : s.poly.coeff 0 ≠ 0) :
    ∃ sr : StepResult s, s.step = (sr.x, sr.xi, sr.beta, sr.next) :=
  ⟨Classical.choice (s.nonempty_stepResult h), by rw [RecState.step, dite_eq_right h]⟩

/--
@isnad1 id=eq.1h2v.s10.5f2caab6922e from=translated src=- shape=dec8ab1c vocab=dd178d59
-/
@[simp] theorem RecState.step_barrier (s : RecState R) (h : s.poly.coeff 0 = 0) :
    s.step = (0, 0, 0, s) := by rw [RecState.step, dite_eq_left h]

/-- The multiplicity is non-increasing under `step` (it freezes at the barrier).
@isnad1 id=le.0h2v.s5.5b7dffe49a12 from=translated src=- shape=cebe2a32 vocab=036a9c97
-/
theorem RecState.step_mult_le (s : RecState R) : (s.step).2.2.2.mult ≤ s.mult := by
  by_cases h : s.poly.coeff 0 = 0
  · rw [RecState.step_barrier s h]
  · obtain ⟨sr, hsr⟩ := s.step_spec h
    rw [hsr]; exact sr.mult_le

/-- **The state sequence.** Iterating `step` from an initial state.-/
noncomputable def stateSeq (s0 : RecState R) : ℕ → RecState R
  | 0 => s0
  | n + 1 => ((stateSeq s0 n).step).2.2.2

/-- The `n`-th root coefficient `x_{n+1}` produced going from state `n` to state `n+1`.-/
noncomputable def xSeq (s0 : RecState R) (n : ℕ) : R := ((stateSeq s0 n).step).1

/-- The `n`-th exponent increment `ξ_{n+1}`.-/
noncomputable def xiSeq (s0 : RecState R) (n : ℕ) : ℚ := ((stateSeq s0 n).step).2.1

/-- The `n`-th order increment `β_{n+1}`.-/
noncomputable def betaSeq (s0 : RecState R) (n : ℕ) : ℚ := ((stateSeq s0 n).step).2.2.1

/-- The multiplicity is non-increasing along the state sequence.
@isnad1 id=antitone.0h2v.s4.f89db3db4b84 from=translated src=- shape=f62ce331 vocab=915fc8fd
-/
theorem stateSeq_mult_antitone (s0 : RecState R) : Antitone (fun n => (stateSeq s0 n).mult) := by
  apply antitone_nat_of_succ_le
  intro n
  show (stateSeq s0 (n + 1)).mult ≤ (stateSeq s0 n).mult
  exact RecState.step_mult_le _

/-- Away from the barrier, the step's exponent increment `ξ` is positive.
@isnad1 id=lt.1h2v.s10.8f5b0d0adaea from=translated src=- shape=55d7f72c vocab=e9aa882f
-/
theorem RecState.step_xi_pos (s : RecState R) (h : s.poly.coeff 0 ≠ 0) : 0 < (s.step).2.1 := by
  obtain ⟨sr, hsr⟩ := s.step_spec h
  rw [hsr]; exact sr.xi_pos

/-- Under the never-barrier hypothesis, every exponent increment `ξₙ` is positive.
@isnad1 id=lt.1h3v.s10.e4069b010a2f from=translated src=- shape=566222bd vocab=5dedd637
-/
theorem xiSeq_pos (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (n : ℕ) :
    0 < xiSeq s0 n := (stateSeq s0 n).step_xi_pos (hnb n)

/-- An antitone `ℕ → ℕ` sequence is eventually constant.
@isnad1 id=ex.1h1v.s4.60112060844f from=translated src=- shape=911d4a9c vocab=a4758b81
-/
theorem antitone_nat_eventually_const {f : ℕ → ℕ} (hf : Antitone f) :
    ∃ N, ∀ n, N ≤ n → f n = f N := by
  obtain ⟨N, hN⟩ := Nat.sInf_mem (Set.range_nonempty f)
  exact ⟨N, fun n hn => le_antisymm (hf hn) (by rw [hN]; exact Nat.sInf_le ⟨n, rfl⟩)⟩

/-- **The multiplicity stabilizes.** Eventually `(stateSeq s0 n).mult` is a constant value `r`.
@isnad1 id=ex.0h2v.s5.2690234fe421 from=translated src=- shape=ae6b14df vocab=9e38b0eb
-/
theorem stateSeq_mult_eventually_const (s0 : RecState R) :
    ∃ N, ∀ n, N ≤ n → (stateSeq s0 n).mult = (stateSeq s0 N).mult :=
  antitone_nat_eventually_const (stateSeq_mult_antitone s0)

end Azurite.BPR
