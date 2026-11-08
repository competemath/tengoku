module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.ControlledProcess

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two separated environments MAIS-O33's candidate turns on

`AISafetyAtlas.Causal.ControlledProcess` renders MAIS-A2's environment. This
module runs it on the pair MAIS issue
[#9](https://github.com/lionellevine/MAIS/issues/9) constructs, and checks the
arithmetic the candidate's impossibility step rests on.

Two kernels on `m + 2` states and two actions agree everywhere except the row
`(0, 0)`, where one sends mass `1/10` to state `1` and spreads `9/10` over the
rest, and the other does the reverse. Then:

* every entry is positive, so both are **communicating** — the condition print
  imposes, obtained here in one step;
* the two are `4/5` apart at `(0, 0, 1)`, which is the separation;
* at `n = 101` and `δ = 1/2` the reconstruction radius is `2/√50`, and
  `2 · 2/√50 < 4/5`, so the two required balls are **disjoint**.

## Why `δ = 1/2` and not `δ = 0`

The candidate takes `δ = 0`, which makes its agents exactly optimal and forces
an optimal-policy-existence theorem for reachability on a finite process —
absent from Mathlib, and the largest single dependency in the layer. Print
admits any `δ ∈ [0,1)` with `(n-1)(1-δ) > 4`, and `radius_admissible_at_101_half`
records that `δ = 1/2` at `n = 101` is admissible while
`balls_disjoint_at_101_half` records that the separation still works there. At
`δ > 0` the bounded agents can be built by approximating the supremum rather
than attaining it. See `docs/provenance/mais-o33-statability.md`.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.ControlledProcess

open AISafetyAtlas.Causal

/-! ## The pair -/

/-- The kernel: uniform everywhere except the row `(0, 0)`, where mass `p` goes
to state `1` and `1 - p` is spread over the other `m + 1` states.-/
@[expose] public noncomputable def kern (m : ℕ) (p : ℝ) :
    Fin (m + 2) → Fin 2 → Fin (m + 2) → ℝ :=
  fun s a s' ↦
    if s = 0 ∧ a = 0 then (if s' = 1 then p else (1 - p) / (m + 1))
    else 1 / (m + 2)

/-- The controlled Markov process it defines, for any `p` strictly between zero
and one.-/
@[expose] public noncomputable def env (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) where
  prob := kern m p
  prob_nonneg := by
    intro s a s'
    unfold kern
    have hm : (0 : ℝ) < m + 1 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    split_ifs
    · exact hp0.le
    · positivity
    · positivity
  prob_sum := by
    intro s a
    unfold kern
    by_cases h : s = 0 ∧ a = 0
    · simp only [ite_eq_left h]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Fin (m + 2)))]
      have hc : ∀ s' ∈ (Finset.univ : Finset (Fin (m + 2))).erase 1,
          (if s' = 1 then p else (1 - p) / (m + 1)) = (1 - p) / (m + 1) := by
        intro s' hs'
        rw [ite_eq_right (Finset.ne_of_mem_erase hs')]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, ite_eq_left rfl,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      have hcast : ((m + 2 - 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        push_cast [Nat.add_sub_cancel]
        ring
      rw [hcast]
      field_simp
      ring
    · simp only [ite_eq_right h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp

/-- The first world: `P⁰(1 ∣ 0, 0) = 1/10`.-/
@[expose] public noncomputable def env0 (m : ℕ) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) :=
  env m (1 / 10) (by norm_num) (by norm_num)

/-- The second world: `P¹(1 ∣ 0, 0) = 9/10`.-/
@[expose] public noncomputable def env1 (m : ℕ) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) :=
  env m (9 / 10) (by norm_num) (by norm_num)

/-! ## The reconstruction radius at `n = 101`, `δ = 1/2` -/

end AISafetyAtlas.Examples.Causal.ControlledProcess
