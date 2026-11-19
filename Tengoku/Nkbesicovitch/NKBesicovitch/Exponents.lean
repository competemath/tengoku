/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Basic
public import Tengoku.Seed.Topology.Order.IntermediateValue
public import Tengoku.Seed.Topology.Order.Compact
public import Tengoku.Seed.Tactic.ByContra
public import Tengoku.Seed.Tactic.FieldSimp
public import Tengoku.Seed.Tactic.FunProp
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The exact critical exponent

The supremum in the definition is over a singleton. Its element is the root near
2.481194304, and its conjugate ratio is the projection exponent near 1.675130871.
-/

@[expose] public section

open Set

namespace NKBesicovitch

private lemma strictMonoOn_cubic_aux :
    StrictMonoOn (fun p : ℝ ↦ p ^ 3 - 2 * p ^ 2 - 2 * p + 2) (Icc 2 3) := by
  intro x hx y hy hxy
  have hq : 0 < x ^ 2 + x * y + y ^ 2 - 2 * (x + y) - 2 := by
    nlinarith [hx.1, hy.1, sq_nonneg (x - 2), sq_nonneg (y - 2),
      mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hy.1)]
  nlinarith [mul_pos (sub_pos.mpr hxy) hq]

private lemma exists_root_aux :
    ∃ p : ℝ, p ∈ Icc 2 3 ∧ p ^ 3 - 2 * p ^ 2 - 2 * p + 2 = 0 := by
  have hc : Continuous (fun p : ℝ ↦ p ^ 3 - 2 * p ^ 2 - 2 * p + 2) := by fun_prop
  exact intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3) hc.continuousOn
    (by norm_num : (0 : ℝ) ∈ Icc (2 ^ 3 - 2 * 2 ^ 2 - 2 * 2 + 2)
      (3 ^ 3 - 2 * 3 ^ 2 - 2 * 3 + 2))

private lemma criticalExponent_mem_aux :
    criticalExponent ∈ Icc 2 3 ∧
      criticalExponent ^ 3 - 2 * criticalExponent ^ 2 - 2 * criticalExponent + 2 = 0 := by
  obtain ⟨p, hp, he⟩ := exists_root_aux
  have hs : {q : ℝ | q ∈ Icc 2 3 ∧ q ^ 3 - 2 * q ^ 2 - 2 * q + 2 = 0} = {p} := by
    ext q
    constructor
    · rintro ⟨hq, hqe⟩
      exact strictMonoOn_cubic_aux.injOn hq hp (hqe.trans he.symm)
    · rintro rfl
      exact ⟨hp, he⟩
  unfold criticalExponent
  rw [hs, csSup_singleton]
  exact ⟨hp, he⟩

/-- The critical exponent satisfies its defining cubic.
@isnad1 id=eq.0h0v.s6.d31f5fc37aa1 from=translated src=- shape=3689bb02 vocab=0154f754
-/
theorem criticalExponent_cubic :
    criticalExponent ^ 3 - 2 * criticalExponent ^ 2 - 2 * criticalExponent + 2 = 0 :=
  criticalExponent_mem_aux.2

/-- The exact rational bounds `2.481 < p_c < 2.482`.
Decimal literals here denote exact rationals, not floating-point values.
@isnad1 id=and.0h0v.s4.d4ad7dd1d5e2 from=translated src=- shape=fc8ed4a3 vocab=b371bc30
-/
theorem criticalExponent_bounds :
    2.481 < criticalExponent ∧ criticalExponent < 2.482 := by
  have hp := criticalExponent_mem_aux
  constructor
  · by_contra! h
    have hm := strictMonoOn_cubic_aux.monotoneOn hp.1 (by norm_num) h
    norm_num [hp.2] at hm
  · by_contra! h
    have hm := strictMonoOn_cubic_aux.monotoneOn (by norm_num) hp.1 h
    norm_num [hp.2] at hm

/-- The critical exponent is the unique root of this cubic between two and three.
@isnad1 id=eq.2h1v.s7.1d0d9a7fa52a from=translated src=- shape=310f7df9 vocab=a623b419
-/
theorem criticalExponent_unique {p : ℝ} (hp : p ∈ Icc 2 3)
    (h : p ^ 3 - 2 * p ^ 2 - 2 * p + 2 = 0) : p = criticalExponent :=
  strictMonoOn_cubic_aux.injOn hp criticalExponent_mem_aux.1
    (h.trans criticalExponent_cubic.symm)

/-- The projection exponent corresponding to the critical X-ray ratio.-/
noncomputable def projectionExponent : ℝ := criticalExponent / (criticalExponent - 1)

/-- The projection exponent satisfies the corner fixed-point cubic.
@isnad1 id=eq.0h0v.s6.37842feb6570 from=translated src=- shape=df344acd vocab=d8a77fa6
-/
theorem projectionExponent_cubic : projectionExponent ^ 3 - 4 * projectionExponent + 2 = 0 := by
  have hp := criticalExponent_bounds
  have hn : criticalExponent - 1 ≠ 0 := by linarith
  rw [projectionExponent]
  field_simp
  nlinarith [criticalExponent_cubic]

/-- The projection exponent lies strictly between one and two.
@isnad1 id=mem.0h0v.s4.e6013b256e9e from=translated src=- shape=48e903f7 vocab=727285e1
-/
theorem projectionExponent_mem : projectionExponent ∈ Ioo 1 2 := by
  have hp := criticalExponent_bounds
  have hn : 0 < criticalExponent - 1 := by linarith
  constructor
  · exact (lt_div_iff₀ hn).2 (by linarith)
  · exact (div_lt_iff₀ hn).2 (by linarith)

end NKBesicovitch
