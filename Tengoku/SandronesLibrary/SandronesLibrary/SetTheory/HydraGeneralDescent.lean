/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.HydraOrdinalAssignment
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.OrdinalPowerBridge
import Tengoku.Seed.SetTheory.Ordinal.CantorNormalForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# SetTheory / HydraGeneralDescent —— 一般 Hydra 单步的序数下降

既有的 Hydra 下降链（`HydraOneLevelDescent` → `HydraSiblingDescent` →
`HydraParentSiblingDescent` → `HydraRightmostSpineDescent`）都只在「被砍的父分支在每一层都是最右孩子」
这一族证书上成立。本文件去掉这条限制：对**任意**合法 `Hydra.Step`（任意深度、头在其父内的任意位置、
任意左兄弟森林、任意阶段复制），结构序数赋值都严格下降。

关键在于换一个序数赋值。列表序求和 `forestOrdinal` 会让「头」的贡献 `ω^0 = 1` 被右侧无穷序数的后缀吸收，
所以一般位置砍头时它并不下降（本库旧赋值因此只能覆盖最右分支）。本文件改用**自然和**
（Hessenberg 和，`ordNadd`）：逐项系数相加的序数加法，它在每个自变量上严格单调，于是头项永远不被吸收。
mathlib 目前没有 `nadd`，因此这里用 `Ordinal.CNF.coeff`/`Ordinal.CNF.eval` 直接定义并证明所需的代数性质。

本文件**不**声称 Hydra 游戏终止（那需要把严格下降接到良基归纳上），也**不**改动任何已集成的
Goodstein／Hydra 状态文件；新增能力只在本文件内。
-/

namespace SandronesLibrary.SetTheory.HydraGeneralDescent

open SandronesLibrary.SetTheory
open SandronesLibrary.SetTheory.Ordinal
open SandronesLibrary.SetTheory.HydraOrdinalAssignment

universe u

noncomputable section

/-! ## 自然和（Hessenberg 和） -/

private theorem coeff_omega_lt (o e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 o e < Ordinal.omega0 := by
  by_cases h : e ∈ List.map Prod.fst (Ordinal.CNF Ordinal.omega0 o)
  · obtain ⟨⟨e', c⟩, hc, he'⟩ := List.mem_map.mp h
    subst he'
    rw [Ordinal.CNF.coeff_of_mem_CNF hc]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hc
  · rw [Ordinal.CNF.coeff_of_notMem_CNF h]
    exact Ordinal.omega0_pos

private theorem add_lt_omega0 {a b : Ordinal} (ha : a < Ordinal.omega0)
    (hb : b < Ordinal.omega0) : a + b < Ordinal.omega0 := by
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp ha
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
  rw [← Nat.cast_add]
  exact Ordinal.natCast_lt_omega0 (m + n)

/-- 序数的自然和（Hessenberg 和）：把两个序数的 Cantor 正规形系数逐项相加再求值。
它与普通序数加法不同，在每个自变量上严格单调，因此有限个 `ω`—幂项相加时不会互相吸收。
mathlib 目前没有 `nadd`，本定义用 `Ordinal.CNF.coeff` 的逐点加法给出，`Ordinal.CNF` 在此只是定义机制。-/
def ordNadd (a b : Ordinal) : Ordinal :=
  Ordinal.CNF.eval Ordinal.omega0
    (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b)

/-- Pointwise split of an ordinal-valued finitely supported function.  The
mathlib lemma `Finsupp.filter_add_filter_not` needs commutative coefficients, so
we prove the version for `Ordinal` coefficients directly.-/
private theorem filter_add_filter_not_eq (f : Ordinal →₀ Ordinal) (p : Ordinal → Prop)
    [DecidablePred p] :
    Finsupp.filter p f + Finsupp.filter (fun x => ¬ p x) f = f := by
  ext e
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : p e
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

/-- 自然和的右零元。
@isnad1 id=eq.0h1v.s3.843d0ea571e3 from=translated src=- shape=1fa26838 vocab=623decd8
-/
theorem ordNadd_zero_right (a : Ordinal) : ordNadd a 0 = a := by
  rw [ordNadd, Ordinal.CNF.coeff_zero_right, add_zero, Ordinal.CNF.eval_coeff]

/-- 自然和的左零元。
@isnad1 id=eq.0h1v.s3.dca0e0e61479 from=translated src=- shape=a60e91e3 vocab=623decd8
-/
theorem ordNadd_zero_left (b : Ordinal) : ordNadd 0 b = b := by
  rw [ordNadd, Ordinal.CNF.coeff_zero_right, zero_add, Ordinal.CNF.eval_coeff]

/-- 自然和可交换：系数都是有限序数，逐点转成自然数加法后交换。
@isnad1 id=eq.0h2v.s3.3d0fb54f6874 from=translated src=- shape=1013c0ce vocab=623decd8
-/
theorem ordNadd_comm (a b : Ordinal) : ordNadd a b = ordNadd b a := by
  have h : Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b =
      Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 a := by
    ext e
    rw [Finsupp.add_apply, Finsupp.add_apply]
    obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (coeff_omega_lt a e)
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (coeff_omega_lt b e)
    rw [hm, hn, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
  rw [ordNadd, ordNadd, h]

/-- 自然和可结合。
@isnad1 id=eq.0h3v.s4.4506368b18b6 from=translated src=- shape=b8c031c3 vocab=623decd8
-/
theorem ordNadd_assoc (a b c : Ordinal) :
    ordNadd (ordNadd a b) c = ordNadd a (ordNadd b c) := by
  have h₁ : Ordinal.CNF.coeff Ordinal.omega0 (ordNadd a b) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b := by
    rw [ordNadd, Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
      (fun e => add_lt_omega0 (coeff_omega_lt a e) (coeff_omega_lt b e))]
  have h₂ : Ordinal.CNF.coeff Ordinal.omega0 (ordNadd b c) =
      Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 c := by
    rw [ordNadd, Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
      (fun e => add_lt_omega0 (coeff_omega_lt b e) (coeff_omega_lt c e))]
  change Ordinal.CNF.eval Ordinal.omega0
      (Ordinal.CNF.coeff Ordinal.omega0 (ordNadd a b) + Ordinal.CNF.coeff Ordinal.omega0 c) =
    Ordinal.CNF.eval Ordinal.omega0
      (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 (ordNadd b c))
  rw [h₁, h₂, add_assoc]

/-! ### Splitting a coefficient function at one exponent -/

private def abovePart (e : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal →₀ Ordinal :=
  Finsupp.filter (fun e' => e < e') f

private def negAbovePart (e : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal →₀ Ordinal :=
  Finsupp.filter (fun e' => ¬ e < e') f

private def atPart (e : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal →₀ Ordinal :=
  Finsupp.filter (fun e' => e' = e) (negAbovePart e f)

private def belowPart (e : Ordinal) (f : Ordinal →₀ Ordinal) : Ordinal →₀ Ordinal :=
  Finsupp.filter (fun e' => ¬ e' = e) (negAbovePart e f)

private theorem mem_abovePart {e e' : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : e' ∈ (abovePart e f).support) : e < e' := by
  rw [abovePart, Finsupp.support_filter, Finset.mem_filter] at h
  exact h.2

private theorem mem_negAbovePart {e e' : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : e' ∈ (negAbovePart e f).support) : e' ≤ e := by
  rw [negAbovePart, Finsupp.support_filter, Finset.mem_filter] at h
  exact not_lt.mp h.2

private theorem mem_atPart {e e' : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : e' ∈ (atPart e f).support) : e' = e := by
  rw [atPart, Finsupp.support_filter, Finset.mem_filter] at h
  exact h.2

private theorem mem_belowPart {e e' : Ordinal} {f : Ordinal →₀ Ordinal}
    (h : e' ∈ (belowPart e f).support) : e' < e := by
  rw [belowPart, Finsupp.support_filter, Finset.mem_filter] at h
  exact lt_of_le_of_ne (mem_negAbovePart h.1) h.2

private theorem atPart_eq_single (e : Ordinal) (f : Ordinal →₀ Ordinal) :
    atPart e f = Finsupp.single e (f e) := by
  ext e'
  rw [atPart, Finsupp.filter_apply]
  by_cases h : e' = e
  · rw [h, ite_eq_left rfl, Finsupp.single_eq_same, negAbovePart, Finsupp.filter_apply,
      ite_eq_left (lt_irrefl e)]
  · rw [ite_eq_right h, Finsupp.single_eq_of_ne h]

private theorem abovePart_congr {f g : Ordinal →₀ Ordinal} {e : Ordinal}
    (h : ∀ e', e < e' → f e' = g e') : abovePart e f = abovePart e g := by
  ext e'
  rw [abovePart, abovePart, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases he : e < e'
  · rw [ite_eq_left he, ite_eq_left he, h e' he]
  · rw [ite_eq_right he, ite_eq_right he]

private theorem eval_belowPart_lt {f : Ordinal →₀ Ordinal}
    (hf : ∀ e, f e < Ordinal.omega0) (e : Ordinal) :
    Ordinal.CNF.eval Ordinal.omega0 (belowPart e f) < Ordinal.omega0 ^ e := by
  apply Ordinal.CNF.eval_lt
  · intro e'
    by_cases h : e' ∈ (belowPart e f).support
    · have hmem := h
      rw [belowPart, Finsupp.support_filter, Finset.mem_filter] at hmem
      rw [belowPart, Finsupp.filter_apply, ite_eq_left hmem.2, negAbovePart,
        Finsupp.filter_apply, ite_eq_left (not_lt.mpr (mem_negAbovePart hmem.1))]
      exact hf e'
    · rw [Finsupp.notMem_support_iff.mp h]
      exact Ordinal.omega0_pos
  · intro e' h'
    exact mem_belowPart h'

private theorem eval_eq_above_add_at_add_below {f : Ordinal →₀ Ordinal}
    (e : Ordinal) :
    Ordinal.CNF.eval Ordinal.omega0 f =
      Ordinal.CNF.eval Ordinal.omega0 (abovePart e f) +
        (Ordinal.omega0 ^ e * f e + Ordinal.CNF.eval Ordinal.omega0 (belowPart e f)) := by
  have hsplit : abovePart e f + negAbovePart e f = f := by
    rw [abovePart, negAbovePart]
    exact filter_add_filter_not_eq f (fun e' => e < e')
  have hsplit₂ : atPart e f + belowPart e f = negAbovePart e f := by
    rw [atPart, belowPart, negAbovePart]
    exact filter_add_filter_not_eq (negAbovePart e f) (fun e' => e' = e)
  have h₁ : Ordinal.CNF.eval Ordinal.omega0 f =
      Ordinal.CNF.eval Ordinal.omega0 (abovePart e f) +
        Ordinal.CNF.eval Ordinal.omega0 (negAbovePart e f) := by
    conv_lhs => rw [← hsplit]
    rw [Ordinal.CNF.eval_add]
    intro e₁ h₁ e₂ h₂
    exact le_trans (mem_negAbovePart h₂) (mem_abovePart h₁).le
  have h₂ : Ordinal.CNF.eval Ordinal.omega0 (negAbovePart e f) =
      Ordinal.CNF.eval Ordinal.omega0 (atPart e f) +
        Ordinal.CNF.eval Ordinal.omega0 (belowPart e f) := by
    conv_lhs => rw [← hsplit₂]
    rw [Ordinal.CNF.eval_add]
    intro e₁ h₁ e₂ h₂
    rw [mem_atPart h₁]
    exact (mem_belowPart h₂).le
  rw [h₁, h₂, atPart_eq_single, Ordinal.CNF.eval_single]

private theorem eval_lt_eval_of_agree_above {f g : Ordinal →₀ Ordinal}
    (hf : ∀ e, f e < Ordinal.omega0) (_hg : ∀ e, g e < Ordinal.omega0)
    {e : Ordinal} (he : ∀ e', e < e' → f e' = g e') (hlt : f e < g e) :
    Ordinal.CNF.eval Ordinal.omega0 f < Ordinal.CNF.eval Ordinal.omega0 g := by
  have hf' := eval_eq_above_add_at_add_below (f := f) e
  have hg' := eval_eq_above_add_at_add_below (f := g) e
  rw [hf', hg', abovePart_congr he]
  refine (add_lt_add_iff_left _).2 ?_
  calc Ordinal.omega0 ^ e * f e + Ordinal.CNF.eval Ordinal.omega0 (belowPart e f)
      < Ordinal.omega0 ^ e * f e + Ordinal.omega0 ^ e :=
        add_lt_add_right (eval_belowPart_lt hf e) _
    _ = Ordinal.omega0 ^ e * (f e + 1) := by rw [mul_add, mul_one]
    _ ≤ Ordinal.omega0 ^ e * g e := by
        apply mul_le_mul_right
        rw [← Order.succ_eq_add_one]
        exact Order.succ_le_iff.mpr hlt
    _ ≤ Ordinal.omega0 ^ e * g e + Ordinal.CNF.eval Ordinal.omega0 (belowPart e g) :=
        le_self_add

private theorem exists_agree_above_of_ne {f g : Ordinal →₀ Ordinal} (h : f ≠ g) :
    ∃ e, (∀ e', e < e' → f e' = g e') ∧ f e ≠ g e := by
  classical
  set s : Finset Ordinal := (f.support ∪ g.support).filter (fun e => f e ≠ g e) with hs_def
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hs_def] at hempty
    apply h
    ext e
    by_cases he : e ∈ f.support ∪ g.support
    · by_cases hdiff : f e = g e
      · exact hdiff
      · exact absurd (Finset.mem_filter.mpr ⟨he, hdiff⟩)
          (by rw [hempty]; exact Finset.notMem_empty e)
    · rw [Finset.notMem_union] at he
      rw [Finsupp.notMem_support_iff.mp he.1, Finsupp.notMem_support_iff.mp he.2]
  refine ⟨s.max' hs, ?_, ?_⟩
  · intro e' he'
    by_contra hdiff
    have hmem : e' ∈ s := by
      rw [hs_def]
      refine Finset.mem_filter.mpr ⟨?_, hdiff⟩
      by_cases hf : f e' = 0
      · rw [hf] at hdiff
        exact Finset.mem_union.mpr (Or.inr (Finsupp.mem_support_iff.mpr (Ne.symm hdiff)))
      · exact Finset.mem_union.mpr (Or.inl (Finsupp.mem_support_iff.mpr hf))
    exact absurd (Finset.le_max' s e' hmem) (not_le.mpr he')
  · have hmax := Finset.max'_mem s hs
    change s.max' hs ∈ (f.support ∪ g.support).filter (fun e => f e ≠ g e) at hmax
    exact (Finset.mem_filter.mp hmax).2

/-- 自然和在第二个自变量上严格单调（固定第一个自变量）。
@isnad1 id=lt.1h3v.s4.97647d2db8dd from=translated src=- shape=dc7ae3e3 vocab=ef735757
-/
theorem ordNadd_lt_ordNadd_right {a b c : Ordinal} (h : a < b) :
    ordNadd c a < ordNadd c b := by
  have hne : Ordinal.CNF.coeff Ordinal.omega0 a ≠ Ordinal.CNF.coeff Ordinal.omega0 b := by
    intro heq
    have hEq : a = b := by
      have := congrArg (Ordinal.CNF.eval Ordinal.omega0) heq
      rwa [Ordinal.CNF.eval_coeff, Ordinal.CNF.eval_coeff] at this
    exact absurd hEq h.ne
  obtain ⟨e, he, hdiff⟩ := exists_agree_above_of_ne hne
  have hlt' : Ordinal.CNF.coeff Ordinal.omega0 a e < Ordinal.CNF.coeff Ordinal.omega0 b e := by
    rcases lt_or_gt_of_ne hdiff with h' | h'
    · exact h'
    · have hcontra := eval_lt_eval_of_agree_above (coeff_omega_lt b) (coeff_omega_lt a)
        (fun e' hh => (he e' hh).symm) h'
      rw [Ordinal.CNF.eval_coeff, Ordinal.CNF.eval_coeff] at hcontra
      exact absurd hcontra (not_lt.mpr h.le)
  rw [ordNadd, ordNadd]
  refine eval_lt_eval_of_agree_above (e := e) ?_ ?_ ?_ ?_
  · intro e'
    exact add_lt_omega0 (coeff_omega_lt c e') (coeff_omega_lt a e')
  · intro e'
    exact add_lt_omega0 (coeff_omega_lt c e') (coeff_omega_lt b e')
  · intro e' he'
    rw [Finsupp.add_apply, Finsupp.add_apply, he e' he']
  · rw [Finsupp.add_apply, Finsupp.add_apply]
    exact add_lt_add_right hlt' _

/-- 自然和在第一个自变量上严格单调（固定第二个自变量）。
@isnad1 id=lt.1h3v.s4.30b2d7cd4938 from=translated src=- shape=11958600 vocab=ef735757
-/
theorem ordNadd_lt_ordNadd_left {a b c : Ordinal} (h : a < b) :
    ordNadd a c < ordNadd b c := by
  rw [ordNadd_comm a c, ordNadd_comm b c]
  exact ordNadd_lt_ordNadd_right h

private theorem coeff_omega_one :
    Ordinal.CNF.coeff Ordinal.omega0 (1 : Ordinal) = Finsupp.single 0 1 := by
  have h := Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0 (b := Ordinal.omega0)
    (f := Finsupp.single (0 : Ordinal) (1 : Ordinal)) (by
      intro e
      by_cases h : e = 0
      · subst h
        rw [Finsupp.single_eq_same]
        exact Ordinal.one_lt_omega0
      · rw [Finsupp.single_eq_of_ne h]
        exact Ordinal.omega0_pos)
  rwa [Ordinal.CNF.eval_single, Ordinal.opow_zero, one_mul] at h

/-- 自然和加一：`ordNadd a 1 = a + 1`，因为系数 `0` 是最小指数，`1` 永远排在末尾。
@isnad1 id=eq.0h1v.s4.c201c5c5774b from=translated src=- shape=c809089b vocab=fb5a5ae5
-/
theorem ordNadd_one (a : Ordinal) : ordNadd a 1 = a + 1 := by
  rw [ordNadd, coeff_omega_one, Ordinal.CNF.eval_add]
  · rw [Ordinal.CNF.eval_coeff, Ordinal.CNF.eval_single, Ordinal.opow_zero, one_mul]
  · intro e₁ _ e₂ he₂
    have hmem : (Finsupp.single (0 : Ordinal) (1 : Ordinal)) e₂ ≠ 0 :=
      Finsupp.mem_support_iff.mp he₂
    have hzero : e₂ = 0 := by
      by_contra h
      exact hmem (Finsupp.single_eq_of_ne h)
    subst hzero
    exact zero_le

/-! ## 一般序数度量与主定理 -/

mutual
  /-- 一般 Hydra 序数赋值：一个节点的值是其子森林的自然和赋值。-/
  noncomputable def hydraGeneralOrdinal : Hydra → Ordinal.{u}
    | .node children => forestGeneralOrdinal children

  /-- 有序森林的赋值：子节点贡献 `ω^(子节点值)`，用自然和累加。-/
  noncomputable def forestGeneralOrdinal : List Hydra → Ordinal.{u}
    | [] => 0
    | child :: rest =>
        ordNadd (ordinalPow Ordinal.omega0 (hydraGeneralOrdinal child))
          (forestGeneralOrdinal rest)
end

/--
@isnad1 id=eq.0h1v.s3.05f7579a6015 from=translated src=- shape=e3322fec vocab=74469973
-/
@[simp] theorem hydraGeneralOrdinal_node (children : List Hydra) :
    hydraGeneralOrdinal.{u} (.node children) = forestGeneralOrdinal.{u} children := rfl

/--
@isnad1 id=eq.0h2v.s4.5290f4790b4c from=translated src=- shape=059f3f86 vocab=a51ee91a
-/
@[simp] theorem forestGeneralOrdinal_cons (child : Hydra) (rest : List Hydra) :
    forestGeneralOrdinal.{u} (child :: rest) =
      ordNadd (ordinalPow Ordinal.omega0 (hydraGeneralOrdinal.{u} child))
        (forestGeneralOrdinal.{u} rest) := rfl

/--
@isnad1 id=eq.0h0v.s3.0a1640e4613c from=translated src=- shape=35225b15 vocab=78636bbd
-/
@[simp] theorem forestGeneralOrdinal_nil : forestGeneralOrdinal.{u} [] = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.5c1f724c1b65 from=translated src=- shape=b0ae1d2b vocab=eefbe7a7
-/
@[simp] theorem hydraGeneralOrdinal_head : hydraGeneralOrdinal.{u} Hydra.head = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.5cbb7c253af5 from=translated src=- shape=c63989eb vocab=5c877fb3
-/
theorem forestGeneralOrdinal_append (l₁ l₂ : List Hydra) :
    forestGeneralOrdinal.{u} (l₁ ++ l₂) =
      ordNadd (forestGeneralOrdinal.{u} l₁) (forestGeneralOrdinal.{u} l₂) := by
  induction l₁ with
  | nil => rw [List.nil_append]; exact (ordNadd_zero_left _).symm
  | cons c l₁ ih =>
      rw [List.cons_append, forestGeneralOrdinal_cons, ih, forestGeneralOrdinal_cons,
        ← ordNadd_assoc]

/-- Removing a head from a forest strictly decreases its measure, at an
arbitrary position.
@isnad1 id=lt.0h2v.s5.0c3fd8ef938c from=translated src=- shape=7940c130 vocab=5624b9a1
-/
theorem forestGeneralOrdinal_remove_head (L R : List Hydra) :
    forestGeneralOrdinal.{u} (L ++ R) <
      forestGeneralOrdinal.{u} (L ++ Hydra.head :: R) := by
  rw [forestGeneralOrdinal_append, forestGeneralOrdinal_append,
    forestGeneralOrdinal_cons, hydraGeneralOrdinal_head, ordinalPow_zero,
    ordNadd_comm (1 : Ordinal.{u}), ordNadd_one]
  exact ordNadd_lt_ordNadd_right (lt_add_one _)

/-! ### Combinatorial helpers -/

/-! ### Shape lemmas for `chop` -/

/-! ### The general descent theorem -/

end
end SandronesLibrary.SetTheory.HydraGeneralDescent
