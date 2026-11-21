/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku

/-!
TODOs:
  * General proof cleanup
  * Upstreaming
-/

-- TOOD: Add IsBotZeroClass X.IdealSheafData ? (See if it makes proofs easier.  Otherwise don't.)
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
@[implicit_reducible]
noncomputable
def OrderIso.conditionallyCompleteLinearOrder {α β : Type*} [ConditionallyCompleteLinearOrder β]
  [PartialOrder α] (e : α ≃o β) : ConditionallyCompleteLinearOrder α where
  sup a b := e.symm (e a ⊔ e b)
  inf a b := e.symm (e a ⊓ e b)
  le_sup_left a b := by grw [le_symm_apply, le_sup_left (a := e a)]
  le_sup_right a b := by grw [le_symm_apply, le_sup_right (b := e b)]
  sup_le a b c hab hbc := by
    rw [← e.le_iff_le] at hab hbc
    grw [symm_apply_le, sup_le hab hbc]
  inf_le_left a b := by grw [symm_apply_le, inf_le_left]
  inf_le_right a b := by grw [symm_apply_le, inf_le_right]
  le_inf a b c hab hbc := by
    rw [← e.le_iff_le] at hab hbc
    grw [le_symm_apply, le_inf hab hbc]
  sSup s := e.symm (sSup (e '' s))
  sInf s := e.symm (sInf (e '' s))
  isLUB_csSup s hsne hsbdd := by
    conv_lhs => rw [← show e.symm '' e '' s = s by simp]
    refine e.symm.leftOrdContinuous (by simp [hsne]) ?_
    exact isLUB_csSup (by simp [hsne]) (by simp [hsbdd])
  isGLB_csInf s hsne hsbdd := by
    conv_lhs => rw [← show e.symm '' e '' s = s by simp]
    refine e.symm.rightOrdContinuous (by simp [hsne]) ?_
    exact isGLB_csInf (by simp [hsne]) (by simp [hsbdd])
  le_total a b := by
    rw [← e.le_iff_le, ← e.le_iff_le]
    exact le_total _ _
  toDecidableLE := Classical.decRel LE.le
  csSup_of_not_bddAbove s hs := by simp [csSup_of_not_bddAbove, hs]
  csInf_of_not_bddBelow s hs := by simp [csInf_of_not_bddBelow, hs]

/--
@isnad1 id=iff.0h1v.s6.cd992f0b9bcf from=translated src=- shape=bb544786 vocab=243571ae
-/
theorem _root_.Tengoku.LeanTnorms.isReduced_iff_noZeroDivisors {M : Type*} [MonoidWithZero M]
    [LinearOrder M] [MulLeftMono M] [MulRightMono M] [IsBotZeroClass M] :
    IsReduced M ↔ NoZeroDivisors M := by
  refine ⟨fun h ↦ NoZeroDivisors.mk ?_, fun h ↦ isReduced_of_noZeroDivisors⟩
  intro p q hpq
  rw [← min_eq_zero]
  rw [isReduced_iff] at h
  refine h _ ?_
  use 2
  rw [pow_two, ← le_zero_iff, ← hpq]
  exact mul_le_mul' (min_le_left _ _) (min_le_right _ _)

instance {M : Type*} [PartialOrder M] [MonoidWithZero M]
    [PosMulStrictMono M] [IsBotZeroClass M] : IsReduced M := by
  rw [isReduced_iff]
  intro x
  contrapose!
  simp only [ne_eq, ← pos_iff_ne_zero, IsNilpotent, not_exists]
  intro hx n
  exact pow_pos hx n

variable {α : Type*}

section MulMono

variable [Preorder α] [Zero α] [Mul α]

/--
@isnad1 id=mulleftm.0h1v.s4.a896046857e7 from=translated src=- shape=fb04960b vocab=486fcf4a
-/
theorem PosMulMono.toMulLeftMono [IsBotZeroClass α] [PosMulMono α] : MulLeftMono α where
  elim _ _ _ h := mul_le_mul_of_nonneg_left h zero_le

/--
@isnad1 id=iff.0h1v.s4.eb41dc64852d from=translated src=- shape=6c04fe61 vocab=486fcf4a
-/
theorem PosMulMono.mulLeftMono_iff_posMulMono [IsBotZeroClass α] :
    MulLeftMono α ↔ PosMulMono α := ⟨fun _ ↦ inferInstance, fun h ↦ h.toMulLeftMono⟩

/--
@isnad1 id=mulright.0h1v.s4.f7489c92c230 from=translated src=- shape=fb04960b vocab=f08693a9
-/
theorem MulPosMono.toMulRightMono [IsBotZeroClass α] [MulPosMono α] : MulRightMono α where
  elim _ _ _ h := mul_le_mul_of_nonneg_right h zero_le

/--
@isnad1 id=iff.0h1v.s4.6e5d33edf6fb from=translated src=- shape=6c04fe61 vocab=f08693a9
-/
theorem MulPosMono.mulRightMono_iff_mulPosMono [IsBotZeroClass α] :
    MulRightMono α ↔ MulPosMono α := ⟨fun _ ↦ inferInstance, fun h ↦ h.toMulRightMono⟩

end MulMono

section SemilatticeInf
variable [SemilatticeInf α] [One α] [IsBotOneClass α]

/--
@isnad1 id=eq.0h2v.s5.eeb5a3a86a4b from=translated src=- shape=6a5d68bb vocab=8cf11148
-/
@[to_additive]
theorem _root_.Tengoku.LeanTnorms.one_inf (a : α) : 1 ⊓ a = 1 := by simp

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup α] [One α] [IsBotOneClass α]

/--
@isnad1 id=eq.0h2v.s5.28572ddc9fa6 from=translated src=- shape=4c2340e7 vocab=8dddef5d
-/
@[to_additive]
theorem _root_.Tengoku.LeanTnorms.one_sup (a : α) : 1 ⊔ a = a := by simp

/--
@isnad1 id=iff.0h3v.s5.dca5084936bc from=translated src=- shape=cc849372 vocab=8dddef5d
-/
@[to_additive (attr := simp)]
theorem _root_.Tengoku.LeanTnorms.sup_eq_one {a b : α} : a ⊔ b = 1 ↔ a = 1 ∧ b = 1 :=
  let := IsBotOneClass.toOrderBot α
  sup_eq_bot_iff

end SemilatticeSup

/--
@isnad1 id=eq.1h2v.s5.6e010c2d4b04 from=translated src=- shape=1f57bda4 vocab=94e268da
-/
lemma Int.toNat_mul' {a b : ℤ} (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
  by_cases! ha : 0 ≤ a
  · exact Int.toNat_mul ha hb
  · simp only [Int.toNat_of_nonpos (le_of_lt ha), zero_mul, Int.toNat_eq_zero]
    exact Int.mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) hb

-- there might be a better way to do this
/--
@isnad1 id=le.2h3v.s5.195841ff6ff5 from=translated src=- shape=b4343e4a vocab=4a7c8f8e
-/
lemma _root_.Tengoku.LeanTnorms.comp_self_subset {α : Type*} [UniformSpace α] {U V : Set (α × α)}
    (hVU : SetRel.comp V V ⊆ U) (hV : V ∈ uniformity α) : V ⊆ U := by
  intro x hx
  refine hVU ?_
  rw [SetRel.mem_comp]
  use x.1
  simp [hx, refl_mem_uniformity hV]

/--
@isnad1 id=continuo.2h3v.s6.a44780c3474a from=translated src=- shape=883f580f vocab=20b469bb
-/
theorem Antitone.continuous_of_surjective {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [DenselyOrdered β] {f : α → β} (h_anti : Antitone f) (h_surj : Function.Surjective f) :
    Continuous f := by
  have h_mono := Antitone.dual_right h_anti
  have h_surj' := Function.Surjective.comp (Equiv.surjective OrderDual.toDual) h_surj
  apply Monotone.continuous_of_surjective h_mono at h_surj'
  exact (continuous_congr (congrFun rfl)).mp h_surj'

/--
@isnad1 id=isnilpot.3h3v.s6.aae3e4a37a9e from=translated src=- shape=9809e273 vocab=c9ee4665
-/
lemma _root_.Tengoku.LeanTnorms.isNilpotent_monotone {R : Type*} [CommMonoidWithZero R] [PartialOrder R]
    [IsOrderedMonoid R]
    {x y : R} (hx0 : 0 ≤ x) (h : x ≤ y) (hy : IsNilpotent y) :
    IsNilpotent x := by
  obtain ⟨n, hy⟩ := hy
  use n
  by_cases! hn : n = 0
  · simp_all
  refine le_antisymm ?_ ?_
  · rw [← hy]
    exact pow_left_mono n h
  · rw [← show 0 ^ n = (0 : R) by rw [zero_pow hn]]
    exact pow_left_mono n hx0

-- Do these really belong in Mathlib?

/--
@isnad1 id=not.1h3v.s5.fcd4d3c1a062 from=translated src=- shape=c73de50a vocab=df0a4a47
-/
lemma _root_.Tengoku.LeanTnorms.notMem_of_sSup_lt {α : Type*} [CompleteLattice α] {x : α} {s : Set α} (h : sSup s < x) :
    x ∉ s := notMem_of_csSup_lt h <| OrderTop.bddAbove s

private noncomputable
def φ {P : ℕ → ℕ → Prop} (hn : ∀ N, ∃ m > N, ∀ n ≤ N, P m n) : ℕ → ℕ :=
  fun n ↦ match n with
    | Nat.zero => 0
    | N + 1 => Classical.choose (hn (φ hn N))

variable {X : Type*} [MetricSpace X]

/--
@isnad1 id=ex.2h3v.s6.b0a1b415929c from=translated src=- shape=ec0aca35 vocab=a0d3bfdf
-/
lemma _root_.Tengoku.LeanTnorms.refine_seq_uniformity (x : ℕ → X) (y : X)
    (hx : Filter.Tendsto x Filter.atTop (nhds y))
    (hxy : ∀ n, x n ≠ y) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (fun n ↦ dist (x (φ n)) y) := by
  have hn : ∀ N, ∃ m > N, ∀ n ≤ N, dist (x m) y < dist (x n) y := by
    intro N
    rw [tendsto_iff_dist_tendsto_zero, tendsto_order] at hx
    apply And.right at hx
    let ε : ℝ := sInf {dist (x n) y | n ≤ N}
    have he : ε > 0 := by
      rw [gt_iff_lt, Set.Finite.lt_csInf_iff]
      · simp
        grind
      · let f : ℕ → ℝ := fun n ↦ dist (x n) y
        refine Set.Finite.of_surjOn f ?_ <| Set.finite_le_nat N
        intro d
        grind
      · use dist (x 0) y
        grind
    specialize hx ε he
    simp only [Filter.eventually_atTop] at hx
    obtain ⟨m, hm⟩ := hx
    specialize hm (max m (N + 1)) (by grind)
    use max m (N + 1)
    constructor
    · grind
    intro n hn
    refine lt_of_lt_of_le hm ?_
    refine csInf_le ?_ ?_
    · rw [bddBelow_def]
      use 0
      grind [dist_nonneg]
    · grind
  use φ hn
  constructor
  · refine strictMono_nat_of_lt_succ ?_
    intro m
    simp [φ, (Classical.choose_spec (hn (φ hn m))).1]
  · refine strictAnti_nat_of_succ_lt ?_
    intro m
    simp [φ, (Classical.choose_spec (hn (φ hn m))).2 (φ hn m) (by rfl)]

/--
@isnad1 id=ex.4h2v.s7.5cff4d336975 from=translated src=- shape=224da110 vocab=03198539
-/
lemma IsOpen.exists_Ioo_subset_mem_closure {α : Type*} [TopologicalSpace α] [Nontrivial α]
    [CompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α] {s : Set α} (hs : IsOpen s)
    (h : s.Nonempty) (hsb : ⊥ ∉ s) (hst : ⊤ ∉ s) :
    ∃ a b, a < b ∧ Set.Ioo a b ⊆ s ∧ a ∉ s ∧ b ∉ s := by
  obtain ⟨a, b, hab, habs⟩ := IsOpen.exists_Ioo_subset hs h
  obtain ⟨z, haz, hzb⟩ := exists_between hab
  use sInf {x | Set.Ioo x z ⊆ s}
  use sSup {y | Set.Ioo z y ⊆ s}
  have hsis : sInf {x | Set.Ioo x z ⊆ s} < sSup {y | Set.Ioo z y ⊆ s} :=
    lt_of_le_of_lt (sInf_le (by grind)) <| lt_of_lt_of_le hab <| le_sSup <| by grind
  simp only [hsis, true_and]
  constructor; swap; constructor
  · by_cases! hsib : sInf {x | Set.Ioo x z ⊆ s} = ⊥
    · rw [hsib]
      exact hsb
    by_contra!
    have hss : Set.Ioo (sInf {x | Set.Ioo x z ⊆ s}) z ⊆ s := by
      intro w
      simp only [Set.mem_Ioo, sInf_lt_iff, Set.mem_ofPred_eq, and_imp, forall_exists_index]
      grind
    have hm : s ∈ nhds (sInf {x | Set.Ioo x z ⊆ s}) := by
      rw [mem_nhds_iff]
      use s
    rw [mem_nhds_iff_exists_Ioo_subset' (by use ⊥; grind) (by grind)] at hm
    obtain ⟨l, u, hm, hlus⟩ := hm
    have hm' := hm
    simp only [Set.mem_Ioo] at hm'
    apply And.left at hm'
    apply notMem_of_lt_csInf' at hm'
    grind
  · by_cases! hsit : sSup {y | Set.Ioo z y ⊆ s} = ⊤
    · rw [hsit]
      exact hst
    by_contra!
    have hss : Set.Ioo z (sSup {y | Set.Ioo z y ⊆ s}) ⊆ s := by
      intro w
      simp only [Set.mem_Ioo, lt_sSup_iff, Set.mem_ofPred_eq, and_imp, forall_exists_index]
      grind
    have hm : s ∈ nhds (sSup {y | Set.Ioo z y ⊆ s}) := by
      rw [mem_nhds_iff]
      use s
    rw [mem_nhds_iff_exists_Ioo_subset' (by grind) (by use ⊤; grind)] at hm
    obtain ⟨l, u, hm, hlus⟩ := hm
    have hm' := hm
    simp only [Set.mem_Ioo] at hm'
    apply And.right at hm'
    apply notMem_of_csSup_lt at hm'
    specialize hm' <| OrderTop.bddAbove {y | Set.Ioo z y ⊆ s}
    grind
  · intro a
    simp only [Set.mem_Ioo, and_imp]
    intro hai has
    rw [lt_sSup_iff] at has
    rw [sInf_lt_iff] at hai
    grind

open ENNReal

/--
@isnad1 id=ex.0h1v.s5.e152fd192288 from=translated src=- shape=2bed44f7 vocab=31a4f4f0
-/
theorem ENNReal.exists_seq_rat_tendsto (x : ℝ≥0∞) :
    ∃ u : ℕ → ℚ, (∀ n : ℕ, 0 ≤ u n) ∧ Filter.Tendsto (fun x ↦ ENNReal.ofReal (u x))
    Filter.atTop (nhds x) := by
  by_cases! hx : x = ⊤
  · subst hx
    use fun n ↦ n
    simp only [Nat.cast_nonneg, implies_true, Rat.cast_natCast, ofReal_natCast, true_and]
    refine tendsto_nhds_top ?_
    simp only [Nat.cast_lt, Filter.eventually_atTop]
    intro n
    use n + 1
    grind
  by_cases! hx0 : x = 0
  · use fun n ↦ 0
    simp [hx0]
  obtain ⟨u, _, _, hut⟩ := Real.exists_seq_rat_strictMono_tendsto (ENNReal.toReal x)
  have hut' := hut
  simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at hut'
  apply And.left at hut'
  obtain ⟨n, hn⟩ := hut' 0 (by exact ENNReal.toReal_pos hx0 hx)
  use u ∘ (fun k ↦ k + n)
  constructor
  · simp only [Function.comp_apply]
    intro k
    specialize hn (k + n) (by grind)
    rw [Rat.cast_pos] at hn
    exact le_of_lt hn
  · rw [← ENNReal.ofReal_toReal hx]
    refine ENNReal.tendsto_ofReal ?_
    rw [← Filter.tendsto_add_atTop_iff_nat n] at hut
    exact hut
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
