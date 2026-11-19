/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.Seed.Data.Fin.FlagRange
import Tengoku.Seed.Data.Finite.Prod
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Order.Grade
import Tengoku.Seed.SetTheory.Cardinal.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank-indexed presentations of maximal chains

In a finite bounded order graded by `Fin (n + 1)`, assume every maximal
chain meets every grade.  Then maximal chains are equivalent to saturated
sequences indexed by those grades.  This is the sequence interface used by
the product-shuffle count.
-/

namespace HansenCograph

universe u v

noncomputable instance instFiniteFlag {P : Type u} [LE P] [Finite P] :
    Finite (Flag P) := by
  letI : Fintype P := Fintype.ofFinite P
  exact Finite.of_injective (fun s : Flag P ↦ s.carrier.toFinite.toFinset) (by
    intro s t h
    apply Flag.ext
    change s.carrier = t.carrier
    simpa only [Set.Finite.coe_toFinset] using
      congrArg (fun x : Finset P ↦ (x : Set P)) h)

/-- A saturated bottom-to-top sequence with `n` cover steps.-/
structure RankedFlag (P : Type u) [PartialOrder P] [BoundedOrder P]
    (n : ℕ) where
  toFun : Fin (n + 1) → P
  map_zero : toFun 0 = ⊥
  map_last : toFun (.last n) = ⊤
  covBy_succ : ∀ k : Fin n, toFun k.castSucc ⋖ toFun k.succ

instance {P : Type u} [PartialOrder P] [BoundedOrder P] {n : ℕ} :
    CoeFun (RankedFlag P n) (fun _ ↦ Fin (n + 1) → P) :=
  ⟨RankedFlag.toFun⟩

@[ext] theorem RankedFlag.ext {P : Type u} [PartialOrder P] [BoundedOrder P]
    {n : ℕ} {f g : RankedFlag P n} (h : ∀ k, f k = g k) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  exact funext h

/-- A saturated ranked flag is strictly increasing.-/
theorem RankedFlag.strictMono {P : Type u} [PartialOrder P] [BoundedOrder P]
    {n : ℕ} (f : RankedFlag P n) : StrictMono f :=
  Fin.strictMono_iff_lt_succ.mpr fun k ↦ (f.covBy_succ k).lt

/-- In particular, distinct ranks of a saturated flag contain distinct
elements.-/
theorem RankedFlag.injective {P : Type u} [PartialOrder P] [BoundedOrder P]
    {n : ℕ} (f : RankedFlag P n) : Function.Injective f :=
  f.strictMono.injective

noncomputable instance instFiniteRankedFlag {P : Type u}
    [PartialOrder P] [BoundedOrder P] [Finite P] {n : ℕ} :
    Finite (RankedFlag P n) :=
  Finite.of_injective RankedFlag.toFun (fun _ _ h ↦
    RankedFlag.ext (congrFun h))

/-- Every maximal chain meets every available grade.-/
def FlagGradeSurjective (P : Type u) [PartialOrder P]
    (n : ℕ) [GradeOrder (Fin (n + 1)) P] : Prop :=
  ∀ s : Flag P, Function.Surjective
    (fun x : s ↦ grade (Fin (n + 1)) x)

section Graded

variable {P : Type u} [PartialOrder P] [BoundedOrder P]
variable {n : ℕ} [GradeBoundedOrder (Fin (n + 1)) P]

/-- On a maximal chain, the grade map is an order isomorphism once every
grade is attained.-/
noncomputable def flagGradeOrderIso (h : FlagGradeSurjective P n)
    (s : Flag P) : s ≃o Fin (n + 1) where
  toEquiv := Equiv.ofBijective (fun x : s ↦ grade (Fin (n + 1)) x)
    ⟨by
      intro a b hab
      apply Subtype.ext
      by_contra hne
      rcases s.chain_le.total a.2 b.2 with hab' | hba'
      · exact (grade_strictMono (lt_of_le_of_ne hab' hne)).ne hab
      · exact (grade_strictMono (lt_of_le_of_ne hba' (Ne.symm hne))).ne hab.symm,
      h s⟩
  map_rel_iff' := by
    intro a b
    change grade (Fin (n + 1)) (a : P) ≤
      grade (Fin (n + 1)) (b : P) ↔ a ≤ b
    constructor
    · intro hgrade
      rcases s.le_or_le a.2 b.2 with hab | hba
      · exact hab
      · by_cases heq : a = b
        · exact heq.le
        · have hne : (b : P) ≠ (a : P) := by
            intro hval
            apply heq
            exact Subtype.ext hval.symm
          have hlt : grade (Fin (n + 1)) (b : P) <
              grade (Fin (n + 1)) (a : P) :=
            grade_strictMono (lt_of_le_of_ne hba hne)
          exact False.elim (not_le_of_gt hlt hgrade)
    · intro hab
      exact grade_mono hab

/-- Read a maximal chain in increasing grade order.-/
noncomputable def RankedFlag.ofFlag (h : FlagGradeSurjective P n)
    (s : Flag P) : RankedFlag P n where
  toFun k := (flagGradeOrderIso h s).symm k
  map_zero := by
    let botS : s := ⟨⊥, Flag.bot_mem s⟩
    have heq : (flagGradeOrderIso h s).symm 0 = botS := by
      apply (flagGradeOrderIso h s).injective
      rw [(flagGradeOrderIso h s).apply_symm_apply]
      apply Fin.ext
      change (0 : Fin (n + 1)).1 =
        (grade (Fin (n + 1)) (⊥ : P)).1
      rw [grade_bot]
      rfl
    exact congrArg Subtype.val heq
  map_last := by
    let topS : s := ⟨⊤, Flag.top_mem s⟩
    have heq : (flagGradeOrderIso h s).symm (.last n) = topS := by
      apply (flagGradeOrderIso h s).injective
      rw [(flagGradeOrderIso h s).apply_symm_apply]
      apply Fin.ext
      change (Fin.last n).1 =
        (grade (Fin (n + 1)) (⊤ : P)).1
      rw [grade_top]
      rfl
    exact congrArg Subtype.val heq
  covBy_succ k := by
    have hk : (k.castSucc : Fin (n + 1)) ⋖ k.succ := by
      rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
      rfl
    have hsub : (flagGradeOrderIso h s).symm k.castSucc ⋖
        (flagGradeOrderIso h s).symm k.succ :=
      (apply_covBy_apply_iff (flagGradeOrderIso h s).symm).mpr hk
    exact Flag.coe_covBy_coe.mpr hsub

/-- Take the range of a saturated sequence as a maximal chain.-/
def RankedFlag.toFlag (f : RankedFlag P n) : Flag P :=
  Flag.rangeFin f f.map_zero f.map_last
    (fun k ↦ (f.covBy_succ k).wcovBy)

omit [GradeBoundedOrder (Fin (n + 1)) P] in
theorem RankedFlag.mem_toFlag_iff (f : RankedFlag P n) (x : P) :
    x ∈ f.toFlag ↔ ∃ k, f k = x := Iff.rfl

omit [GradeBoundedOrder (Fin (n + 1)) P] in
theorem RankedFlag.toFlag_card [Finite P] (f : RankedFlag P n) :
    Nat.card f.toFlag = n + 1 := by
  change Nat.card (Set.range f) = n + 1
  rw [Nat.card_range_of_injective f.injective, Nat.card_fin]

omit [GradeBoundedOrder (Fin (n + 1)) P] in
/-- A saturated sequence is determined by its range.  Thus forgetting the
rank indexing is injective even without an ambient grading.-/
theorem RankedFlag.toFlag_injective : Function.Injective
    (RankedFlag.toFlag : RankedFlag P n → Flag P) := by
  intro f g h
  apply RankedFlag.ext
  intro k
  induction k using Fin.induction with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | succ k ih =>
      have hfmem : f k.succ ∈ g.toFlag := by
        rw [← h]
        exact ⟨k.succ, rfl⟩
      obtain ⟨j, hj⟩ := (g.mem_toFlag_iff (f k.succ)).mp hfmem
      have hkj : k.succ ≤ j := by
        apply Fin.mk_le_mk.mpr
        by_contra hnot
        have hjk : j ≤ k.castSucc := Fin.mk_le_mk.mpr (by omega)
        have hvalues : g j ≤ g k.castSucc := g.strictMono.monotone hjk
        rw [hj, ← ih] at hvalues
        exact (not_le_of_gt (f.covBy_succ k).lt) hvalues
      have hgf : g k.succ ≤ f k.succ := by
        rw [← hj]
        exact g.strictMono.monotone hkj
      have hgmem : g k.succ ∈ f.toFlag := by
        rw [h]
        exact ⟨k.succ, rfl⟩
      obtain ⟨i, hi⟩ := (f.mem_toFlag_iff (g k.succ)).mp hgmem
      have hki : k.succ ≤ i := by
        apply Fin.mk_le_mk.mpr
        by_contra hnot
        have hik : i ≤ k.castSucc := Fin.mk_le_mk.mpr (by omega)
        have hvalues : f i ≤ f k.castSucc := f.strictMono.monotone hik
        rw [hi, ih] at hvalues
        exact (not_le_of_gt (g.covBy_succ k).lt) hvalues
      have hfg : f k.succ ≤ g k.succ := by
        rw [← hi]
        exact f.strictMono.monotone hki
      exact le_antisymm hfg hgf

/-- The grades along a saturated ranked flag are exactly its indices.-/
theorem RankedFlag.grade_apply (f : RankedFlag P n) :
    ∀ k, grade (Fin (n + 1)) (f k) = k := by
  intro k
  induction k using Fin.induction with
  | zero =>
      rw [f.map_zero, grade_bot]
      rfl
  | succ k ih =>
      have hgrade := (f.covBy_succ k).grade (Fin (n + 1))
      rw [ih] at hgrade
      apply Fin.ext
      rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hgrade
      exact hgrade.symm

/-- Reading a maximal chain by grade and then forgetting the indexing gives
the original chain.-/
theorem RankedFlag.toFlag_ofFlag (h : FlagGradeSurjective P n)
    (s : Flag P) : (RankedFlag.ofFlag h s).toFlag = s := by
  apply Flag.ext
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ((flagGradeOrderIso h s).symm k).2
  · intro hx
    let xs : s := ⟨x, hx⟩
    refine ⟨flagGradeOrderIso h s xs, ?_⟩
    exact congrArg Subtype.val ((flagGradeOrderIso h s).symm_apply_apply xs)

/-- Forgetting and then recovering the grade indexing gives the original
saturated sequence.-/
theorem RankedFlag.ofFlag_toFlag (h : FlagGradeSurjective P n)
    (f : RankedFlag P n) : RankedFlag.ofFlag h f.toFlag = f := by
  apply RankedFlag.ext
  intro k
  let x : f.toFlag := ⟨f k, ⟨k, rfl⟩⟩
  have hxgrade : flagGradeOrderIso h f.toFlag x = k := by
    change grade (Fin (n + 1)) (f k) = k
    exact f.grade_apply k
  have hinv : (flagGradeOrderIso h f.toFlag).symm k = x := by
    apply (flagGradeOrderIso h f.toFlag).injective
    simp [hxgrade]
  exact congrArg Subtype.val hinv

/-- Maximal chains are equivalent to saturated rank-indexed sequences.-/
noncomputable def flagEquivRankedFlag (h : FlagGradeSurjective P n) :
    Flag P ≃ RankedFlag P n where
  toFun := RankedFlag.ofFlag h
  invFun := RankedFlag.toFlag
  left_inv := RankedFlag.toFlag_ofFlag h
  right_inv := RankedFlag.ofFlag_toFlag h

end Graded

end HansenCograph
