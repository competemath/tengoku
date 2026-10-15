/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku.LeanPool.LeanPool.WhiteheadTheorem.Shapes.UnitInterval
public import Tengoku

/-!
# LeanPool.WhiteheadTheorem.Shapes.Cube

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.Shapes.Cube`.
-/

@[expose] public section

open scoped unitInterval Topology Topology.Homotopy

namespace Cube

/-- `Cube.boundaryJar (n + 1) = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹` -/
def boundaryJar (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | (∃ i, y i = 0 ∨ y i = 1) ∧
      (y (Fin.last _) = 1 → ∃ i < Fin.last _, y i = 0 ∨ y i = 1) }

/-- `Cube.boundaryLid (n + 1) = Iⁿ × {1} ⊆ Iⁿ⁺¹` -/
def boundaryLid (n : ℕ) : Set (I^ Fin n) :=
  match n with
  | 0 => ∅
  | _ + 1 => {y | y (Fin.last _) = 1}

/-- `«term∂I^_»` -/
scoped[Topology.Homotopy] notation "∂I^" n => Cube.boundary (Fin n)
/-- `«term⊔I^_»` -/
scoped[Topology.Homotopy] notation "⊔I^" n => Cube.boundaryJar n

/-- `boundaryIncl` -/
def boundaryIncl (n : ℕ) : C(∂I^n, I^ (Fin n)) := ⟨Subtype.val, continuous_subtype_val⟩
/-- `boundaryJarIncl` -/
def boundaryJarIncl (n : ℕ) : C(⊔I^n, I^ (Fin n)) := ⟨Subtype.val, continuous_subtype_val⟩

/--
@isnad1 id=isempty.0h0v.s4.38ed386c9a46 from=translated src=- shape=c57bc207 vocab=f9d4a813
-/
instance isEmpty_boundary_zero : IsEmpty (∂I^0) :=
  Set.isEmpty_coe_sort.mpr <| Set.subset_empty_iff.mp fun _ ⟨i, _⟩ ↦ isEmptyElim i
/--
@isnad1 id=isempty.0h0v.s4.b2cf5f0fd8f3 from=translated src=- shape=20dd0be4 vocab=b195578f
-/
instance isEmpty_boundaryJar_zero : IsEmpty (⊔I^0) := by
  rw [Set.isEmpty_coe_sort]; rfl

/--
@isnad1 id=le.0h1v.s4.e9c0f77a13c7 from=translated src=- shape=b6d0840e vocab=05d27851
-/
lemma boundaryJar_subset_boundary (n : ℕ) : (⊔I^n) ⊆ (∂I^n) :=
  match n with
  | 0 => fun y hy ↦ isEmptyElim (⟨y, hy⟩ : ⊔I^0)
  | _ + 1 => fun _ ⟨hy1, _⟩ ↦ hy1

/-- `boundaryJarInclToBoundary` -/
def boundaryJarInclToBoundary (n : ℕ) : C(⊔I^n, ∂I^n) where
  toFun := fun ⟨y, hy⟩ ↦ ⟨y, boundaryJar_subset_boundary n hy⟩
  continuous_toFun := by fun_prop

/--
@isnad1 id=mem.1h2v.s7.de5f3c68a9f7 from=translated src=- shape=ae8906fa vocab=c67eb6d7
-/
lemma mem_boundaryJar_of_lt_last {n : ℕ} (y : I^(Fin (n + 1)))
    (hy : ∃ i < Fin.last _, y i = 0 ∨ y i = 1) : y ∈ ⊔I^(n+1) := by
  obtain ⟨i, ⟨hi, hyi⟩⟩ := hy
  constructor
  · exact ⟨i, hyi⟩
  · intro _; exact ⟨i, ⟨hi, hyi⟩⟩

/--
@isnad1 id=mem.1h2v.s5.1e6c7b51061c from=translated src=- shape=159eb7d6 vocab=4d701308
-/
lemma mem_boundaryJar_of_exists_eq_zero {n : ℕ} (y : I^Fin n)
    (hy : ∃ i, y i = 0) : y ∈ ⊔I^n :=
  match n with
  | 0 => isEmptyElim hy.choose
  | n + 1 => by
      obtain ⟨i, hi⟩ := hy
      constructor
      · use i; left; exact hi
      · intro hn1
        by_cases h : i = Fin.last _
        · rw [← h] at hn1; exfalso; exact (by norm_num : (1 : I) ≠ 0) (hn1.symm.trans hi)
        · use i; exact ⟨Fin.lt_last_iff_ne_last.mpr h, Or.inl hi⟩

/--
@isnad1 id=or.1h2v.s6.67f02c1d1f83 from=translated src=- shape=eb2609c0 vocab=54490b3d
-/
lemma mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary {n : ℕ} (y : I^Fin n)
    (hy : y ∈ ∂I^n) : y ∈ Cube.boundaryLid n ∨ y ∈ ⊔I^n :=
  match n with
  | 0 => isEmptyElim (⟨y, hy⟩ : ∂I^0)
  | n + 1 => by
      by_cases hyn : y (Fin.last _) = 1
      · left; exact hyn
      · right
        constructor
        · exact hy
        · intro hyn'; exfalso; exact hyn hyn'

/-- `⊔I^1 = {0}` is a singleton -/
instance uniqueBoundaryJarOne : Unique (⊔I^1) where
  default := ⟨0,
    ⟨ by use 0; simp only [Pi.zero_apply, zero_ne_one, or_false],
      by intro h; simp only [Pi.zero_apply, zero_ne_one] at h ⟩ ⟩
  uniq := fun ⟨y, ⟨⟨i, hi⟩, hy2⟩⟩ ↦ by
    ext j
    have : Unique (Fin 1) := by infer_instance
    have iz : i = 0 := Subsingleton.eq_zero i
    have jz : j = 0 := Subsingleton.eq_zero j
    rw [iz] at hi
    obtain h0 | h1 := hi
    all_goals simp only [Pi.zero_apply, Set.Icc.coe_zero, Set.Icc.coe_eq_zero]; rw [jz]
    · exact h0
    · exfalso; obtain ⟨k, hk⟩ := hy2 h1; exact Nat.not_succ_le_zero k hk.left

/-- `homeoNeqLast` -/
def homeoNeqLast {n : ℕ} : (I^ Fin n) ≃ₜ I^{ j : Fin (n + 1) // j ≠ Fin.last _ } :=
  Homeomorph.piCongr
    { toFun i := ⟨i.castSucc, by
        simp_all ⟩
      invFun i := ⟨i, by
        have := i.2
        simp only [ne_eq] at this
        exact Fin.lt_last_iff_ne_last.mpr this ⟩
      left_inv i := by simp only [Fin.val_castSucc, Fin.eta]
      right_inv i := by simp only [ne_eq, Fin.castSucc_mk, Fin.eta, Subtype.coe_eta] }
    fun _ ↦ Homeomorph.refl _

/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `(yₙ, (y₀, y₁, …, yₙ₋₁))` -/
def splitAtLast {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ I × (I^ Fin n) :=
  splitAt (Fin.last _) |>.trans <|
    Homeomorph.prodCongr (Homeomorph.refl _) homeoNeqLast.symm

/-- A homeomorphism that sends `(y₀, y₁, …, yₙ₋₁, yₙ)` to `((y₀, y₁, …, yₙ₋₁), yₙ)` -/
def splitAtLastComm {n : ℕ} : (I^ Fin (n + 1)) ≃ₜ (I^ Fin n) × I :=
  splitAtLast.trans <| Homeomorph.prodComm I (I^ Fin n)

/--
@isnad1 id=eq.0h2v.s9.a1f8da0c2334 from=translated src=- shape=ed12f5ac vocab=e4cd4dda
-/
lemma splitAtLast_fst_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).fst = y (Fin.last n) := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]

/--
@isnad1 id=eq.0h2v.s9.a98fca7cad7d from=translated src=- shape=7ad84d16 vocab=b2680988
-/
lemma splitAtLastComm_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLastComm y).snd = y (Fin.last n) := by
  simp only [splitAtLastComm, splitAtLast, ne_eq, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.coe_prodComm, Prod.swap_prod_mk]

/--
@isnad1 id=eq.0h2v.s10.763c8753f7f8 from=translated src=- shape=b55d636c vocab=6ce37d14
-/
lemma splitAtLast_snd_eq {n : ℕ} (y : I^Fin (n + 1)) :
    (splitAtLast y).snd = (splitAtLastComm y).fst := by
  simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
    Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
    splitAtLastComm, Homeomorph.coe_prodComm, Prod.swap_prod_mk]

/--
@isnad1 id=eq.0h3v.s9.4229b732d8c8 from=translated src=- shape=2b879124 vocab=0127007e
-/
lemma splitAtLast_snd_apply_eq {n : ℕ} (y : I^Fin (n + 1)) (i : Fin n) :
    (splitAtLast y).snd i = y i.castSucc := by
  simp only [splitAtLast, ne_eq, homeoNeqLast, Homeomorph.trans_apply,
    Homeomorph.funSplitAt_apply, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq]
  rfl

/--
@isnad1 id=eq.0h3v.s9.9f8622e7bef5 from=translated src=- shape=197ece32 vocab=8504cf59
-/
lemma splitAtLast_symm_apply_last {n : ℕ} (t : I) (y : I^Fin n) :
    (splitAtLast.symm ⟨t, y⟩) (Fin.last _) = t := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/--
@isnad1 id=eq.1h4v.s9.f900b92200e8 from=translated src=- shape=18934597 vocab=3fe7c839
-/
lemma splitAtLast_symm_apply_eq_of_neq_last {n : ℕ} (t : I) (y : I^Fin n) (i : Fin (n + 1))
    (hi : i ≠ Fin.last _) :
    (splitAtLast.symm ⟨t, y⟩) i = y ⟨i, Fin.lt_last_iff_ne_last.mpr hi⟩ := by
  simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm,
    Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply,
    Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply]
  simp only [homeoNeqLast, ne_eq, Homeomorph.piCongr_apply]
  simp_all only []
  rfl

/-- `y ∈ ⊔I^(n+1)` if and only if either `y` is on the bottom face,
or its first `n` coordinates constitute a point in `∂I^n`.
Note that `(splitAtLast y).fst` is the last (`n`-th) coordinate.
@isnad1 id=iff.0h2v.s10.3bea6795fe7b from=translated src=- shape=06a0db59 vocab=caf2927b
-/
lemma mem_boundaryJar_iff_splitAtLast {n : ℕ} {y : I^Fin (n + 1)} :
    y ∈ (⊔I^(n+1)) ↔ (splitAtLast y).fst = 0 ∨ (splitAtLast y).snd ∈ ∂I^n := by
  constructor
  · intro hy
    simp only [splitAtLast, ne_eq, Homeomorph.trans_apply, Homeomorph.funSplitAt_apply,
      Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq]
    by_cases h0 : y (Fin.last n) = 0
    · left; exact h0
    · right
      by_cases h1 : y (Fin.last n) = 1
      · have := hy.right h1
        obtain ⟨i, hi, h⟩ := hy.right h1
        use ⟨i, hi⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
      · obtain ⟨i, h⟩ := hy.left
        have : i ≠ (Fin.last n) := fun hn ↦ by
          rw [hn] at h; rcases h with h | h; exacts [h0 h, h1 h]
        use ⟨i.val, Fin.lt_last_iff_ne_last.mpr this⟩
        rcases h with h | h
        · left; change (homeoNeqLast.invFun _) _ = 0; simpa [homeoNeqLast]
        · right; change (homeoNeqLast.invFun _) _ = 1; simpa [homeoNeqLast]
  · intro hy
    rcases hy with hy | ⟨i, hi⟩
    · rw [splitAtLast_fst_eq] at hy
      apply mem_boundaryJar_of_exists_eq_zero
      use Fin.last n
    · rw [splitAtLast_snd_apply_eq] at hi
      constructor
      · use i.castSucc
      · intro hyn
        use i.castSucc
        exact ⟨Fin.castSucc_lt_last i, hi⟩

/-- An easy corrolary of `mem_boundaryJar_iff_splitAtLast`
@isnad1 id=mem.2h2v.s9.ba9c5002a012 from=translated src=- shape=5b3dcd7e vocab=e6a02661
-/
lemma splitAtLast_snd_mem_boundary_of_last_neq_zero {n : ℕ} {y : I^Fin (n + 1)}
    (hy : y ∈ ⊔I^(n + 1)) (hyn : y (Fin.last _) ≠ 0) :
    (splitAtLast y).snd ∈ ∂I^n := by
  rw [← splitAtLast_fst_eq y] at hyn
  cases mem_boundaryJar_iff_splitAtLast.mp hy
  · exfalso; exact hyn ‹_›
  · assumption

/--
@isnad1 id=mem.1h3v.s9.fa06e8536326 from=translated src=- shape=c7693fea vocab=0a4e7e41
-/
lemma splitAtLast_symm_mem_boundary_of_mem_boundary
    {n : ℕ} {y : I^Fin n} (t : I) (hy : y ∈ ∂I^n) :
    splitAtLast.symm ⟨t, y⟩ ∈ ∂I^(n + 1) := by
  obtain ⟨i, hi⟩ := hy
  use i.castSucc
  rw [splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
  exact hi

/-- The inclusion from the n-dimensional cube to the top face of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, 1).
(Although `1` appears first in this definition, it is actually the last coordinate
in `(I^ Fin (n + 1))`, due to `Cube.insertAt`). -/
def inclToTop {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := splitAtLast.symm ⟨1, y⟩
  continuous_toFun := splitAtLast.symm.continuous.comp <|
    Continuous.prodMk continuous_const continuous_id

namespace inclToTop

/-- (y, 1) is in the `boundary`.
@isnad1 id=mem.0h2v.s8.ddcbc5221148 from=translated src=- shape=ebb210da vocab=18058b9b
-/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToTop y ∈ ∂I^(n + 1) := by
  use Fin.last _
  right
  simp only [inclToTop, splitAtLast, ne_eq, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, ContinuousMap.coe_mk,
    Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/-- If y is in the `boundary`, then (y, 1) is in the `boundaryJar`.
@isnad1 id=mem.1h2v.s8.a7383a9a4304 from=translated src=- shape=8a82b4d4 vocab=abdce74f
-/
lemma mem_boundaryJar_of {n : ℕ} {y : I^Fin n}
    (hy : y ∈ ∂I^n) : inclToTop y ∈ ⊔I^(n + 1) := by
  obtain ⟨i, hi⟩ := hy
  simp only [inclToTop, ContinuousMap.coe_mk]
  constructor
  · use Fin.last _        -- the n-th coordinate of (y, 1) is 1
    simp only [splitAtLast, ne_eq, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte,
    one_ne_zero, or_true]
  · intro _
    use i.castSucc         -- the i-th coordinate of (y, 1) is 0 or 1, where i < n
    constructor
    · simp only [Fin.castSucc_lt_last]
    · simpa only [splitAtLast, ne_eq, homeoNeqLast, Fin.coe_eq_castSucc,
      Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
      Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply, id_eq,
      Homeomorph.funSplitAt_symm_apply, Fin.natCast_eq_last, Fin.castSucc_ne_last, ↓reduceDIte,
      Homeomorph.piCongr_apply, Equiv.coe_fn_symm_mk, Fin.val_castSucc, Fin.eta]

end inclToTop

/--
@isnad1 id=eq.0h2v.s9.ca92a2a1db4a from=translated src=- shape=aa85f85e vocab=8e624913
-/
lemma splitAtLast_inclToTop_eq {n : ℕ} {y : I^Fin n} :
    splitAtLast (inclToTop y) = ⟨1, y⟩ := by
  simp only [splitAtLast, ne_eq, inclToTop, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.refl_symm, Homeomorph.symm_symm, Homeomorph.coe_prodCongr,
    Homeomorph.refl_apply, Prod.map_apply, id_eq, ContinuousMap.coe_mk, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]

/-- `(y₀, y₁, …, yₙ₋₁, yₙ) ↦ (y₀, y₁, …, yₙ₋₁)` -/
def discardLast {n : ℕ} : C(I^ Fin (n + 1), I^ Fin n) where
  toFun y := fun i ↦ y ⟨i.val, i.prop.trans (by omega : n < n + 1)⟩
  continuous_toFun := by fun_prop

/-- (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) -/
def inclToBot {n : ℕ} : C(I^ Fin n, I^ Fin (n + 1)) where
  toFun y := Cube.insertAt (Fin.last _) ⟨0, Cube.homeoNeqLast y⟩
  continuous_toFun := (Cube.insertAt _).continuous.comp <|
    Continuous.prodMk continuous_const Cube.homeoNeqLast.continuous

namespace inclToBot

/-- (y, 0) is in the `boundary`.
@isnad1 id=mem.0h2v.s8.690b558350be from=translated src=- shape=ebb210da vocab=6f2e9aa2
-/
lemma mem_boundary {n : ℕ} (y : I^Fin n) : inclToBot y ∈ ∂I^(n + 1) := by
  use Fin.last _
  left
  simp only [inclToBot, ne_eq, ContinuousMap.coe_mk,
    Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]

/-- (y, 0) is in the `boundaryJar`.
@isnad1 id=mem.0h2v.s8.281de960dd8a from=translated src=- shape=e2df83c7 vocab=72b74955
-/
lemma mem_boundaryJar {n : ℕ} (y : I^Fin n) : inclToBot y ∈ ⊔I^(n + 1) := by
  constructor
  · exact mem_boundary y
  · intro h; exfalso
    have : inclToBot y (Fin.last n) = (0 : ℝ) := by simp [inclToBot]
    simp_all

end inclToBot

/-- The inclusion (y₀, y₁, …, yₙ₋₁) ↦ (y₀, y₁, …, yₙ₋₁, 0) to the bottom face of `⊔I^(n+1)` -/
def inclToBoundaryJarBot {n : ℕ} : C(I^ Fin n, ⊔I^(n+1)) where
  toFun y := ⟨ inclToBot y, inclToBot.mem_boundaryJar y ⟩
  continuous_toFun := Continuous.subtype_mk inclToBot.continuous _

/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to
the sides of `⊔I^(n+1)`, i.e.,
the closure of the complement of the top and bottom faces of `∂I^(n+1)`. -/
def inclToBoundaryJarSides {n : ℕ} : C((∂I^n) × I, ⊔I^(n+1)) where
  toFun := fun yt ↦
    ⟨ (toContinuousMap splitAtLastComm.symm |>.comp <|
        ContinuousMap.prodMap (boundaryIncl n) (ContinuousMap.id _)) yt,
    by
      obtain ⟨⟨y, ⟨i, hyi⟩⟩, t⟩ := yt
      constructor
      · use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last]
      · intro _; use i.castSucc
        simp [splitAtLastComm, splitAtLast, homeoNeqLast, boundaryIncl]
        simpa [Fin.castSucc_ne_last, Fin.castSucc_lt_last]  ⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [ContinuousMap.coe_comp, ContinuousMap.coe_coe, Homeomorph.comp_continuous_iff]
    apply ContinuousMapClass.map_continuous

/-- The inclusion `(y, t) ↦ (y₀, y₁, …, yₙ₋₁, t)` to the sides of
the $(n+1)$-dimensional cube. -/
def inclToSides {n : ℕ} : C((∂I^n) × I, I^ Fin (n + 1)) where
  toFun := Subtype.val ∘ inclToBoundaryJarSides
  continuous_toFun := Continuous.subtype_val inclToBoundaryJarSides.continuous

end Cube

namespace TopCat

/-- `cube` -/
def cube (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| I^ Fin n

/-- `cubeBoundary` -/
def cubeBoundary (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundary (Fin n)

/-- `cubeBoundaryJar` -/
def cubeBoundaryJar (n : ℕ) : TopCat.{u} := TopCat.of <| ULift <| Cube.boundaryJar n

/-- `𝕀 n` denotes the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "𝕀 " => cube

/-- `∂𝕀 n` denotes the boundary of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "∂𝕀 " => cubeBoundary

/-- `⊔𝕀 n` denotes the "boundary jar" ($⊔Iⁿ⁺¹ = ∂Iⁿ × I ∪ Iⁿ × {0} ⊆ Iⁿ⁺¹$)
of the `n`-cube (as an object in `TopCat`). -/
scoped prefix:arg "⊔𝕀 " => cubeBoundaryJar

/-- The inclusion `∂𝕀 n ⟶ 𝕀 n` of the boundary of the `n`-cube. -/
def cubeBoundaryIncl (n : ℕ) : cubeBoundary.{u} n ⟶ cube.{u} n :=
  ofHom
    { toFun := fun ⟨⟨p, _⟩⟩ ↦ ⟨p⟩
      continuous_toFun :=
        continuous_uliftUp.comp <| continuous_subtype_val.comp continuous_induced_dom }

/-- `cubeBoundaryJarInclToBoundary` -/
def cubeBoundaryJarInclToBoundary (n : ℕ) : cubeBoundaryJar.{u} n ⟶ cubeBoundary.{u} n :=
  ofHom
    { toFun := fun ⟨p⟩ ↦ ⟨Cube.boundaryJarInclToBoundary n p⟩
      continuous_toFun := by fun_prop }

/--
@isnad1 id=eq.1h2v.s7.17c4e4de0485 from=translated src=- shape=12db05ee vocab=40c72a97
-/
@[simp↓]
lemma cubeBoundaryIncl_apply_down_eq {n : ℕ} (y : I^Fin n) (hy : y ∈ ∂I^n) :
    (cubeBoundaryIncl n ⟨⟨y, hy⟩⟩).down = y := rfl

/-- `cubeSplitAtLast` -/
def cubeSplitAtLast {n : ℕ} : 𝕀 (n + 1) ≅ TopCat.of (I × 𝕀 n) where
  hom := ofHom ⟨fun ⟨y⟩ ↦ ⟨(Cube.splitAtLast y).fst, ⟨(Cube.splitAtLast y).snd⟩⟩, by fun_prop⟩
  inv := ofHom ⟨fun ⟨t, ⟨y⟩⟩ ↦ ⟨Cube.splitAtLast.symm ⟨t, y⟩⟩, by fun_prop⟩
  hom_inv_id := by
    ext ⟨y⟩
    change ULift.up (Cube.splitAtLast.symm (Cube.splitAtLast y)) = ULift.up y
    exact congrArg ULift.up (Cube.splitAtLast.symm_apply_apply y)
  inv_hom_id := by
    ext ⟨t, ⟨y⟩⟩
    all_goals simp only [hom_id, ContinuousMap.id_apply]
    · congr 1
      change (Cube.splitAtLast (Cube.splitAtLast.symm _)).fst = _
      simp only [Homeomorph.apply_symm_apply]
    · change ({ down := (Cube.splitAtLast (Cube.splitAtLast.symm (t, y))).2 } : ULift _) = _
      simp only [Homeomorph.apply_symm_apply]

/-- This lemma should be applied before expanding the `match` expression.
@isnad1 id=eq.0h3v.s10.e4a0681e2fa6 from=translated src=- shape=c1c021ce vocab=910494e5
-/
@[simp↓]
lemma cubeSplitAtLast_inv_down_eq {n : ℕ} (t : I) (y : 𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, y⟩).down = Cube.splitAtLast.symm ⟨t, y.down⟩ := rfl

/--
@isnad1 id=mem.0h3v.s9.16a8f66c6c62 from=translated src=- shape=8522372c vocab=49ba685c
-/
lemma cubeSplitAtLast_inv_mem_boundary_of_mem_boundary {n : ℕ} (t : I) (y : ∂𝕀 n) :
    (cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩).down ∈ ∂I^ (n + 1) := by
  simp only [↓cubeSplitAtLast_inv_down_eq]
  apply Cube.splitAtLast_symm_mem_boundary_of_mem_boundary t y.down.property

namespace cubeBoundary

/-- The inclusion from the n-dimensional cube to the top or bottom face
of the boundary of the (n+1)-dimensional cube,
mapping (y₀, y₁, …, yₙ₋₁) to (y₀, y₁, …, yₙ₋₁, t). -/
def cubeInclToBotOrTop {n : ℕ} (t : unitInterval.zeroOne) : 𝕀 n ⟶ ∂𝕀 (n + 1) :=
  ofHom
    { toFun := fun ⟨y⟩ ↦ ⟨Cube.splitAtLast.symm ⟨unitInterval.zeroOneIncl t, y⟩, by
        use Fin.last _
        simp only [Cube.splitAtLast, ne_eq, ContinuousMap.coe_mk,
          Homeomorph.symm_trans_apply, Homeomorph.prodCongr_symm, Homeomorph.refl_symm,
          Homeomorph.symm_symm, Homeomorph.coe_prodCongr, Homeomorph.refl_apply, Prod.map_apply,
          id_eq, Homeomorph.funSplitAt_symm_apply, ↓reduceDIte]
        obtain ht | ht := unitInterval.zeroOne.val_eq_zero_or_val_eq_one t
        · left; simp_all only [Set.Icc.mk_zero]
        · right; simp_all only [Set.Icc.mk_one] ⟩
      continuous_toFun := by fun_prop }

/-- `botOrTop` -/
abbrev botOrTop (n : ℕ) (t : unitInterval.zeroOne) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | y (Fin.last _) = unitInterval.zeroOneIncl t}

/-- `sides` -/
abbrev sides (n : ℕ) : Set (∂𝕀 (n + 1)) :=
  {⟨⟨y, _⟩⟩ | ∃ i < Fin.last _, y i = 0 ∨ y i = 1}

/--
@isnad1 id=mem.0h3v.s7.e3a34762782e from=translated src=- shape=faeb1ce3 vocab=1bc59e36
-/
lemma cubeInclToBotOrTop_mem_botOrTop
    {n : ℕ} (t : unitInterval.zeroOne) (y : 𝕀 n) :
    cubeInclToBotOrTop t y ∈ botOrTop n t := by
  change (Cube.splitAtLast.symm (unitInterval.zeroOneIncl t, y.down)) (Fin.last n) =
    unitInterval.zeroOneIncl t
  rw [Cube.splitAtLast_symm_apply_last]

/-- Given a point on the boundary of the `n`-dimensional cube,
cast it as a point on the boundary of the `(n + 1)`-dimensional cube
by specifying the height `t : I`. -/
def castSucc {n : ℕ} (t : I) (y : ∂𝕀 n) : ∂𝕀 (n + 1) :=
  ⟨cubeSplitAtLast.inv ⟨t, cubeBoundaryIncl n y⟩ |>.down,
    cubeSplitAtLast_inv_mem_boundary_of_mem_boundary t y⟩

/--
@isnad1 id=mem.0h3v.s6.527998439dcb from=translated src=- shape=88152bcd vocab=7eeba8e7
-/
lemma castSucc_mem_sides {n : ℕ} (t : I) (y : ∂𝕀 n) :
    castSucc t y ∈ sides n := by
  obtain ⟨⟨y, ⟨i, hi⟩⟩⟩ := y
  use i.castSucc
  constructor
  · exact Fin.castSucc_lt_last i
  · change Cube.splitAtLast.symm (t, y) i.castSucc = 0 ∨
      Cube.splitAtLast.symm (t, y) i.castSucc = 1
    rw [Cube.splitAtLast_symm_apply_eq_of_neq_last t y i.castSucc (Fin.castSucc_ne_last i)]
    exact hi

end cubeBoundary

end TopCat
