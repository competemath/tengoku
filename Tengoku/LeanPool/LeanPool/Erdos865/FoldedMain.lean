/-
Copyright (c) 2026 Ricky Cipollini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ricky Cipollini
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos865.Defs
import Tengoku.LeanPool.LeanPool.Erdos865.FoldedAux
public import Tengoku

/-!
# The folded additive lemma

Monotonicity of the sum sets, the reflection `-B = {m - b}` and its effect on
`lowSums`/`highSums`/`collisions`, and the inductive `core_step` that proves the folded
additive lemma `folded_additive`.
-/

@[expose] public section

open Finset

namespace Erdos865

/-! ### Monotonicity of the sum sets -/

/--
@isnad1 id=foldedok.2h3v.s4.d7bc8e592460 from=translated src=- shape=2f100fbd vocab=2e16f601
-/
theorem foldedOK_subset {m : ℕ} {B C : Finset ℕ} (hB : FoldedOK m B) (h : C ⊆ B) :
    FoldedOK m C := by
  constructor;
  · exact fun x hx => hB.1 x ( h hx );
  · exact fun x hx y hy hxy =>
      ⟨ hB.2 x ( h hx ) y ( h hy ) hxy |>.1,
        fun hxy' => hB.2 x ( h hx ) y ( h hy ) hxy |>.2 <| h hxy' ⟩

/--
@isnad1 id=le.1h3v.s5.ebe429c74618 from=translated src=- shape=0b1fbad5 vocab=f6fdcf05
-/
theorem lowSums_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) : lowSums m B ⊆ lowSums m C := by
  exact Finset.image_subset_image
    ( Finset.filter_subset_filter _ ( Finset.product_subset_product h h ) )

/--
@isnad1 id=le.1h3v.s5.04d05f3573fc from=translated src=- shape=0b1fbad5 vocab=89a599cc
-/
theorem highSums_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) : highSums m B ⊆ highSums m C := by
  exact Finset.image_subset_iff.mpr fun p hp => Finset.mem_image.mpr
    ⟨ p, Finset.mem_filter.mpr
      ⟨ Finset.mem_product.mpr
        ⟨ h <| Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.1,
          h <| Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.2 ⟩,
        Finset.mem_filter.mp hp |>.2 ⟩, rfl ⟩

/--
@isnad1 id=le.1h3v.s5.f9c94d5d0bb2 from=translated src=- shape=0b1fbad5 vocab=12956b85
-/
theorem collisions_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) :
    collisions m B ⊆ collisions m C :=
  Finset.inter_subset_inter (lowSums_mono h) (highSums_mono h)

/--
@isnad1 id=lt.1h3v.s4.60c595a85f23 from=translated src=- shape=675b2633 vocab=8c8c015f
-/
theorem mem_lowSums_lt {m : ℕ} {B : Finset ℕ} {v : ℕ} (hv : v ∈ lowSums m B) : v < m := by
  unfold lowSums at hv;
  grind

/--
@isnad1 id=lt.3h3v.s5.7e8ab08c6622 from=translated src=- shape=810e2838 vocab=db96ffb6
-/
theorem mem_highSums_lt {m : ℕ} (_hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {v : ℕ}
    (hv : v ∈ highSums m B) : v < m := by
  obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hv;
  rw [ tsub_lt_iff_left ] <;>
    linarith [ Finset.mem_filter.mp hp,
      hB.1 p.1 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ),
      hB.1 p.2 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ]

/-
After deleting the minimum `α`, the value `α + β` is no longer a low pair sum, because
every remaining pair of distinct elements has both entries `≥ β > α`, so sum `> α + β`.
-/
/--
@isnad1 id=not.2h4v.s6.38440378e3d1 from=translated src=- shape=a8ea1489 vocab=ffda01a6
-/
theorem sum_not_lowSums_erase {m : ℕ} {S : Finset ℕ} {α β : ℕ} (hαβ : α < β)
    (hmin2 : ∀ x ∈ S, x ≠ α → β ≤ x) : α + β ∉ lowSums m (S.erase α) := by
  simp [lowSums];
  grind

/-! ### Reflection `-B = {m - b}` -/

/-- The reflected set `-B = {m - b : b ∈ B}`. -/
def reflB (m : ℕ) (B : Finset ℕ) : Finset ℕ := B.image (fun b : ℕ => m - b)

/--
@isnad1 id=eq.1h2v.s4.c6f0c6bdc8a7 from=translated src=- shape=d56d969d vocab=5d7edb1a
-/
theorem card_reflB {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (reflB m B).card = B.card := by
  rw [ reflB, Finset.card_image_of_injOn ];
  exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hB.1 x hx, hB.1 y hy ] ;

/--
@isnad1 id=foldedok.2h2v.s4.84bc95a65b27 from=translated src=- shape=1d2d2ac5 vocab=3ffcd556
-/
theorem foldedOK_reflB {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    FoldedOK m (reflB m B) := by
  constructor;
  · intro b hb; obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hb;
    exact ⟨ Nat.sub_pos_of_lt ( hB.1 x hx |>.2 ), Nat.sub_lt ( by linarith ) ( hB.1 x hx |>.1 ) ⟩;
  · intro x hx y hy hxy;
    constructor;
    · obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx;
      obtain ⟨ b, hb, rfl ⟩ := Finset.mem_image.mp hy;
      simp_all +decide [ FoldedOK ];
      grind +ring;
    · simp_all +decide only [reflB, mem_image, ne_eq, not_exists, not_and];
      intro z hz;
      obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, rfl ⟩ := hy; have := hB.2 a ha b hb;
      simp_all +decide only [ne_eq];
      contrapose! this;
      have h_eq : (a + b) % m = z := by
        have h_eq : (a + b) % m = (m - (m - a + (m - b)) % m) % m := by
          simp +decide only [← ZMod.natCast_eq_natCast_iff', Nat.cast_add];
          rw [ Nat.cast_sub ( Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) ) ) ];
          simp +decide [ Nat.cast_sub ( show a ≤ m from by linarith [ hB.1 a ha ] ),
            Nat.cast_sub ( show b ≤ m from by linarith [ hB.1 b hb ] ) ];
          ring;
        rw [ h_eq, ← this, Nat.sub_sub_self ( show z ≤ m from by linarith [ hB.1 z hz ] ) ];
        exact Nat.mod_eq_of_lt ( hB.1 z hz |>.2 );
      exact ⟨ by aesop, fun _ => h_eq.symm ▸ hz ⟩

/--
@isnad1 id=eq.2h2v.s5.97258a6c4248 from=translated src=- shape=f801de39 vocab=13951686
-/
theorem lowSums_reflB {m : ℕ} (_hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    lowSums m (reflB m B) = (highSums m B).image (fun v : ℕ => m - v) := by
  ext z;
  constructor;
  · unfold lowSums highSums;
    simp +zetaDelta only [ne_eq, mem_image, mem_filter, mem_product, Prod.exists, ↓existsAndEq,
      and_true, forall_exists_index, and_imp] at *;
    rintro x y hx hy hxy hxy' rfl; rcases Finset.mem_image.mp hx with ⟨ a, ha, rfl ⟩;
    rcases Finset.mem_image.mp hy with ⟨ b, hb, rfl ⟩; use a, b; simp_all +decide ;
    have := hB.1 a ha; have := hB.1 b hb; omega;
  · simp +zetaDelta only [mem_image, forall_exists_index, and_imp] at *;
    rintro x hx rfl;
    unfold highSums lowSums reflB at *;
    simp +zetaDelta only [ne_eq, mem_image, mem_filter, mem_product, Prod.exists, ↓existsAndEq,
      and_true] at *;
    obtain ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, h ⟩, rfl ⟩ := hx; use a, b;
    simp_all +decide [ add_comm ];
    have := hB.1 a ha; have := hB.1 b hb; omega;

/--
@isnad1 id=eq.1h2v.s5.b35ca91f1f69 from=translated src=- shape=c6f5b3ed vocab=2da7299d
-/
theorem highSums_reflB {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} :
    highSums m (reflB m B) = (lowSums m B).image (fun v : ℕ => m - v) := by
  ext z;
  simp only [highSums, ne_eq, reflB, mem_image, mem_filter, mem_product, Prod.exists, ↓existsAndEq,
    and_true, lowSums];
  constructor <;> intro h; all_goals grind

/--
@isnad1 id=eq.2h2v.s5.9cb851d2fcb3 from=translated src=- shape=c2bf6d6e vocab=c7afe2ab
-/
theorem collisions_reflB_card {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    (collisions m (reflB m B)).card = (collisions m B).card := by
  -- By definition of `collisions`, we know that
  -- `collisions m (reflB m B) = coll highSums m B ∩ lowSums m B|
  have h_collisions_refl : collisions m (reflB m B) =
      ((highSums m B) ∩ (lowSums m B)).image (fun v => m - v) := by
    unfold collisions
    rw [lowSums_reflB hm hB, highSums_reflB (B := B) hm]
    ext z
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, b, hb, hb'⟩
      have ha_lt := mem_highSums_lt hm hB ha
      have hb_lt := mem_lowSums_lt hb
      have hab : a = b := by omega
      exact ⟨a, ⟨ha, by rw [hab]; exact hb⟩, rfl⟩
    · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
      exact ⟨⟨v, hv1, rfl⟩, v, hv2, rfl⟩
  rw [ h_collisions_refl, collisions ];
  rw [ Finset.inter_comm, Finset.card_image_of_injOn ];
  exact fun x hx y hy hxy => by
    rw [ tsub_right_inj ] at hxy <;>
      linarith [ mem_lowSums_lt ( Finset.mem_of_mem_inter_left hx ),
        mem_highSums_lt hm hB ( Finset.mem_of_mem_inter_right hy ) ];

/-! ### The core inductive step -/

/--
@isnad1 id=le.9h4v.s7.9841957efd6c from=translated src=- shape=332f3bed vocab=1694f93d
-/
theorem core_step {m : ℕ} (hm : 2 ≤ m) {S : Finset ℕ} (hS : FoldedOK m S) {α β : ℕ}
    (hα : α ∈ S) (hβ : β ∈ S) (hαβ : α < β) (hmin : ∀ x ∈ S, α ≤ x)
    (hmin2 : ∀ x ∈ S, x ≠ α → β ≤ x) (hsum : α + β < m)
    (IH : ∀ S', FoldedOK m S' → S'.card < S.card →
      4 * S'.card ≤ 4 * (collisions m S').card + m + 8) :
    4 * S.card ≤ 4 * (collisions m S).card + m + 8 := by
  by_cases hnc : α + β ∈ collisions m S;
  · obtain ⟨S', hS', hS'_card⟩ :
        ∃ S' : Finset ℕ, S' = S.erase α ∧ FoldedOK m S' ∧ S'.card < S.card ∧
          (collisions m S').card + 1 ≤ (collisions m S).card := by
      refine ⟨ S.erase α, rfl, foldedOK_subset hS ( Finset.erase_subset α S ), ?_, ?_ ⟩;
      · exact Finset.card_lt_card ( Finset.erase_ssubset hα );
      · refine Nat.succ_le_of_lt ( Finset.card_lt_card ?_ );
        refine ⟨ ?_, ?_ ⟩;
        · exact collisions_mono ( Finset.erase_subset _ _ );
        · rw [ Finset.not_subset ];
          refine ⟨ α + β, hnc, ?_ ⟩;
          exact fun h => sum_not_lowSums_erase hαβ hmin2 <| Finset.mem_of_mem_inter_left h;
    grind;
  · linarith [ case2_bound hm hS hα hβ hαβ hmin hmin2 hsum hnc ]

/-! ### The folded additive lemma -/

/-
**Folded additive lemma.** For `m ≥ 2` and `B` satisfying `FoldedOK`,
`4 * |B| ≤ 4 * |C(B)| + m + 8`, i.e. `|B| - |C(B)| ≤ m/4 + 2`.
-/
/--
@isnad1 id=le.2h2v.s6.836bad680d97 from=translated src=- shape=d9407481 vocab=cc36e476
-/
theorem folded_additive {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    4 * B.card ≤ 4 * (collisions m B).card + m + 8 := by
  by_contra! h_contra;
  -- By strong induction on B.card, we can assume the statement holds for all sets with
  -- cardinality less than B.card.
  induction k : B.card using Nat.strong_induction_on generalizing B m
  rename_i ih
  by_cases h_card : B.card ≤ 1;
  · grind;
  · -- Let α := B.min' (nonempty proof from card ≥ 2). Then hα : α ∈ B (Finset.min'_mem) and
    -- hmin : ∀ x ∈ B, α ≤ x (Finset.min'_le).
    obtain ⟨α, hα⟩ : ∃ α ∈ B, ∀ x ∈ B, α ≤ x := by
      exact ⟨ Nat.find <| Finset.card_pos.mp <| by linarith,
        Nat.find_spec <| Finset.card_pos.mp <| by linarith, fun x hx => Nat.find_min' _ hx ⟩
    obtain ⟨β, hβ⟩ : ∃ β ∈ B.erase α, ∀ x ∈ B.erase α, β ≤ x := by
      exact ⟨ Finset.min' _
        ⟨ Classical.choose ( Finset.exists_mem_ne ( by linarith ) α ),
          Finset.mem_erase_of_ne_of_mem
            ( Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) α ) |>.2 )
            ( Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) α ) |>.1 ) ⟩,
        Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx ⟩
    have hαβ : α < β := by
      exact lt_of_le_of_ne ( hα.2 β ( Finset.mem_of_mem_erase hβ.1 ) ) ( by aesop )
    have hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x := by
      exact fun x hx hx' => hβ.2 x ( Finset.mem_erase_of_ne_of_mem hx' hx )
    have hsum : α + β < m ∨ β + α > m := by
      have := hB.2 α hα.1 β ( Finset.mem_of_mem_erase hβ.1 ) ( by linarith ); omega;
    obtain hsum | hsum := hsum;
    · exact absurd ( core_step hm hB hα.1 ( Finset.mem_of_mem_erase hβ.1 ) hαβ hα.2 hmin2 hsum
        fun S' hS' hS'_card => by
          specialize ih ( S'.card ) ( by linarith [ Finset.card_erase_lt_of_mem hα.1 ] ) hm hS';
          aesop ) ( by linarith );
    · -- Let u := B.max' (nonempty), v := (B.erase u).max'. Then:
      obtain ⟨u, hu⟩ : ∃ u ∈ B, ∀ x ∈ B, x ≤ u := by
        exact ⟨ Finset.max' B ⟨ α, hα.1 ⟩, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
      obtain ⟨v, hv⟩ : ∃ v ∈ B.erase u, ∀ x ∈ B.erase u, x ≤ v := by
        exact ⟨ Finset.max' _ <| Finset.card_pos.mp <|
            by rw [ Finset.card_erase_of_mem hu.1 ]; omega,
          Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
      have hu_gt_v : u > v := by
        grind
      have huv_gt_m : u + v > m := by
        grind
      have huv_ne_m : u + v ≠ m := by
        grind
      generalize_proofs at *; (
      -- Let S := reflB m B, and consider α' := m - u, β' := m - v. Verify the core_step
      -- hypotheses for S with α', β':
      set S := reflB m B
      set α' := m - u
      set β' := m - v
      have hS : FoldedOK m S := by
        exact foldedOK_reflB hm hB
      have hα' : α' ∈ S := by
        exact Finset.mem_image.mpr ⟨ u, hu.1, rfl ⟩
      have hβ' : β' ∈ S := by
        exact Finset.mem_image.mpr ⟨ v, Finset.mem_of_mem_erase hv.1, rfl ⟩
      have hα'β' : α' < β' := by
        exact Nat.sub_lt_sub_left
          ( by linarith [ hB.1 u hu.1, hB.1 v ( Finset.mem_of_mem_erase hv.1 ) ] ) hu_gt_v
      have hmin' : ∀ z ∈ S, α' ≤ z := by
        simp +zetaDelta at *;
        simp +decide [ reflB ];
        grind
      have hmin2' : ∀ z ∈ S, z ≠ α' → β' ≤ z := by
        simp +zetaDelta at *;
        simp_all +decide [ reflB ];
        grind +qlia
      have hsum' : α' + β' < m := by
        rw [ tsub_add_tsub_comm ] <;>
          try linarith [ hB.1 u hu.1, hB.1 v ( Finset.mem_of_mem_erase hv.1 ) ];
        grind
      generalize_proofs at *; (
      -- Apply the core_step lemma to S with α' and β'.
      have h_core_step : 4 * S.card ≤ 4 * (collisions m S).card + m + 8 := by
        apply core_step hm hS hα' hβ' hα'β' hmin' hmin2' hsum' (fun S' hS' hS'_card => by
          exact le_of_not_gt fun h =>
            ih _ ( by linarith [ show #S = #B from card_reflB hB ] ) hm hS' h rfl)
      generalize_proofs at *; (
      grind +suggestions)))

end Erdos865
