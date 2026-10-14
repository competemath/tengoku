/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.LeanPool.LeanPool.CenteredMaximal.Lattice.Constants
public import Tengoku

/-!
# Level-one witnesses for the weighted lattice

The atom with index `(c, r) ∈ ℤ²` sits at `(c · hgap, r · vgap)` and has mass `colWeight c`,
which is `1` for even `c` and `heavy` for odd `c`. A *witness* for the point `(x, y)` is a side
`L ≥ 1` and a finite set `A` of atoms, all within sup-distance `L/2` of `(x, y)`, of total mass at
least `L²`: the closed square of side `L` centred at `(x, y)` then has average at least `1`.

Six explicit witnesses cover the quarter cell `[0, hgap] × [0, vgap/2]` except one open slot
(`exists_isWitness_of_nonneg`). Reflections in the two axes and translations by the period
`(2 hgap, vgap)` preserve the atom masses, so they transport witnesses to the whole plane.
-/

@[expose] public section

noncomputable section

open Finset

namespace LeanPool.CenteredMaximal.Lattice

/-- The mass of an atom in column `c`: `1` if `c` is even, `heavy` if `c` is odd. -/
def colWeight (c : ℤ) : ℝ := if Even c then 1 else heavy

/-- `(L, A)` witnesses level one at `(x, y)`: `L ≥ 1`, the atoms of `A` have total mass at least
`L²`, and every atom of `A` lies in the closed square of side `L` centred at `(x, y)`. -/
def IsWitness (x y L : ℝ) (A : Finset (ℤ × ℤ)) : Prop :=
  1 ≤ L ∧ L ^ 2 ≤ ∑ p ∈ A, colWeight p.1 ∧
    ∀ p ∈ A, |p.1 * hgap - x| ≤ L / 2 ∧ |p.2 * vgap - y| ≤ L / 2

/-- The atoms that a witness for a point of the period cell with index `(k, l)` may use. -/
def nearBox (k l : ℤ) : Finset (ℤ × ℤ) :=
  Icc (2 * k - 2) (2 * k + 2) ×ˢ Icc (l - 1) (l + 1)

/-- Reflection of atom indices in the vertical axis. -/
def negFst : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)

/-- Reflection of atom indices in the horizontal axis. -/
def negSnd : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)

/-- `negFst` negates the first coordinate.
@isnad1 id=eq.0h0v.s6.94e44e0d8754 from=translated src=- shape=427a9586 vocab=c27c5247
-/
@[simp] theorem coe_negFst : ⇑negFst = fun p ↦ (-p.1, p.2) := rfl

/-- `negSnd` negates the second coordinate.
@isnad1 id=eq.0h0v.s6.e50742d753c4 from=translated src=- shape=7c7dc22d vocab=593915fe
-/
@[simp] theorem coe_negSnd : ⇑negSnd = fun p ↦ (p.1, -p.2) := rfl

/--
@isnad1 id=eq.0h1v.s3.d625e1da3b7b from=translated src=- shape=8fc7e33b vocab=adffaed2
-/
theorem colWeight_neg (c : ℤ) : colWeight (-c) = colWeight c := by
  simp [colWeight]

/--
@isnad1 id=eq.0h2v.s4.c57a28534fe0 from=translated src=- shape=f5bf2abb vocab=cc9d31fd
-/
theorem colWeight_add_two_mul (c k : ℤ) : colWeight (c + 2 * k) = colWeight c := by
  simp [colWeight, Int.even_add, parity_simps]

/-- Reflecting the atoms in the vertical axis (`negFst`, `c ↦ -c`) turns a witness for `(x, y)`
into a witness for `(-x, y)` with the same side; `IsWitness.neg_snd` is the horizontal analogue.
@isnad1 id=iswitnes.1h4v.s5.e44542bf1652 from=translated src=- shape=bd57a6e2 vocab=ee8bdf04
-/
theorem IsWitness.neg_fst {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness (-x) y L (A.map negFst.toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [negFst, colWeight_neg] using hm, forall_mem_map.2 fun p hp ↦ ?_⟩
  simpa [negFst, neg_add_eq_sub, abs_sub_comm] using hd p hp

/-- Reflecting the atoms in the horizontal axis (`negSnd`, `r ↦ -r`) turns a witness for `(x, y)`
into a witness for `(x, -y)` with the same side; `IsWitness.neg_fst` is the vertical analogue.
@isnad1 id=iswitnes.1h4v.s5.e17b032091cf from=translated src=- shape=b200d137 vocab=8317a49b
-/
theorem IsWitness.neg_snd {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness x (-y) L (A.map negSnd.toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [negSnd] using hm, forall_mem_map.2 fun p hp ↦ ?_⟩
  simpa [negSnd, neg_add_eq_sub, abs_sub_comm] using hd p hp

/-- Translating the atoms by `(2 * k, l)` turns a witness for `(x, y)` into a witness for
`(x + 2 * k * hgap, y + l * vgap)` with the same side. The column shift is even because `colWeight`
has period `2` (`colWeight_add_two_mul`); `map_addRight_subset_nearBox` tracks the moved atoms.
@isnad1 id=iswitnes.1h6v.s6.2a4734fd65ea from=translated src=- shape=cd1adbe1 vocab=7d49e2fc
-/
theorem IsWitness.translate {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) (k l : ℤ) :
    IsWitness (x + 2 * k * hgap) (y + l * vgap) L
      (A.map (Equiv.addRight ((2 * k, l) : ℤ × ℤ)).toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [colWeight_add_two_mul] using hm, forall_mem_map.2 fun p hp ↦ ?_⟩
  simpa [add_mul] using hd p hp

/-- Reflecting in the vertical axis (`negFst`) keeps a subset of `nearBox 0 0` inside
`nearBox 0 0`: the atom-set companion of `IsWitness.neg_fst`.
@isnad1 id=le.1h1v.s6.ff2e89cf4d45 from=translated src=- shape=3587e40b vocab=65b85223
-/
theorem map_negFst_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negFst.toEmbedding ⊆ nearBox 0 0 := by
  grind [nearBox, Function.Embedding.coeFn_mk, coe_negFst]

/-- Reflecting in the horizontal axis (`negSnd`) keeps a subset of `nearBox 0 0` inside
`nearBox 0 0`: the atom-set companion of `IsWitness.neg_snd`.
@isnad1 id=le.1h1v.s6.6024dfc11407 from=translated src=- shape=3587e40b vocab=0251aac1
-/
theorem map_negSnd_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negSnd.toEmbedding ⊆ nearBox 0 0 := by
  grind [nearBox, Function.Embedding.coeFn_mk, coe_negSnd]

/-- Translating a subset of `nearBox 0 0` by `(2 * k, l)` lands in `nearBox k l`: the atom-set
companion of `IsWitness.translate`.
@isnad1 id=le.1h3v.s6.f97a530379c7 from=translated src=- shape=475096f8 vocab=a97724a4
-/
theorem map_addRight_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) (k l : ℤ) :
    A.map (Equiv.addRight ((2 * k, l) : ℤ × ℤ)).toEmbedding ⊆ nearBox k l := by
  grind [nearBox, Function.Embedding.coeFn_mk, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]

/-! ### The six witnesses -/

/-- The light atom at the origin, side `1`.
@isnad1 id=iswitnes.2h2v.s6.b72c899b06f8 from=translated src=- shape=a06eabb2 vocab=6e1ec41d
-/
theorem isWitness_light {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    IsWitness x y 1 {(0, 0)} := by
  refine ⟨le_rfl, by simp [colWeight], ?_⟩
  simpa [abs_neg] using And.intro hx hy

/-- Heavy, light, heavy atoms (columns `-1, 0, 1`) in rows `0` and `1`, side `2 hgap + 1`; their
total mass `4 heavy + 2` is exactly the area `(2 hgap + 1)²`.
@isnad1 id=iswitnes.4h2v.s8.b349906234cd from=translated src=- shape=4a8eeded vocab=d188da75
-/
theorem isWitness_hlh2 {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hy : 1 / 2 ≤ y)
    (hy' : y ≤ vgap / 2) :
    IsWitness x y (2 * hgap + 1) {(-1, 0), (0, 0), (1, 0), (-1, 1), (0, 1), (1, 1)} := by
  norm_num [IsWitness, colWeight, abs_le]
  split_ands <;> linarith [two_mul_hgap_add_one_sq, vgap_eq]

/-- A light and a heavy atom (columns `0, 1`) in row `0`, side `root`; their total mass `1 + heavy`
is exactly the area `root²`.
@isnad1 id=iswitnes.4h2v.s7.0c1cd5e0d049 from=translated src=- shape=13a57dfa vocab=c6d6b0c1
-/
theorem isWitness_lh1 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ root / 2) (hy : 0 ≤ y)
    (hy' : y ≤ root / 2) : IsWitness x y root {(0, 0), (1, 0)} := by
  norm_num [IsWitness, colWeight, abs_le]
  split_ands <;> linarith [one_add_heavy, two_mul_hgap_sub_one]

/-- Light and heavy atoms (columns `0, 1`) in rows `0` and `1`, side `sideLH2`; their total mass
`2 (1 + heavy)` is exactly the area `sideLH2²`.
@isnad1 id=iswitnes.4h2v.s8.08aee3a250d4 from=translated src=- shape=6a55d61b vocab=1a95e85e
-/
theorem isWitness_lh2 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ sideLH2 / 2)
    (hy : vgap - sideLH2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLH2 {(0, 0), (1, 0), (0, 1), (1, 1)} := by
  norm_num [IsWitness, colWeight, abs_le]
  split_ands <;> linarith [sideLH2_sq, two_mul_hgap_sub_one, root_le_sideLH2, hgap_pos, vgap_gt]

/-- One heavy atom (column `1`, row `0`), side `sideH1`; its mass `heavy` is exactly the area
`sideH1²`.
@isnad1 id=iswitnes.4h2v.s6.9fd59a9d4f12 from=translated src=- shape=4c34828e vocab=4dbb003d
-/
theorem isWitness_h1 {x y : ℝ} (hx : hgap - sideH1 / 2 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ sideH1 / 2) : IsWitness x y sideH1 {(1, 0)} := by
  norm_num [IsWitness, colWeight, abs_le]
  split_ands <;> linarith [sideH1_sq, one_le_sideH1]

/-- Light, heavy, light atoms (columns `0, 1, 2`) in rows `0` and `1`, side `sideLHL2`; their total
mass `2 (2 + heavy)` is exactly the area `sideLHL2²`.
@isnad1 id=iswitnes.4h2v.s8.018188b7e6f8 from=translated src=- shape=297af1e9 vocab=04da6dbb
-/
theorem isWitness_lhl2 {x y : ℝ} (hx : 2 * hgap - sideLHL2 / 2 ≤ x) (hx' : x ≤ hgap)
    (hy : vgap - sideLHL2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLHL2 {(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)} := by
  norm_num [IsWitness, colWeight, abs_le]
  split_ands <;> linarith [sideLHL2_sq, vgap_gt, hgap_pos]

/-! ### Coverage -/

private theorem exists_isWitness_of_root_div_two_le {x y : ℝ} (hx : root / 2 ≤ x) (hx' : x ≤ hgap)
    (hy : 0 ≤ y) (hy' : y ≤ vgap / 2) (hslot : ¬ (x < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < y ∧
      y < vgap - sideLH2 / 2)) : ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  -- `h1` below the slot, `lhl2` to its right, `lh2` above it
  rcases le_or_gt y (sideH1 / 2) with hy₁ | hy₁
  · exact ⟨_, _, by decide,
      isWitness_h1 (by linarith [two_mul_hgap_sub_one, one_le_sideH1]) hx' hy hy₁⟩
  rcases le_or_gt (2 * hgap - sideLHL2 / 2) x with hx₁ | hx₁
  · exact ⟨_, _, by decide, isWitness_lhl2 hx₁ hx' (by linarith [vgap_sub_le_sideH1]) hy'⟩
  exact ⟨_, _, by decide, isWitness_lh2 (by linarith [one_le_root])
    (by linarith [four_mul_hgap_sub_le_sideLH2]) (not_lt.1 fun h ↦ hslot ⟨hx₁, hy₁, h⟩) hy'⟩

/-- The six witnesses cover the quarter cell `[0, hgap] × [0, vgap/2]` except the open slot
`(root/2, 2 hgap - sideLHL2/2) × (sideH1/2, vgap - sideLH2/2)`, using only atoms of `nearBox 0 0`.
`exists_isWitness_of_abs` extends this to the whole period cell by reflection.
@isnad1 id=ex.5h2v.s7.4994b9d5ab7d from=translated src=- shape=045f1bb4 vocab=b66e4d90
-/
theorem exists_isWitness_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ vgap / 2) (hslot : ¬ (root / 2 < x ∧ x < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < y ∧
      y < vgap - sideLH2 / 2)) : ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  -- `x ≤ 1/2`: `light` up to `y = 1/2`, `hlh2` above
  rcases le_or_gt x (1 / 2) with h₁ | h₁
  · rcases le_or_gt y (1 / 2) with h₂ | h₂
    · exact ⟨_, _, by decide, isWitness_light ((abs_of_nonneg hx).trans_le h₁)
        ((abs_of_nonneg hy).trans_le h₂)⟩
    · exact ⟨_, _, by decide, isWitness_hlh2 hx h₁ h₂.le hy'⟩
  -- `1/2 < x ≤ root/2`: `lh1` up to `y = root/2`, `lh2` above
  rcases le_or_gt x (root / 2) with h₃ | h₃
  · rcases le_or_gt y (root / 2) with h₄ | h₄
    · exact ⟨_, _, by decide, isWitness_lh1 h₁.le h₃ hy h₄⟩
    · exact ⟨_, _, by decide, isWitness_lh2 h₁.le (by linarith [root_le_sideLH2])
        (by linarith [two_mul_vgap_le_root_add_sideLH2]) hy'⟩
  -- `root/2 < x`: around the slot
  exact exists_isWitness_of_root_div_two_le h₃.le hx' hy hy' fun h ↦ hslot ⟨h₃, h⟩

/-- Every point of the period cell `[-hgap, hgap] × [-vgap/2, vgap/2]` outside the open slot of
`exists_isWitness_of_nonneg` and its reflections in one or both axes has a level-one witness whose
atoms lie in `nearBox 0 0`. This is the whole-cell form of `exists_isWitness_of_nonneg`;
`exists_isWitness_of_mem_goodCopy` moves it to the cell with index `(k, l)`.
@isnad1 id=ex.3h2v.s7.a8dd5db27170 from=translated src=- shape=e57e35b0 vocab=8a99bc5c
-/
theorem exists_isWitness_of_abs {x y : ℝ} (hx : |x| ≤ hgap) (hy : |y| ≤ vgap / 2)
    (hslot : ¬ (root / 2 < |x| ∧ |x| < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < |y| ∧
      |y| < vgap - sideLH2 / 2)) : ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  -- a witness for the point `(|x|, |y|)` of the quarter cell
  obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_nonneg (abs_nonneg x) hx (abs_nonneg y) hy hslot
  -- `|x|` is `x` or `-x`; in the second case reflect the witness in the vertical axis
  obtain ⟨L, A, hA, hw⟩ : ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x |y| L A :=
    (abs_choice x).elim (fun h ↦ ⟨L, A, hA, h ▸ hw⟩)
      fun h ↦ ⟨L, _, map_negFst_subset_nearBox hA, by simpa [h] using hw.neg_fst⟩
  -- `|y|` is `y` or `-y`; in the second case reflect the witness in the horizontal axis
  exact (abs_choice y).elim (fun h ↦ ⟨L, A, hA, h ▸ hw⟩)
    fun h ↦ ⟨L, _, map_negSnd_subset_nearBox hA, by simpa [h] using hw.neg_snd⟩

end LeanPool.CenteredMaximal.Lattice
