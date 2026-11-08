module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.Design23632Forced
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness of the `2-(6,3,2)` design up to relabeling

This file proves Lemma `23632_unique` (up to relabeling) from the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`.

## Main definitions
* `Design23632.mapDesign`

## Main statements
* `Design23632.Is23632.map`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

namespace Design23632

open scoped BigOperators

/-!
## Transporting designs by a point permutation
-/

/-- The embedding of blocks induced by a permutation of points.-/
public def BlockMap (σ : Equiv Point Point) : Block ↪ Block :=
  { toFun := fun B => B.map σ.toEmbedding
    inj' := Finset.map_injective σ.toEmbedding }

/-- Transport a design `T` by a point permutation `σ`.-/
@[expose] public def mapDesign (σ : Equiv Point Point) (T : Finset Block) : Finset Block :=
  T.map (BlockMap σ)

/-- Membership characterization for `mapDesign`.-/
@[simp] public lemma mem_mapDesign {σ : Equiv Point Point} {T : Finset Block} {B : Block} :
    B ∈ mapDesign σ T ↔ ∃ B0 ∈ T, B = B0.map σ.toEmbedding := by
  constructor
  · intro hB
    rcases Finset.mem_map.1 hB with ⟨B0, hB0, rfl⟩
    exact ⟨B0, hB0, rfl⟩
  · rintro ⟨B0, hB0, rfl⟩
    exact Finset.mem_map.2 ⟨B0, hB0, rfl⟩

attribute [grind =] mem_mapDesign

/-- `mapDesign` preserves cardinality.-/
@[simp] public lemma card_mapDesign (σ : Equiv Point Point) (T : Finset Block) :
    (mapDesign σ T).card = T.card := by
  simp [mapDesign]

@[simp] lemma mem_map_block {σ : Equiv Point Point} {B : Block} {x : Point} :
    x ∈ B.map σ.toEmbedding ↔ σ.symm x ∈ B := by
  simp

attribute [grind =] mem_map_block

/-!
## Choosing a permutation sending a triple to `012`
-/

lemma exists_perm_send_triple
    {x y z : Point} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ σ : Equiv Point Point, σ x = 0 ∧ σ y = 1 ∧ σ z = 2 := by
  let σ₁ : Equiv Point Point := Equiv.swap x 0
  have hx0 : σ₁ x = 0 := by simp [σ₁]
  have hy₁0 : σ₁ y ≠ 0 := by
    intro hy0
    have : σ₁ x = σ₁ y := by simpa [hx0] using hy0.symm
    exact hxy (σ₁.injective this)
  let σ₂ : Equiv Point Point := Equiv.swap (σ₁ y) 1
  have hσ₂_fix0 : σ₂ 0 = 0 := by
    have h0ne : (0 : Point) ≠ σ₁ y := by
      intro h
      exact hy₁0 (by simp [h])
    have h0ne1 : (0 : Point) ≠ 1 := by decide
    simpa [σ₂] using (Equiv.swap_apply_of_ne_of_ne h0ne h0ne1)
  have hy1 : (σ₁.trans σ₂) y = 1 := by
    simp [Equiv.trans_apply, σ₂]
  have hx0' : (σ₁.trans σ₂) x = 0 := by
    simp [Equiv.trans_apply, hx0, hσ₂_fix0]
  let z₂ : Point := (σ₁.trans σ₂) z
  have hz₂_ne0 : z₂ ≠ 0 := by
    intro h
    have : (σ₁.trans σ₂) x = (σ₁.trans σ₂) z := by simpa [z₂, hx0'] using h.symm
    exact hxz ((σ₁.trans σ₂).injective this)
  have hz₂_ne1 : z₂ ≠ 1 := by
    intro h
    have : (σ₁.trans σ₂) y = (σ₁.trans σ₂) z := by simpa [z₂, hy1] using h.symm
    exact hyz ((σ₁.trans σ₂).injective this)
  let σ₃ : Equiv Point Point := Equiv.swap z₂ 2
  have hσ₃_fix0 : σ₃ 0 = 0 := by
    have h0ne : (0 : Point) ≠ z₂ := by
      intro h
      exact hz₂_ne0 (by simp [h])
    have h0ne2 : (0 : Point) ≠ 2 := by decide
    simpa [σ₃] using (Equiv.swap_apply_of_ne_of_ne h0ne h0ne2)
  have hσ₃_fix1 : σ₃ 1 = 1 := by
    have h1ne : (1 : Point) ≠ z₂ := by
      intro h
      exact hz₂_ne1 (by simp [h])
    have h1ne2 : (1 : Point) ≠ 2 := by decide
    simpa [σ₃] using (Equiv.swap_apply_of_ne_of_ne h1ne h1ne2)
  refine ⟨(σ₁.trans σ₂).trans σ₃, ?_, ?_, ?_⟩
  · simp [Equiv.trans_apply, hx0', hσ₃_fix0]
  · simp [Equiv.trans_apply, hy1, hσ₃_fix1]
  · simp [Equiv.trans_apply, σ₃, z₂]

/-!
## The other block through a pair
-/

lemma third_point_in_345 {u : Point} (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hu2 : u ≠ 2) :
    u = 3 ∨ u = 4 ∨ u = 5 := by
  fin_cases u
  · cases hu0 rfl
  · cases hu1 rfl
  · cases hu2 rfl
  · left; rfl
  · right; left; rfl
  · right; right; rfl

lemma card_three_blocks {B₁ B₂ B₃ : Block} (h12 : B₁ ≠ B₂) (h13 : B₁ ≠ B₃) (h23 : B₂ ≠ B₃) :
    ({B₁, B₂, B₃} : Finset Block).card = 3 := by
  simpa using (Finset.card_eq_three.2 ⟨B₁, B₂, B₃, h12, h13, h23, rfl⟩)

lemma exists_third_345
    {a b : Point} (ha : a = 3 ∨ a = 4 ∨ a = 5) (hb : b = 3 ∨ b = 4 ∨ b = 5) (hab : a ≠ b) :
    ∃ d : Point,
      (d = 3 ∨ d = 4 ∨ d = 5) ∧ d ≠ a ∧ d ≠ b ∧
        ({a, b, d} : Finset Point) = ({3, 4, 5} : Finset Point) := by
  let S : Finset Point := ({3, 4, 5} : Finset Point)
  have haS : a ∈ S := by
    rcases ha with rfl | rfl | rfl <;> simp [S]
  have hbS : b ∈ S := by
    rcases hb with rfl | rfl | rfl <;> simp [S]
  have hbSa : b ∈ S.erase a := by
    simp [Finset.mem_erase, hbS, hab.symm]
  have hcardEraseA : (S.erase a).card = 2 := by
    simpa [S] using (Finset.card_erase_of_mem haS)
  have hcardEraseAB : ((S.erase a).erase b).card = 1 := by
    simpa [hcardEraseA] using (Finset.card_erase_of_mem hbSa)
  rcases Finset.card_eq_one.1 hcardEraseAB with ⟨d, hd⟩
  have hdMem : d ∈ (S.erase a).erase b := by simp [hd]
  have hdS : d ∈ S := (Finset.mem_erase.1 (Finset.mem_erase.1 hdMem).2).2
  have hda : d ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hdMem).2).1
  have hdb : d ≠ b := (Finset.mem_erase.1 hdMem).1
  have hd345 : d = 3 ∨ d = 4 ∨ d = 5 := by
    simpa [S] using hdS
  have hsubset : ({a, b, d} : Finset Point) ⊆ S := by
    intro t ht
    rcases (by simpa using ht) with rfl | rfl | rfl
    · exact haS
    · exact hbS
    · exact hdS
  have hcardABD : ({a, b, d} : Finset Point).card = 3 := by
    simpa using (Finset.card_eq_three.2 ⟨a, b, d, hab, hda.symm, hdb.symm, rfl⟩)
  have hcardS : S.card = 3 := by decide
  have hEq : ({a, b, d} : Finset Point) = S :=
    Finset.eq_of_subset_of_card_le hsubset (by simp [hcardABD, hcardS])
  exact ⟨d, hd345, hda, hdb, by simpa [S] using hEq⟩

lemma exists_perm_fix012_send_abc
    {a b c : Point}
    (ha : a = 3 ∨ a = 4 ∨ a = 5)
    (hb : b = 3 ∨ b = 4 ∨ b = 5)
    (hc : c = 3 ∨ c = 4 ∨ c = 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ τ : Equiv Point Point,
      τ 0 = 0 ∧ τ 1 = 1 ∧ τ 2 = 2 ∧ τ a = 4 ∧ τ b = 3 ∧ τ c = 5 := by
  rcases ha with ha3 | ha4 | ha5
  · subst ha3
    rcases hb with hb3 | hb4 | hb5
    · cases hab (by simp [hb3])
    · subst hb4
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hac rfl
      · subst hc4; cases hbc rfl
      · subst hc5
        refine ⟨Equiv.swap 3 4, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    · subst hb5
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hac rfl
      · subst hc4
        refine ⟨(Equiv.swap 3 4).trans (Equiv.swap 3 5), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc5; cases hbc rfl
  · subst ha4
    rcases hb with hb3 | hb4 | hb5
    · subst hb3
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hbc rfl
      · subst hc4; cases hac rfl
      · subst hc5
        refine ⟨Equiv.refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
    · cases hab (by simp [hb4])
    · subst hb5
      rcases hc with hc3 | hc4 | hc5
      · subst hc3
        refine ⟨Equiv.swap 3 5, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc4; cases hac rfl
      · subst hc5; cases hbc rfl
  · subst ha5
    rcases hb with hb3 | hb4 | hb5
    · subst hb3
      rcases hc with hc3 | hc4 | hc5
      · subst hc3; cases hbc rfl
      · subst hc4
        refine ⟨Equiv.swap 4 5, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc5; cases hac rfl
    · subst hb4
      rcases hc with hc3 | hc4 | hc5
      · subst hc3
        refine ⟨(Equiv.swap 3 5).trans (Equiv.swap 3 4), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
      · subst hc4; cases hbc rfl
      · subst hc5; cases hac rfl
    · cases hab (by simp [hb5])

end Design23632

end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
