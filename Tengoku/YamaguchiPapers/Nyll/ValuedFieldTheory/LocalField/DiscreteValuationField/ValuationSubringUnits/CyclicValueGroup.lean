/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
import Tengoku.Seed.Algebra.Order.Group.Cyclic
import Tengoku.Seed.Algebra.Group.Int.TypeTags
import Tengoku.Seed.Data.Int.WithZero
import Tengoku.Seed.RingTheory.Valuation.Archimedean
import Tengoku.Seed.RingTheory.Valuation.RankOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
-/

noncomputable section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

/-- A nontrivial `ℤᵐ⁰`-valued valuation is rank one via the standard strictly
monotone embedding `ℤᵐ⁰ -> ℝ≥0`.  This is kept as an explicit definition, not
a global instance, so later finite-dimensional closedness arguments can opt in
without changing typeclass search everywhere.-/
@[implicit_reducible]
noncomputable def rankOne
    [Ring R]
    (v : _root_.Valuation R ℤᵐ⁰) [v.IsNontrivial] : v.RankOne where
  hom' :=
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
      MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' :=
    (WithZeroMulInt.toNNReal_strictMono
      (by norm_num : (1 : ℝ≥0) < 2)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial :=
    _root_.Valuation.IsNontrivial.exists_val_nontrivial (v := v)

/-- A cyclic linearly ordered commutative group is multiplicatively
Archimedean.  Mathlib supplies the valuation-theoretic equivalence
`RankOne <-> MulArchimedean`; this lemma supplies the missing ordered-group
input for actual valuation ranges whose unit group has already been proved
cyclic.-/
theorem isCyclic_mulArchimedean
    (G : Type*) [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [IsCyclic G] :
    MulArchimedean G := by
  classical
  by_cases hsub : Subsingleton G
  · refine ⟨fun _ y hy => ?_⟩
    exact (hy.ne' (Subsingleton.elim y 1)).elim
  have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
  let a : G := LinearOrderedCommGroup.Subgroup.genLTOne (⊤ : Subgroup G)
  let b : G := a⁻¹
  have hb : 1 < b := by
    have ha : a < 1 := by
      simpa [a] using
      LinearOrderedCommGroup.Subgroup.genLTOne_lt_one (⊤ : Subgroup G)
    simpa [b] using (one_lt_inv'.2 ha)
  have hbtop : Subgroup.zpowers b = (⊤ : Subgroup G) := by
    have hatop : Subgroup.zpowers a = (⊤ : Subgroup G) := by
      simp [a]
    simpa [b, Subgroup.zpowers_inv] using hatop
  refine ⟨fun x y hy => ?_⟩
  have hxmem : x ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  have hymem : y ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  rw [Subgroup.mem_zpowers_iff] at hxmem hymem
  rcases hxmem with ⟨m, rfl⟩
  rcases hymem with ⟨l, hy_eq⟩
  rw [← hy_eq] at hy
  have hlpos : 0 < l :=
    (zpow_lt_zpow_iff_right hb).1 (by simpa using hy)
  obtain ⟨n, hn⟩ := Archimedean.arch m hlpos
  refine ⟨n, ?_⟩
  rw [← hy_eq]
  have hmn : m ≤ l * (n : ℤ) := by
    simpa [nsmul_eq_mul, mul_comm] using hn
  calc
    b ^ m ≤ b ^ (l * (n : ℤ)) :=
      (zpow_le_zpow_iff_right hb).2 hmn
    _ = (b ^ l) ^ n := by
      rw [zpow_mul, zpow_natCast]

/-- If the nonzero part of a value group is cyclic, the value group is
multiplicatively Archimedean.-/
theorem units_isCyclic_mulArchimedean
    (Gamma : Type x) [LinearOrderedCommGroupWithZero Gamma]
    [IsCyclic Gammaˣ] :
    MulArchimedean Gamma := by
  have : MulArchimedean Gammaˣ :=
    isCyclic_mulArchimedean Gammaˣ
  exact (Units.mulArchimedean_iff (G₀ := Gamma)).1 inferInstance

open LinearOrderedCommGroup

end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
