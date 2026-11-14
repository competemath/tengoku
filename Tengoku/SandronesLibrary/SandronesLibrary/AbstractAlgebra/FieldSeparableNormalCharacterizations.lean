/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
import Tengoku.SandronesLibrary.SandronesLibrary.AbstractAlgebra.PolynomialFactorization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# 抽象代数 / 可分性与正规性的根论刻画

本模块是 A3.8 的独立第二批交付。在既有 `SeparablePolynomial` 与
`NormalExtension` 定义保持冻结的前提下，它把可分多项式的“无重根”
语义落实为显式扩域中的根重数判据，并把正规扩张改写为教材常用的
“不可约多项式一旦在扩域中有根，就在该扩域中完全分裂”。

根重数由 A3.4 正式 `PolynomialFactorization` 承载。公开接口继续只使用
显式 `FieldEmbedding`、正式 `Polynomial`、`evaluateOver`、
`PolynomialSplitsIn` 以及 A3.5--A3.8 的教材谓词。Mathlib 的根多重集与
可分性接口只在私有证明桥中出现，不改变第一批定义层。

> **Entry**: abstract-algebra.field.separable-normal-characterizations
-/

namespace SandronesLibrary.AbstractAlgebra.FieldSeparableNormal

open Polynomial
open SandronesLibrary.AbstractAlgebra.FieldExtension
open SandronesLibrary.AbstractAlgebra.FieldDegree
open SandronesLibrary.AbstractAlgebra.FieldSplitting

/-! ## 私有 Mathlib 证明后端 -/

-- 可分性沿显式域嵌入映射后给出逐根的重数上界。
private theorem mapped_rootMultiplicity_le_one_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {p : Polynomial K}
    (hp : SeparablePolynomial p) (x : L) :
    (p.map e.toRingHom).rootMultiplicity x ≤ 1 := by
  apply Polynomial.rootMultiplicity_le_one_of_separable
  rw [Polynomial.separable_def']
  exact (separablePolynomial_map_iff e p).mpr hp

-- 非零且已经分裂时，逐根重数至多为一恰好刻画可分性。
private theorem separable_iff_mapped_rootMultiplicity_le_one_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {p : Polynomial K}
    (hp : p ≠ 0) (hs : PolynomialSplitsIn e p) :
    SeparablePolynomial p ↔
      ∀ x : L, (p.map e.toRingHom).rootMultiplicity x ≤ 1 := by
  constructor
  · intro hsep x
    exact mapped_rootMultiplicity_le_one_bridge e hsep x
  · intro hmult
    have hmap0 : p.map e.toRingHom ≠ 0 := Polynomial.map_ne_zero hp
    have hnodup : (p.map e.toRingHom).roots.Nodup := by
      classical
      rw [Multiset.nodup_iff_count_le_one]
      intro x
      rw [Polynomial.count_roots]
      exact hmult x
    have hsepMap : (p.map e.toRingHom).Separable :=
      (Polynomial.nodup_roots_iff_of_splits hmap0 hs).mp hnodup
    have hsep : p.Separable :=
      (Polynomial.separable_map e.toRingHom).mp hsepMap
    rw [Polynomial.separable_def'] at hsep
    exact hsep

-- 正规扩张与“不可约多项式一旦有根便完全分裂”的教材刻画桥。
private theorem normalExtension_irreducible_root_bridge
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    NormalExtension e ↔
      AlgebraicExtension e ∧
        ∀ p : Polynomial K,
          Irreducible p →
            (∃ x : L, evaluateOver e p x = 0) →
              PolynomialSplitsIn e p := by
  constructor
  · rintro ⟨halg, hminSplits⟩
    refine ⟨halg, ?_⟩
    intro p hp ⟨x, hx⟩
    have hxalg : AlgebraicElement e x := halg x
    obtain ⟨q, hq⟩ := minimalPolynomialOf_exists e hxalg
    have hqirr : Irreducible q :=
      minimalPolynomialOf_irreducible e hxalg hq
    have hq_dvd_p : q ∣ p := hq.2.2 p hx
    have hp_dvd_q : p ∣ q := hqirr.dvd_symm hp hq_dvd_p
    have hqSplits : PolynomialSplitsIn e q := hminSplits x q hq
    apply Polynomial.Splits.of_dvd hqSplits
    · exact Polynomial.map_ne_zero (minimalPolynomialOf_ne_zero e hq)
    · exact Polynomial.map_dvd e.toRingHom hp_dvd_q
  · rintro ⟨halg, hirrSplits⟩
    refine ⟨halg, ?_⟩
    intro x p hp
    apply hirrSplits p (minimalPolynomialOf_irreducible e (halg x) hp)
    exact ⟨x, hp.2.1⟩

/-! ## 可分多项式的根重数刻画 -/

/-- **可分多项式在扩域中没有重根**：可分多项式映入任意显式扩域后，
每个元素作为根的重数都至多为一。非根的根重数为零，因此也自然满足
同一上界。

> **Entry**: abstract-algebra.field.separable-normal-characterizations-/
theorem separablePolynomial_rootMultiplicity_le_one
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {p : Polynomial K}
    (hp : SeparablePolynomial p) (x : L) :
    (p.map e.toRingHom).rootMultiplicity x ≤ 1 :=
  mapped_rootMultiplicity_le_one_bridge e hp x

/-- **分裂多项式的根重数判据**：设非零多项式在指定扩域中已经分裂，
则它可分，当且仅当映射后的多项式在扩域中每一点的根重数都至多为一。
分裂假设保证逐根检查覆盖多项式的全部不可约因子。

> **Entry**: abstract-algebra.field.separable-normal-characterizations-/
theorem separablePolynomial_iff_rootMultiplicity_le_one_of_splits
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) {p : Polynomial K}
    (hp : p ≠ 0) (hs : PolynomialSplitsIn e p) :
    SeparablePolynomial p ↔
      ∀ x : L, (p.map e.toRingHom).rootMultiplicity x ≤ 1 :=
  separable_iff_mapped_rootMultiplicity_le_one_bridge e hp hs

/-! ## 正规扩张的不可约多项式刻画 -/

/-- **正规扩张的不可约多项式判据**：一个显式域扩张正规，当且仅当
它首先是代数扩张，并且每个在目标域中至少获得一个根的基域不可约
多项式，都沿该嵌入在目标域中完全分裂。

> **Entry**: abstract-algebra.field.separable-normal-characterizations-/
theorem normalExtension_iff_irreducible_with_root_splits
    {K L : Type*} [Field K] [Field L]
    (e : FieldEmbedding K L) :
    NormalExtension e ↔
      AlgebraicExtension e ∧
        ∀ p : Polynomial K,
          Irreducible p →
            (∃ x : L, evaluateOver e p x = 0) →
              PolynomialSplitsIn e p :=
  normalExtension_irreducible_root_bridge e

end SandronesLibrary.AbstractAlgebra.FieldSeparableNormal
