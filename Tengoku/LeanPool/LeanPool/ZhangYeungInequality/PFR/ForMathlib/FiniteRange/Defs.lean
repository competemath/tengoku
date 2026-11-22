/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Tengoku.Seed.MeasureTheory.Measure.Map
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LeanPool.ZhangYeungInequality.PFR.ForMathlib.FiniteRange.Defs

Imported Lean Pool material for `LeanPool.ZhangYeungInequality.PFR.ForMathlib.FiniteRange.Defs`.
-/

@[expose] public section

/-- The property of having a finite range. -/
class FiniteRange {Ω G : Type*} (X : Ω → G) : Prop where
  finite : (Set.range X).Finite

/-- fintype structure on the range of a finite range map. -/
noncomputable abbrev FiniteRange.fintype {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Fintype (Set.range X) := hX.finite.fintype

/-- The range of a finite range map, as a finset. -/
noncomputable def FiniteRange.toFinset {Ω G : Type*} (X : Ω
  → G) [hX : FiniteRange X] : Finset G :=
    @Set.toFinset _ _ hX.fintype

/-- If the codomain of X is finite, then X has finite range. -/
instance {Ω G : Type*} (X : Ω → G) [Finite G] : FiniteRange X where
  finite := Set.toFinite (Set.range X)

/-- Functions ranging in a Finset have finite range
@isnad1 id=finitera.1h4v.s5.addfce1c0e89 from=translated src=- shape=df816e27 vocab=dba5353a
-/
lemma finiteRange_of_finset {Ω G : Type*} (f : Ω → G) (A : Finset G) (h : ∀ ω, f ω ∈ A) :
    FiniteRange f := by
  constructor
  apply Set.Finite.subset (Finset.finite_toSet A)
  intro y hy
  simp only [Set.mem_range] at hy
  rcases hy with ⟨ω, rfl⟩
  exact h ω

/--
@isnad1 id=eq.0h3v.s4.a47bc81b05bd from=translated src=- shape=24d1cee0 vocab=733aca8d
-/
lemma FiniteRange.range {Ω G : Type*} (X : Ω → G) [hX : FiniteRange X] :
    Set.range X = FiniteRange.toFinset X := by simp [FiniteRange.toFinset]

/--
@isnad1 id=mem.0h4v.s5.62cc5d3b3aea from=translated src=- shape=c8914e19 vocab=964ec056
-/
lemma FiniteRange.mem {Ω G : Type*} (X : Ω → G) [FiniteRange X] (ω : Ω) :
    X ω ∈ FiniteRange.toFinset X := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range, exists_apply_eq_apply]

/--
@isnad1 id=iff.0h4v.s5.340031eb0c45 from=translated src=- shape=36b43592 vocab=964ec056
-/
@[simp]
lemma FiniteRange.mem_iff {Ω G : Type*} (X : Ω → G) [FiniteRange X] (x : G) :
    x ∈ FiniteRange.toFinset X ↔ ∃ ω, X ω = x := by
  simp_rw [← Finset.mem_coe, ← FiniteRange.range X, Set.mem_range]

/-- Constants have finite range -/
instance {Ω G : Type*} (c : G) : FiniteRange (fun _ : Ω ↦ c) := by
  apply finiteRange_of_finset _ { c }
  simp

/-- If X has finite range, then any function of X has finite range. -/
instance {Ω G H : Type*} (X : Ω → G) (f : G
  → H) [hX : FiniteRange X] : FiniteRange (f ∘ X) where
  finite := (Set.range_comp f X) ▸ Set.Finite.image f hX.finite

/-- If X has finite range, then X of any function has finite range. -/
instance {Ω Ω' G : Type*} (X : Ω → G) (f : Ω'
  → Ω) [hX : FiniteRange X] : FiniteRange (X ∘ f) := by
  apply finiteRange_of_finset _ (FiniteRange.toFinset X)
  intro ω
  exact FiniteRange.mem X (f ω)

/-- If X, Y have finite range, then so does the pair ⟨X, Y⟩. -/
instance {Ω G H : Type*} (X : Ω → G) (Y : Ω → H) [hX : FiniteRange X] [hY : FiniteRange Y] :
    FiniteRange fun ω ↦ (X ω, Y ω) where
  finite := (hX.finite.prod hY.finite).subset (Set.range_pair_subset ..)

/-- The product of functions of finite range, has finite range.
@isnad1 id=finitera.0h4v.s5.fa8fb4d86070 from=translated src=- shape=ebc27b79 vocab=4f521af8
-/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange (X * Y) := by
  change FiniteRange ((fun p ↦ p.1 * p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

/-- The product of functions of finite range, has finite range.
@isnad1 id=finitera.0h4v.s5.77b0f2207c23 from=translated src=- shape=617c72b8 vocab=4f521af8
-/
@[to_additive /-- The sum of functions of finite range, has finite range. -/]
instance FiniteRange.mul' {Ω G : Type*} (X Y : Ω → G) [Mul G] [FiniteRange X] [FiniteRange Y] :
    FiniteRange fun ω ↦ X ω * Y ω := FiniteRange.mul ..

/-- The quotient of two functions with finite range, has finite range.
@isnad1 id=finitera.0h4v.s5.dd0ed24ccff8 from=translated src=- shape=ebc27b79 vocab=18cf73b9
-/
@[to_additive /-- The difference of functions of finite range, has finite range. -/]
instance FiniteRange.div {Ω G : Type*} (X Y : Ω → G) [Div G]
    [hX : FiniteRange X] [hY : FiniteRange Y] : FiniteRange (X/Y) := by
  change FiniteRange ((fun p ↦ p.1 / p.2) ∘ fun ω ↦ (X ω, Y ω))
  infer_instance

open MeasureTheory

/--
@isnad1 id=eq.1h4v.s6.ad531bcb2536 from=translated src=- shape=020e881c vocab=f6cf7942
-/
lemma FiniteRange.full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X) (FiniteRange.toFinset X) = μ Set.univ := by
  rw [Measure.map_apply hX (by measurability)]
  congr
  ext ω
  simp

/--
@isnad1 id=eq.1h4v.s5.69edc1e41af9 from=translated src=- shape=914d6012 vocab=12915493
-/
lemma FiniteRange.real_full {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] {X : Ω
      → G} (hX : Measurable X) [FiniteRange X] (μ : Measure Ω) :
    (μ.map X).real (FiniteRange.toFinset X) = μ.real Set.univ := by
  simp [measureReal_def, FiniteRange.full hX]

-- `AEMeasurable X μ` is needed: without it `μ.map X` is an arbitrary Dirac mass (for `μ ≠ 0`),
-- which need not be supported on the range of `X`.
/--
@isnad1 id=eq.1h4v.s6.c5bd5dac958a from=translated src=- shape=cd04aadd vocab=358962e2
-/
lemma FiniteRange.null_of_compl {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    (μ.map X) (FiniteRange.toFinset X : Set G)ᶜ = 0 := by
  rw [Measure.map_apply₀ hX (by measurability)]
  convert measure_empty (μ := μ)
  ext ω
  simp

/--
@isnad1 id=eventual.1h4v.s6.4294c7d795da from=translated src=- shape=712e80df vocab=04fad218
-/
lemma FiniteRange.ae_mem_toFinset {Ω G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    [MeasurableSingletonClass G] (μ : Measure Ω) (X : Ω → G) (hX : AEMeasurable X μ)
    [FiniteRange X] :
    ∀ᵐ x ∂(μ.map X), x ∈ (FiniteRange.toFinset X : Set G) := FiniteRange.null_of_compl μ X hX
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
