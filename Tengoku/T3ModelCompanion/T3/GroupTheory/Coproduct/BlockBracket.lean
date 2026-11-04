/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Coproduct.Graded
public import Tengoku.T3ModelCompanion.T3.GroupTheory.AssociatedGraded.Lie
public import Tengoku.Seed.Algebra.Module.Submodule.Bilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The bracket respects the two factor degrees of a coproduct

Pure blocks are the images of the factor layers and mixed blocks are the images of the
canonical tensor maps, all embedded in the actual graded Lie algebra. Only the nine blocks
of positive total degree at most three can be nonzero. The bracket adds both factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.
-/

@[expose] public section

open scoped DirectSum TensorProduct

namespace T3.Coproduct

open AssociatedGraded

variable {G H : Type*} [Group G] [Group H]
  [Fact (HasExponentThree G)] [Fact (HasExponentThree H)]

/-- The left pure component in the actual graded Lie algebra of the coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, block `Bᵢ,₀`.-/
def pureLeftBlock (i : ℕ) : Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) i).comp (mapLayer inl i))

/-- The right pure component in the actual graded Lie algebra of the coproduct.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, block `B₀,ⱼ`.-/
def pureRightBlock (j : ℕ) : Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) j).comp (mapLayer inr j))

/-- The mixed tensor component in the actual graded Lie algebra, in positive factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, block `Bᵢ,ⱼ`.-/
def mixedBlock {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    Submodule (ZMod 3) (GradedModule (Coproduct G H)) :=
  LinearMap.range ((DirectSum.lof (ZMod 3) ℕ (Layer (Coproduct G H)) (i + j)).comp
    (mixedMap hi hj))

/-- The paper's blocks, using the canonical images in the graded coproduct.
Degree zero and degrees at least four vanish in the actual graded quotients.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
def block : ℕ → ℕ → Submodule (ZMod 3) (GradedModule (Coproduct G H))
  | 0, j => pureRightBlock j
  | i + 1, 0 => pureLeftBlock (i + 1)
  | i + 1, j + 1 => mixedBlock (Nat.succ_pos i) (Nat.succ_pos j)

omit [Fact (HasExponentThree H)] in
private theorem pureLeftBlock_le_grade (i : ℕ) :
    pureLeftBlock (G := G) (H := H) i ≤ grade (Coproduct G H) i := by
  rintro x ⟨y, rfl⟩
  exact ⟨mapLayer inl i y, rfl⟩

omit [Fact (HasExponentThree G)] in
private theorem pureRightBlock_le_grade (j : ℕ) :
    pureRightBlock (G := G) (H := H) j ≤ grade (Coproduct G H) j := by
  rintro x ⟨y, rfl⟩
  exact ⟨mapLayer inr j y, rfl⟩

private theorem mixedBlock_le_grade {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    mixedBlock (G := G) (H := H) hi hj ≤ grade (Coproduct G H) (i + j) := by
  rintro x ⟨y, rfl⟩
  exact ⟨mixedMap hi hj y, rfl⟩

omit [Fact (HasExponentThree H)] in
private theorem pureLeftBlock_zero : pureLeftBlock (G := G) (H := H) 0 = ⊥ := by
  apply eq_bot_iff.mpr
  exact (pureLeftBlock_le_grade 0).trans (le_of_eq grade_zero)

omit [Fact (HasExponentThree G)] in
private theorem pureRightBlock_zero : pureRightBlock (G := G) (H := H) 0 = ⊥ := by
  apply eq_bot_iff.mpr
  exact (pureRightBlock_le_grade 0).trans (le_of_eq grade_zero)

/-- On the right axis the blocks are the canonical right pure images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
@[simp]
theorem block_zero_left (j : ℕ) : block (G := G) (H := H) 0 j = pureRightBlock j := rfl

/-- On the left axis the blocks are the canonical left pure images.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
@[simp]
theorem block_zero_right (i : ℕ) : block (G := G) (H := H) i 0 = pureLeftBlock i := by
  cases i with
  | zero => exact pureRightBlock_zero.trans pureLeftBlock_zero.symm
  | succ i => rfl

/-- In positive factor degrees the block is exactly the canonical mixed tensor image.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
theorem block_of_pos {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    block (G := G) (H := H) i j = mixedBlock hi hj := by
  cases i with
  | zero => omega
  | succ i => cases j with
    | zero => omega
    | succ j => rfl

/-- The total homogeneous degree of a block is the sum of its factor degrees.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
theorem block_le_grade (i j : ℕ) :
    block (G := G) (H := H) i j ≤ grade (Coproduct G H) (i + j) := by
  cases i with
  | zero => simpa only [block, zero_add] using pureRightBlock_le_grade j
  | succ i => cases j with
    | zero => exact pureLeftBlock_le_grade (i + 1)
    | succ j => exact mixedBlock_le_grade _ _

/-- There is no block of total degree zero.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, positive grading.-/
theorem block_zero_zero : block (G := G) (H := H) 0 0 = ⊥ := pureRightBlock_zero

/-- All blocks of total degree at least four vanish, as specified in the paper.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2.-/
theorem block_eq_bot_of_four_le {i j : ℕ} (h : 4 ≤ i + j) :
    block (G := G) (H := H) i j = ⊥ :=
  eq_bot_iff.mpr ((block_le_grade i j).trans (le_of_eq (grade_eq_bot_of_four_le h)))

/-- Bracketing a mixed `(1,1)` pure tensor with the left first layer gives its `(2,1)` component.
The left arguments occur in the cyclic order `c, a`.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2, mixed bracket formula.-/
theorem bracket_mixedMap_tmul_inl (a c : Layer G 1) (b : Layer H 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mixedMap (by decide) (by decide) (a ⊗ₜ[ZMod 3] b)) (mapLayer inl 1 c) =
      mixedMap (i := 2) (j := 1) (by decide) (by decide)
        (bracketLayer (by decide) (by decide) c a ⊗ₜ[ZMod 3] b) := by
  rw [mixedMap_tmul, mixedMap_tmul, mapLayer_bracketLayer (i := 1) (j := 1)]
  exact (bracketLayer_triple_cyclic _ _ _).trans (bracketLayer_triple_cyclic _ _ _)

/-- Bracketing a mixed `(1,1)` pure tensor with the right first layer gives the negative
`(1,2)` component, with the right arguments in their original order.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, item 2, mixed bracket formula.-/
theorem bracket_mixedMap_tmul_inr (a : Layer G 1) (b c : Layer H 1) :
    bracketLayer (i := 2) (j := 1) (by decide) (by decide)
      (mixedMap (by decide) (by decide) (a ⊗ₜ[ZMod 3] b)) (mapLayer inr 1 c) =
      -mixedMap (i := 1) (j := 2) (by decide) (by decide)
        (a ⊗ₜ[ZMod 3] bracketLayer (by decide) (by decide) b c) := by
  rw [mixedMap_tmul, mixedMap_tmul, mapLayer_bracketLayer (i := 1) (j := 1),
    bracketLayer_one_two, neg_neg]
  exact bracketLayer_triple_cyclic _ _ _

end T3.Coproduct
