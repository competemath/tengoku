import Tengoku.RainichKaluzaReconstruction.RainichKaluza.LorentzianScalarBlock
import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative-sign ambiguity

The complementary Sylvester equation fixes the two diagonal entries but not
the relative sign of the two scalar components.  This file proves that the two
resulting mixed tensors are exchanged by reflection of one eigendirection.
Consequently curvature algebra alone does not select a unique scalar tensor on
the genuinely two-component branch.
-/

namespace RainichKaluza

/-- Extensionality for the lightweight mixed-block structure.
@isnad1 id=eq.4h2v.s5.6b4a7c96d55d from=translated src=- shape=b72505ad vocab=a64ad705
-/
theorem mixedBlock_ext {left right : MixedBlock}
    (haa : left.aa = right.aa) (hab : left.ab = right.ab)
    (hba : left.ba = right.ba) (hbb : left.bb = right.bb) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Flip both off-diagonal entries while leaving the spectral diagonals fixed.-/
def flipRelativeSign (block : MixedBlock) : MixedBlock where
  aa := block.aa
  ab := -block.ab
  ba := -block.ba
  bb := block.bb

/--
@isnad1 id=eq.0h1v.s3.ca38411a05cc from=translated src=- shape=47dcad53 vocab=c6820774
-/
@[simp]
theorem flipRelativeSign_involutive (block : MixedBlock) :
    flipRelativeSign (flipRelativeSign block) = block := by
  cases block
  simp [flipRelativeSign]

/-- Negating exactly one scalar component produces the relative-sign flip.
@isnad1 id=eq.0h4v.s4.ee406a99822d from=translated src=- shape=675f9311 vocab=916e3ae8
-/
theorem scalarMixedBlock_neg_second
    (epsilonA epsilonB x y : ℝ) :
    scalarMixedBlockOfComponents epsilonA epsilonB x (-y) =
      flipRelativeSign
        (scalarMixedBlockOfComponents epsilonA epsilonB x y) := by
  apply mixedBlock_ext <;>
    simp [scalarMixedBlockOfComponents, scalarMixedDiagonal,
      scalarMixedOffDiagonal, flipRelativeSign] <;>
    ring

/-- The Sylvester equation is invariant under the relative-sign flip.
@isnad1 id=iff.0h4v.s4.3c8aee6a8141 from=translated src=- shape=b77ee48c vocab=3c278c14
-/
theorem solvesComplementaryBlock_flip_iff
    (a b qSq : ℝ) (block : MixedBlock) :
    SolvesComplementaryBlock a b qSq (flipRelativeSign block) ↔
      SolvesComplementaryBlock a b qSq block := by
  simp [SolvesComplementaryBlock, flipRelativeSign]

/-- Equal component squares give either the same scalar tensor or its unique
relative-sign flip.  The simultaneous global sign does not change the tensor.
@isnad1 id=or.2h6v.s6.ca7d62c8cce9 from=translated src=- shape=4d9c7f27 vocab=b1252bae
-/
theorem scalarMixedBlock_eq_or_flip_of_sq_eq_sq
    (epsilonA epsilonB x y x' y' : ℝ)
    (hxSq : x ^ 2 = x' ^ 2)
    (hySq : y ^ 2 = y' ^ 2) :
    scalarMixedBlockOfComponents epsilonA epsilonB x' y' =
        scalarMixedBlockOfComponents epsilonA epsilonB x y ∨
      scalarMixedBlockOfComponents epsilonA epsilonB x' y' =
        flipRelativeSign
          (scalarMixedBlockOfComponents epsilonA epsilonB x y) := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hxSq with hxx | hxx
  · have hx' : x' = x := hxx.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hySq with hyy | hyy
    · exact Or.inl (by rw [hx', hyy.symm])
    · have hy' : y' = -y := by linarith
      exact Or.inr (by rw [hx', hy', scalarMixedBlock_neg_second])
  · have hx' : x' = -x := by linarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hySq with hyy | hyy
    · have hy' : y' = y := hyy.symm
      apply Or.inr
      apply mixedBlock_ext <;>
        simp [scalarMixedBlockOfComponents, scalarMixedDiagonal,
          scalarMixedOffDiagonal, flipRelativeSign, hx', hy'] <;>
        ring
    · have hy' : y' = -y := by linarith
      apply Or.inl
      apply mixedBlock_ext <;>
        simp [scalarMixedBlockOfComponents, scalarMixedDiagonal,
          scalarMixedOffDiagonal, hx', hy']

/-- **Classification of scalar-generated reconstruction solutions.** On the
generic branch `a ≠ b`, any two scalar-generated complementary solutions are
the same mixed tensor or the relative-sign reflection of one another.
@isnad1 id=or.5h9v.s6.c3d3bb9a7333 from=translated src=- shape=26b15d50 vocab=d96138ea
-/
theorem scalarComplementarySolutions_eq_or_flip
    (a b qSq epsilonA epsilonB x y x' y' : ℝ)
    (hab : a ≠ b)
    (hepsilonA : epsilonA ^ 2 = 1)
    (hepsilonB : epsilonB ^ 2 = 1)
    (hsolves : SolvesComplementaryBlock a b qSq
      (scalarMixedBlockOfComponents epsilonA epsilonB x y))
    (hsolves' : SolvesComplementaryBlock a b qSq
      (scalarMixedBlockOfComponents epsilonA epsilonB x' y')) :
    scalarMixedBlockOfComponents epsilonA epsilonB x' y' =
        scalarMixedBlockOfComponents epsilonA epsilonB x y ∨
      scalarMixedBlockOfComponents epsilonA epsilonB x' y' =
        flipRelativeSign
          (scalarMixedBlockOfComponents epsilonA epsilonB x y) := by
  have hepsilonA_ne : epsilonA ≠ 0 := by
    intro hepsilonA_zero
    rw [hepsilonA_zero, zero_pow (by norm_num : 2 ≠ 0)] at hepsilonA
    norm_num at hepsilonA
  have hepsilonB_ne : epsilonB ≠ 0 := by
    intro hepsilonB_zero
    rw [hepsilonB_zero, zero_pow (by norm_num : 2 ≠ 0)] at hepsilonB
    norm_num at hepsilonB
  have hdiag := (solvesComplementaryBlock_iff a b qSq hab
    (scalarMixedBlockOfComponents epsilonA epsilonB x y)).mp hsolves
  have hdiag' := (solvesComplementaryBlock_iff a b qSq hab
    (scalarMixedBlockOfComponents epsilonA epsilonB x' y')).mp hsolves'
  have haa : scalarMixedDiagonal epsilonA x =
      scalarMixedDiagonal epsilonA x' := by
    simpa [scalarMixedBlockOfComponents] using hdiag.1.trans hdiag'.1.symm
  have hbb : scalarMixedDiagonal epsilonB y =
      scalarMixedDiagonal epsilonB y' := by
    simpa [scalarMixedBlockOfComponents] using hdiag.2.trans hdiag'.2.symm
  simp [scalarMixedDiagonal] at haa hbb
  exact scalarMixedBlock_eq_or_flip_of_sq_eq_sq epsilonA epsilonB x y x' y'
    (haa.resolve_right hepsilonA_ne) (hbb.resolve_right hepsilonB_ne)

/-- On the genuinely two-component branch, the two relative-sign choices are
distinct mixed tensors.
@isnad1 id=ne.3h4v.s6.29b244547133 from=translated src=- shape=7342786f vocab=3c27441a
-/
theorem scalarMixedBlock_relative_sign_nonunique
    (epsilonA epsilonB x y : ℝ)
    (hepsilonA : epsilonA ^ 2 = 1)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    scalarMixedBlockOfComponents epsilonA epsilonB x y ≠
      scalarMixedBlockOfComponents epsilonA epsilonB x (-y) := by
  intro hblock
  have hepsilonA_ne : epsilonA ≠ 0 := by
    intro hepsilonA_zero
    rw [hepsilonA_zero, zero_pow (by norm_num : 2 ≠ 0)] at hepsilonA
    norm_num at hepsilonA
  have hab := congrArg MixedBlock.ab hblock
  simp [scalarMixedBlockOfComponents, scalarMixedOffDiagonal] at hab
  have hab_zero : epsilonA * x * y = 0 := by linarith
  exact (mul_ne_zero (mul_ne_zero hepsilonA_ne hx) hy) hab_zero

/-- **Pointwise uniqueness obstruction.** Every genuinely two-component
scalar-generated solution produces a second, distinct solution with identical
forced diagonal/Ricci data by reversing one component.
@isnad1 id=and.4h7v.s6.5e3bd46a5b9a from=translated src=- shape=a1e27f4b vocab=e9328779
-/
theorem exists_distinct_relative_sign_solution
    (a b qSq epsilonA epsilonB x y : ℝ)
    (hepsilonA : epsilonA ^ 2 = 1)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hsolves : SolvesComplementaryBlock a b qSq
      (scalarMixedBlockOfComponents epsilonA epsilonB x y)) :
    SolvesComplementaryBlock a b qSq
        (scalarMixedBlockOfComponents epsilonA epsilonB x (-y)) ∧
      scalarMixedBlockOfComponents epsilonA epsilonB x y ≠
        scalarMixedBlockOfComponents epsilonA epsilonB x (-y) := by
  constructor
  · rw [scalarMixedBlock_neg_second]
    exact (solvesComplementaryBlock_flip_iff a b qSq
      (scalarMixedBlockOfComponents epsilonA epsilonB x y)).mpr hsolves
  · exact scalarMixedBlock_relative_sign_nonunique epsilonA epsilonB x y
      hepsilonA hx hy

/-- Matrix realization of a mixed block in the ordered complementary
eigenbasis.-/
def mixedBlockMatrix (block : MixedBlock) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![block.aa, block.ab; block.ba, block.bb]

/-- Reflection of the second complementary eigendirection.-/
def secondSpectralReflection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Ricci restriction to the ordered complementary eigenspace.-/
def complementaryRicciMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; 0, b]

/-- The spectral reflection is an involution.
@isnad1 id=eq.0h0v.s7.081344642cd7 from=translated src=- shape=af6c9ceb vocab=e9cb77bd
-/
theorem secondSpectralReflection_sq :
    secondSpectralReflection * secondSpectralReflection = 1 := by
  rw [show secondSpectralReflection = !![(1 : ℝ), 0; 0, -1] from rfl]
  rw [Matrix.mul_fin_two]
  rw [Matrix.one_fin_two]
  norm_num

/-- The reflection belongs to the centralizer of the Ricci block.
@isnad1 id=eq.0h2v.s7.8100fa983742 from=translated src=- shape=f955734c vocab=73ad7971
-/
theorem secondSpectralReflection_commutes_with_Ricci (a b : ℝ) :
    secondSpectralReflection * complementaryRicciMatrix a b =
      complementaryRicciMatrix a b * secondSpectralReflection := by
  rw [show secondSpectralReflection = !![(1 : ℝ), 0; 0, -1] from rfl]
  rw [show complementaryRicciMatrix a b = !![a, 0; 0, b] from rfl]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-- Conjugation by the reflection leaves the Ricci data unchanged.
@isnad1 id=eq.0h2v.s7.18270a7c28aa from=translated src=- shape=e49e8e95 vocab=73ad7971
-/
theorem secondSpectralReflection_preserves_Ricci (a b : ℝ) :
    secondSpectralReflection * complementaryRicciMatrix a b *
        secondSpectralReflection = complementaryRicciMatrix a b := by
  rw [secondSpectralReflection_commutes_with_Ricci]
  rw [mul_assoc, secondSpectralReflection_sq, mul_one]

/-- **Basis-independent orbit interpretation.** Conjugating by the reflection
of the second eigendirection realizes exactly the relative-sign flip.
@isnad1 id=eq.0h1v.s7.d9962bdf7dd6 from=translated src=- shape=b4737db4 vocab=04830a34
-/
theorem secondSpectralReflection_conjugates (block : MixedBlock) :
    secondSpectralReflection * mixedBlockMatrix block *
        secondSpectralReflection =
      mixedBlockMatrix (flipRelativeSign block) := by
  rw [show secondSpectralReflection = !![(1 : ℝ), 0; 0, -1] from rfl]
  rw [show mixedBlockMatrix block =
    !![block.aa, block.ab; block.ba, block.bb] from rfl]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mixedBlockMatrix, flipRelativeSign]

end RainichKaluza
