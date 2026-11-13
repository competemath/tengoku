import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.InnerProductSpace.L2Embedding
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousLinearMap
import Tengoku.Seed.Data.List.Basic
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete prefix creation and annihilation on finite-word ℓ² space

The word-prefix creation map is an actual linear isometry, and annihilation
is its native Hilbert adjoint. Their actions on word basis vectors and their
operator composition relations are proved from the ℓ² embedding interface.
The alphabet may be arbitrary, including empty. This file does not assert
semicircular laws, freeness, or a faithful vacuum state.

Source: the concrete full-Fock construction in Nica--Speicher, Lectures on
the Combinatorics of Free Probability, Definitions 7.13 and Remark 7.14.
-/

noncomputable section
set_option autoImplicit false

open scoped Classical lp InnerProduct ENNReal

namespace NLAlib

/-- The concrete complex Hilbert space with orthonormal basis indexed by all
finite words in an alphabet. The empty word remains present for an empty alphabet.-/
abbrev WordHilbertSpace (ι : Type*) := ℓ²(List ι, ℂ)

variable {ι : Type*}

/-- The actual prefix creation isometry sends the basis vector of `w` to
the basis vector of `i :: w`.-/
def wordCreation (i : ι) : WordHilbertSpace ι →ₗᵢ[ℂ] WordHilbertSpace ι :=
  lp.embeddingLinearIsometry ⟨List.cons i, List.cons_injective⟩

/-- Actual annihilation is the native Hilbert adjoint of prefix creation.-/
def wordAnnihilation (i : ι) : WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι :=
  (wordCreation i).toContinuousLinearMap.adjoint

/-- Creation prepends one letter to the support of a word basis vector.
@isnad1 id=eq.0h4v.s11.a016f37897c9 from=translated src=- shape=1fbb805f vocab=06fa271b
-/
@[simp]
theorem wordCreation_apply_single (i : ι) (w : List ι) (z : ℂ) :
    wordCreation i (lp.single 2 w z) = lp.single 2 (i :: w) z := by
  convert! lp.embeddingLinearIsometry_apply_single
    (𝕜 := ℂ) (⟨List.cons i, List.cons_injective⟩ : List ι ↪ List ι) w z using 1
  · unfold wordCreation
    congr 1
    ext v
    by_cases hv : v = w <;> simp [lp.single_apply, hv]
  · ext v
    by_cases hv : v = i :: w <;> simp [lp.single_apply, hv]

/-- Annihilation restricts a word-coordinate function to words with the
given initial letter.
@isnad1 id=eq.0h4v.s12.505b978bea0a from=translated src=- shape=47b4465e vocab=d3e7904d
-/
@[simp]
theorem wordAnnihilation_apply (i : ι) (f : WordHilbertSpace ι) (w : List ι) :
    wordAnnihilation i f w = f (i :: w) :=
  lp.embeddingLinearIsometry_adjoint_apply _ f w

/-- Annihilation kills every basis vector supported at the empty word.
@isnad1 id=eq.0h3v.s12.3073d0defadc from=translated src=- shape=96c7ce86 vocab=0352316a
-/
@[simp]
theorem wordAnnihilation_apply_single_nil (i : ι) (z : ℂ) :
    wordAnnihilation i (lp.single 2 [] z) = 0 := by
  classical
  ext w
  simp [wordAnnihilation_apply, lp.single_apply]

open scoped Classical in
/-- On a nonempty word basis vector, annihilation removes a matching initial
letter and kills a vector with a different initial letter.
@isnad1 id=eq.0h5v.s12.97c27c6995cf from=translated src=- shape=3edd6378 vocab=c1fc2134
-/
@[simp]
theorem wordAnnihilation_apply_single_cons (i j : ι) (w : List ι) (z : ℂ) :
    wordAnnihilation i (lp.single 2 (j :: w) z) =
      if i = j then lp.single 2 w z else 0 := by
  classical
  ext v
  by_cases hij : i = j
  · subst j
    simp [wordAnnihilation_apply, lp.single_apply, Pi.single_apply]
  · simp [wordAnnihilation_apply, lp.single_apply, hij]

open scoped Classical in
/-- The native annihilation/creation composition is identity at equal
letters and zero at different letters. No law or moment assumption is used.
@isnad1 id=eq.0h3v.s14.7d20b4a3f2c6 from=translated src=- shape=9b70d7f3 vocab=f480de23
-/
theorem wordAnnihilation_comp_wordCreation (i j : ι) :
    wordAnnihilation i ∘L (wordCreation j).toContinuousLinearMap =
      if i = j then 1 else 0 := by
  classical
  apply lp.ext_continuousLinearMap (by simp : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  ext z
  by_cases hij : i = j
  · subst j
    simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap]
  · simp [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply,
      LinearIsometry.coe_toContinuousLinearMap, hij]

open scoped Classical in
/-- The concrete bounded word-prefix operators satisfy the native star-ring
relation `ell_i* ell_j = delta_ij I`.
@isnad1 id=eq.0h3v.s15.3ebd853fe99d from=translated src=- shape=a35d21fe vocab=e92230d7
-/
theorem star_wordCreation_mul_wordCreation (i j : ι) :
    star (wordCreation i).toContinuousLinearMap * (wordCreation j).toContinuousLinearMap =
      if i = j then 1 else 0 := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  exact wordAnnihilation_comp_wordCreation i j

/-- The actual unit vacuum vector is the basis vector of the empty word.-/
def wordVacuum (ι : Type*) : WordHilbertSpace ι :=
  lp.single 2 [] 1

/-- The concrete vacuum has norm one even when the alphabet is empty.
@isnad1 id=eq.0h1v.s7.6b36ee9a5995 from=translated src=- shape=06d60e9e vocab=a567885e
-/
@[simp]
theorem norm_wordVacuum : ‖wordVacuum ι‖ = 1 := by
  simp [wordVacuum, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- Every actual annihilation operator kills the vacuum.
@isnad1 id=eq.0h2v.s12.2e450202f665 from=translated src=- shape=551cf11c vocab=8db0f565
-/
@[simp]
theorem wordAnnihilation_wordVacuum (i : ι) : wordAnnihilation i (wordVacuum ι) = 0 :=
  wordAnnihilation_apply_single_nil i 1

end NLAlib
