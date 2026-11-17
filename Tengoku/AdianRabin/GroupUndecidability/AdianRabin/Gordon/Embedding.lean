import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.Amalgam
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.LeftNormalForm
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.Gordon.RightNormalForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The free-product embeddings needed for Gordon's nontriviality direction. -/

namespace Undecidability.Gordon

namespace LeftBridge

open Monoid

def oldToSplit (P : FP n m) :
    P.Group →* LeftNormalForm.SplitLeft P.Group :=
  CoprodI.of (M := MillerTancer.LeftNormalForm.LeftFactor P.Group)
    (i := MillerTancer.LeftNormalForm.LeftIndex.old)

def newToSplit (P : FP n m) :
    FreeGroup (Fin 2) →* LeftNormalForm.SplitLeft P.Group :=
  FreeGroup.lift ![LeftNormalForm.a, LeftNormalForm.auxiliaryAlpha]

def comparison (P : FP n m) :
    Amalgam.LeftFactor P →* LeftNormalForm.SplitLeft P.Group :=
  Monoid.Coprod.lift (oldToSplit P) (newToSplit P)

/--
@isnad1 id=eq.0h4v.s9.c138ab7d4548 from=translated src=- shape=37105528 vocab=b34b58e7
-/
@[simp] theorem comparison_old (P : FP n m) (g : P.Group) :
    comparison P (Amalgam.oldLeft P g) = MillerTancer.LeftNormalForm.old g := rfl

/--
@isnad1 id=eq.0h3v.s8.1bd439395908 from=translated src=- shape=50daf2b4 vocab=9c23f3fb
-/
@[simp] theorem comparison_a (P : FP n m) :
    comparison P (Amalgam.aLeft P) = LeftNormalForm.a := by
  simp [comparison, Amalgam.aLeft, newToSplit]

/--
@isnad1 id=eq.0h3v.s8.817d3a50f568 from=translated src=- shape=50daf2b4 vocab=792f2b5d
-/
@[simp] theorem comparison_alpha (P : FP n m) :
    comparison P (Amalgam.alphaLeft P) =
      LeftNormalForm.auxiliaryAlpha := by
  simp [comparison, Amalgam.alphaLeft, newToSplit]

/--
@isnad1 id=eq.0h6v.s8.188ec9425c7f from=translated src=- shape=43d98fbd vocab=0810e5f9
-/
theorem comparison_leftBasis (P : FP n m) (data : TorsionData P)
    (w : Word n) (i : BasisIndex n) :
    comparison P (Amalgam.leftBasis P data w i) =
      LeftNormalForm.splitBasis data.degree
        (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w) i := by
  cases i <;>
    simp [Amalgam.leftBasis, LeftNormalForm.splitBasis,
      LeftNormalForm.oldElement, LeftNormalForm.degreeInt,
      LeftNormalForm.a, LeftNormalForm.auxiliaryAlpha,
      map_mul, map_inv, map_pow, zpow_neg, zpow_natCast, mul_assoc]

/--
@isnad1 id=eq.0h5v.s10.d97d8009c2a9 from=translated src=- shape=13efa0ec vocab=c1d78b40
-/
theorem comparison_comp_leftMap (P : FP n m) (data : TorsionData P)
    (w : Word n) :
    (comparison P).comp (Amalgam.leftMap P data w) =
      FreeGroup.lift
        (LeftNormalForm.splitBasis data.degree
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w)) := by
  ext i
  simp [Amalgam.leftMap, comparison_leftBasis]

/--
@isnad1 id=injectiv.1h5v.s8.05c8577f8f13 from=translated src=- shape=2440669a vocab=76eee3f6
-/
theorem leftMap_injective (P : FP n m) (data : TorsionData P)
    (w : Word n) (hw : P.evalWord w ≠ 1) :
    Function.Injective (Amalgam.leftMap P data w) := by
  have hinj : Function.Injective
      (FreeGroup.lift
        (LeftNormalForm.splitBasis data.degree
          (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w))) :=
    LeftNormalForm.splitBasis_lift_injective data.degree
      data.degree_pos data.degree_injective
      (fun j ↦ (PresentedGroup.of j : P.Group)) (P.evalWord w) hw
  intro x y hxy
  apply hinj
  rw [← comparison_comp_leftMap P data w]
  exact congrArg (comparison P) hxy

end LeftBridge

/--
@isnad1 id=eq.0h1v.s5.4a4bb04608ec from=translated src=- shape=55074be3 vocab=f931db38
-/
theorem amalgam_rightMap_eq (n : ℕ) :
    Amalgam.rightMap n = rightBasisMap n := by
  apply FreeGroup.ext_hom
  intro i
  cases i <;>
    simp [Amalgam.rightMap, Amalgam.rightBasis,
      Amalgam.rightConjugate, Amalgam.bRight, Amalgam.betaRight,
      rightBasisMap, rightBasis, rightU, rightB, rightBeta]

/--
@isnad1 id=injectiv.0h1v.s6.868d5dec60cf from=translated src=- shape=52afbc2d vocab=73b35a71
-/
theorem amalgam_rightMap_injective (n : ℕ) :
    Function.Injective (Amalgam.rightMap n) := by
  rw [amalgam_rightMap_eq n]
  exact rightBasisMap_injective n

/-- The hard implication in Gordon's Lemma 2.1: a nontrivial input word
remains visible in the amalgamated-product witness.
@isnad1 id=not.1h5v.s5.858f72ca7396 from=translated src=- shape=738dba56 vocab=b9c13531
-/
theorem transform_not_trivial_of_not_wordProblem
    (P : FP n m) (data : TorsionData P) (w : Word n)
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P data w).presentsTrivial := by
  have hwEval : P.evalWord w ≠ 1 := by
    intro h
    exact hw ((P.wordProblem_iff_evalWord_eq_one w).mpr h)
  exact Amalgam.transform_not_trivial_of_basis_injective P data w
    (LeftBridge.leftMap_injective P data w hwEval)
    (amalgam_rightMap_injective n) hw

end Undecidability.Gordon
