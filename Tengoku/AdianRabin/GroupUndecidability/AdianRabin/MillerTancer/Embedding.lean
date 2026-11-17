import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.MillerTancer.LeftNormalForm
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.MillerTancer.Amalgam
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.MillerTancer.RightNormalForm
import Tengoku.AdianRabin.GroupUndecidability.AdianRabin.MillerTancer.LeftInjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Comparison between the two equivalent models of the left factor used in the
Miller--Tancer amalgam argument.

`Amalgam.LeftFactor P` is the paper-like bracketing

  `P.Group * FreeGroup {alpha, beta}`,

whereas `LeftNormalForm.MillerLeft P.Group` brackets the same three free
factors as

  `(P.Group * <beta>) * <alpha>`.

For the injectivity argument we only need the canonical homomorphism from the
first model to the second and its action on the five distinguished elements.
-/

namespace Undecidability.MillerTancer.LeftBridge

open Monoid

/-- The old presented group included into the base of the nested model.-/
def oldToMiller (P : FP n m) : P.Group →* LeftNormalForm.MillerLeft P.Group :=
  (CoprodI.of (M := LeftNormalForm.OuterFactor P.Group)
      (i := LeftNormalForm.OuterIndex.base)).comp
    (CoprodI.of (M := LeftNormalForm.LeftFactor P.Group)
      (i := LeftNormalForm.LeftIndex.old))

/-- Send the two new generators of the paper-like left factor to the
corresponding `alpha` and `beta` in the nested normal-form model.-/
def newToMiller (P : FP n m) :
    FreeGroup (Fin 2) →* LeftNormalForm.MillerLeft P.Group :=
  FreeGroup.lift
    ![LeftNormalForm.outerAlpha,
      LeftNormalForm.baseOf LeftNormalForm.beta]

/-- Reassociate the left factor, with the generator convention required by
the five basis elements.-/
def comparison (P : FP n m) :
    Amalgam.LeftFactor P →*
      LeftNormalForm.MillerLeft P.Group :=
  Monoid.Coprod.lift (oldToMiller P) (newToMiller P)

/--
@isnad1 id=eq.0h4v.s9.1d578085a18b from=translated src=- shape=d2113f0a vocab=e65dc96c
-/
@[simp] theorem comparison_old (P : FP n m) (g : P.Group) :
    comparison P (Amalgam.oldLeft P g) =
      LeftNormalForm.baseOf (LeftNormalForm.old g) := rfl

/--
@isnad1 id=eq.0h3v.s8.ce89dfee7d13 from=translated src=- shape=50daf2b4 vocab=b3c3707a
-/
@[simp] theorem comparison_alpha (P : FP n m) :
    comparison P (Amalgam.alphaLeft P) =
      LeftNormalForm.outerAlpha := by
  simp [comparison, Amalgam.alphaLeft, newToMiller]

/--
@isnad1 id=eq.0h3v.s8.56e77b002aef from=translated src=- shape=e034fceb vocab=0f2dde4c
-/
@[simp] theorem comparison_beta (P : FP n m) :
    comparison P (Amalgam.betaLeft P) =
      LeftNormalForm.baseOf LeftNormalForm.beta := by
  simp [comparison, Amalgam.betaLeft, newToMiller]

/--
@isnad1 id=eq.0h5v.s8.a86dcbad31f1 from=translated src=- shape=5d8ebe5e vocab=d58044a2
-/
@[simp] theorem baseOf_mul (P : FP n m)
    (x y : LeftNormalForm.LeftProduct P.Group) :
    LeftNormalForm.baseOf (x * y) =
      LeftNormalForm.baseOf x * LeftNormalForm.baseOf y :=
  map_mul
    (CoprodI.of
      (M := LeftNormalForm.OuterFactor P.Group)
      (i := LeftNormalForm.OuterIndex.base) :
      LeftNormalForm.LeftProduct P.Group →*
        LeftNormalForm.MillerLeft P.Group) x y

/-- The comparison sends the paper's five left-hand amalgamating elements to
the exact five elements used by the nested normal-form proof.
@isnad1 id=eq.0h6v.s8.f125b43c193f from=translated src=- shape=abd96f5e vocab=a8abf7ef
-/
theorem comparison_leftBasis (P : FP n m) (z w : Word n) (i : Fin 5) :
    comparison P (Amalgam.leftBasis P z w i) =
      LeftNormalForm.outerLeftBasis (P.evalWord w) (P.evalWord z) i := by
  fin_cases i <;>
    simp [Amalgam.leftBasis, LeftNormalForm.outerLeftBasis,
      map_mul, map_inv, map_pow, mul_assoc]

/--
@isnad1 id=eq.0h5v.s10.9d4a5f253cfa from=translated src=- shape=7ba5d09d vocab=e0446eea
-/
theorem comparison_comp_leftMap (P : FP n m) (z w : Word n) :
    (comparison P).comp (Amalgam.leftMap P z w) =
      FreeGroup.lift
        (LeftNormalForm.outerLeftBasis (P.evalWord w) (P.evalWord z)) := by
  ext i
  simp [Amalgam.leftMap, comparison_leftBasis]

/-- Injectivity in the nested normal-form model implies injectivity of the
paper-like left map.  The nontriviality hypothesis is recorded because it is
the hypothesis from which the normal-form proof obtains `hinj`; it is not
needed again by this purely functorial bridge.
@isnad1 id=injectiv.2h5v.s10.c66660acee4c from=translated src=- shape=5510b2ee vocab=e1c588aa
-/
theorem leftMap_injective_of_outerLeftBasis_injective
    (P : FP n m) (z w : Word n)
    (_hw : P.evalWord w ≠ 1)
    (hinj : Function.Injective
      (FreeGroup.lift
        (LeftNormalForm.outerLeftBasis
          (P.evalWord w) (P.evalWord z)))) :
    Function.Injective (Amalgam.leftMap P z w) := by
  intro x y hxy
  apply hinj
  rw [← comparison_comp_leftMap P z w]
  exact congrArg (comparison P) hxy

end Undecidability.MillerTancer.LeftBridge

/-!
The nontrivial half of the Miller--Tancer construction, specialized
to one extra relation `z` that normally generates the old group.

The two lists of five words freely generate subgroups of the left and right
factors.  Identifying those subgroups forms a free product with amalgamation.
The old group embeds in that pushout, so a nontrivial `w` remains nontrivial
after the four new relations are imposed.
-/

namespace Undecidability.MillerTancer

open Amalgam

/-- The independently proved right normal-form map is exactly the right map
used by the amalgamated-product construction.
@isnad1 id=eq.0h0v.s6.dd0544e11f25 from=translated src=- shape=66ad9eef vocab=91043ede
-/
theorem pushout_rightMap_eq : Amalgam.rightMap = rightBasisMap := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;>
    simp [Amalgam.rightMap, Amalgam.rightBasis,
      rightBasisMap, rightBasis, Amalgam.betaRight,
      Amalgam.gammaRight, rightBeta, rightGamma]

/--
@isnad1 id=injectiv.0h0v.s7.e5bcb5e02c62 from=translated src=- shape=d2491ecb vocab=a14668a8
-/
theorem pushout_rightMap_injective :
    Function.Injective Amalgam.rightMap := by
  rw [pushout_rightMap_eq]
  exact RightNormalForm.original_rightBasisMap_injective

/-- Reduce the nontriviality implication to injectivity of the left list of
five amalgamating words.
@isnad1 id=not.2h5v.s8.38f85561f51e from=translated src=- shape=49c3931f vocab=4e8087ff
-/
theorem transform_not_trivial_of_leftMap_injective
    (P : FP n m) (z w : Word n)
    (hleft : Function.Injective (Amalgam.leftMap P z w))
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P z w).presentsTrivial :=
  Amalgam.transform_not_trivial_of_basis_injective
    P z w hleft pushout_rightMap_injective hw

/-- If `w` is nontrivial in the old presentation, its transformed presentation
is nontrivial.  This is the amalgamated-free-product argument in the proof of
Tancer's Theorem 9, for the Miller commutator variant used in the paper.
@isnad1 id=not.1h5v.s5.c09bb6736d4c from=translated src=- shape=74fbed1d vocab=c301f2de
-/
theorem transform_not_trivial_of_not_wordProblem
    (P : FP n m) (z w : Word n)
    (hw : ¬ P.wordProblem w) :
    ¬ (transform P z w).presentsTrivial := by
  have hwEval : P.evalWord w ≠ 1 := by
    intro h
    exact hw ((P.wordProblem_iff_evalWord_eq_one w).mpr h)
  have houter :=
    LeftInjective.outerLeftBasis_lift_injective
      (P.evalWord w) (P.evalWord z) hwEval
  have hleft :=
    LeftBridge.leftMap_injective_of_outerLeftBasis_injective
      P z w hwEval houter
  exact transform_not_trivial_of_leftMap_injective P z w hleft hw

end Undecidability.MillerTancer
