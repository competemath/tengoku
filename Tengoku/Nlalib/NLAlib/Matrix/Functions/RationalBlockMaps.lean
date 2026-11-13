import Tengoku.Nlalib.NLAlib.Matrix.Functions.RationalBlockIdentities
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.PolynomialDifferential
import Tengoku.Seed.Analysis.Matrix.Normed
import Tengoku.Seed.Analysis.CStarAlgebra.Matrix
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous linear and bilinear rational differences

The finite insertion formulas bundle into continuous maps in their directions.
These maps are continuous in the base matrices on the denominator domain.
Source: matrix-toolkit derivations, F16--F19.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial ContinuousLinearMap
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n 𝕜
private local instance : ContinuousAdd (M →L[𝕜] M →L[𝕜] M) :=
  (inferInstance : IsTopologicalAddGroup (M →L[𝕜] M →L[𝕜] M)).toContinuousAdd

/--
@isnad1 id=continuo.0h2v.s12.8f99d871ff04 from=translated src=- shape=de1ec4ab vocab=285aaa58
-/
@[fun_prop] theorem continuous_flip_matrixBilinear :
    Continuous (fun L : M →L[𝕜] M →L[𝕜] M => L.flip) :=
  (flipₗᵢ 𝕜 M M M).continuous

/-- The monomial insertion sum as a continuous linear map.-/
def monomialBlockMap (A B : M) (k : ℕ) : M →L[𝕜] M :=
  ∑ j ∈ Finset.range k, mulLeftRight 𝕜 M (A ^ (k.pred - j)) (B ^ j)

/--
@isnad1 id=eq.0h6v.s9.6ee1777adf84 from=translated src=- shape=9cd929fd vocab=4bfdd7d3
-/
@[simp] theorem monomialBlockMap_apply (A B H : M) (k : ℕ) :
    monomialBlockMap A B k H = monomialBlockDifference A B H k := by
  simp [monomialBlockMap, monomialBlockDifference]

/-- The first polynomial block difference as a continuous linear map.-/
def polynomialBlockMap (p : 𝕜[X]) (A B : M) : M →L[𝕜] M :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • monomialBlockMap A B k

/--
@isnad1 id=eq.0h6v.s9.57c45115070d from=translated src=- shape=7cd54492 vocab=b8e60259
-/
@[simp] theorem polynomialBlockMap_apply (p : 𝕜[X]) (A B H : M) :
    polynomialBlockMap p A B H = polynomialBlockDifference p A B H := by
  simp [polynomialBlockMap, polynomialBlockDifference]

/-- On the diagonal, the first block map is the existing noncommutative
polynomial insertion derivative.
@isnad1 id=eq.0h4v.s8.baabfcc0a728 from=translated src=- shape=ae497357 vocab=6637a999
-/
theorem polynomialBlockMap_self (p : 𝕜[X]) (A : M) :
    polynomialBlockMap p A A = p.frechetDerivative A := by
  ext H i j
  simp only [polynomialBlockMap_apply, Polynomial.frechetDerivative_apply,
    polynomialBlockDifference, monomialBlockDifference]

/-- The ordered second polynomial block difference as a continuous bilinear map.-/
def polynomialSecondBlockMap (p : 𝕜[X]) (A B C : M) : M →L[𝕜] M →L[𝕜] M :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k •
    ∑ j ∈ Finset.range k,
      (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (C ^ j))).comp
        ((mul 𝕜 M).comp (monomialBlockMap A B (k.pred - j)))

/--
@isnad1 id=eq.0h8v.s11.4433294e0369 from=translated src=- shape=ebebf120 vocab=b24bf2e4
-/
@[simp] theorem polynomialSecondBlockMap_apply (p : 𝕜[X]) (A B C G H : M) :
    polynomialSecondBlockMap p A B C G H = polynomialSecondBlockDifference p A B C G H := by
  simp [polynomialSecondBlockMap, polynomialSecondBlockDifference]

/-- The first rational difference as a continuous linear map.-/
def rationalBlockMap (P Q : 𝕜[X]) (A B : M) : M →L[𝕜] M :=
  (mulLeftRight 𝕜 M 1 (aeval B Q)⁻¹).comp
    (polynomialBlockMap P A B -
      (mulLeftRight 𝕜 M (rationalMatrixEval P Q A) 1).comp (polynomialBlockMap Q A B))

/--
@isnad1 id=eq.0h7v.s9.87cd9e3f7e00 from=translated src=- shape=45dc69b2 vocab=7d09d1b2
-/
@[simp] theorem rationalBlockMap_apply (P Q : 𝕜[X]) (A B H : M) :
    rationalBlockMap P Q A B H = rationalBlockDifference P Q A B H := by
  simp [rationalBlockMap, rationalBlockDifference, Matrix.sub_mul]

/-- The ordered second rational difference as a continuous bilinear map.-/
def rationalSecondBlockMap (P Q : 𝕜[X]) (A B C : M) : M →L[𝕜] M →L[𝕜] M :=
  (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (aeval C Q)⁻¹)).comp
    (polynomialSecondBlockMap P A B C -
      (compL 𝕜 M M M (mulLeftRight 𝕜 M (rationalMatrixEval P Q A) 1)).comp
        (polynomialSecondBlockMap Q A B C) -
      bilinearComp (mul 𝕜 M) (rationalBlockMap P Q A B) (polynomialBlockMap Q B C))

/--
@isnad1 id=eq.0h9v.s11.5770ff45047e from=translated src=- shape=027c5db5 vocab=e2fa3e6e
-/
@[simp] theorem rationalSecondBlockMap_apply (P Q : 𝕜[X]) (A B C G H : M) :
    rationalSecondBlockMap P Q A B C G H = rationalSecondBlockDifference P Q A B C G H := by
  simp [rationalSecondBlockMap, rationalSecondBlockDifference, Matrix.sub_mul]

/--
@isnad1 id=continuo.0h3v.s9.4586a6e15dbe from=translated src=- shape=c54fb426 vocab=bee52dd2
-/
@[fun_prop] theorem continuous_monomialBlockMap (k : ℕ) :
    Continuous (fun Z : M × M => monomialBlockMap Z.1 Z.2 k) := by
  unfold monomialBlockMap
  fun_prop

/--
@isnad1 id=continuo.0h3v.s9.221ee1332ab3 from=translated src=- shape=8c71cf21 vocab=a267d582
-/
@[fun_prop] theorem continuous_polynomialBlockMap (p : 𝕜[X]) :
    Continuous (fun Z : M × M => polynomialBlockMap p Z.1 Z.2) := by
  unfold polynomialBlockMap monomialBlockMap
  fun_prop

/--
@isnad1 id=continuo.0h3v.s11.c3d9100f803c from=translated src=- shape=59cbe9a0 vocab=825ecb7e
-/
@[fun_prop] theorem continuous_polynomialSecondBlockMap (p : 𝕜[X]) :
    Continuous (fun Z : M × M × M => polynomialSecondBlockMap p Z.1 Z.2.1 Z.2.2) := by
  unfold polynomialSecondBlockMap monomialBlockMap
  refine continuous_finsetSum _ fun k _ => ?_
  have hc : Continuous (fun Z : M × M × M => ∑ j ∈ Finset.range k,
      (compL 𝕜 M M M (mulLeftRight 𝕜 M 1 (Z.2.2 ^ j))).comp
        ((mul 𝕜 M).comp (∑ i ∈ Finset.range (k.pred - j),
          mulLeftRight 𝕜 M (Z.1 ^ ((k.pred - j).pred - i)) (Z.2.1 ^ i)))) := by
    refine continuous_finsetSum _ fun j _ => ?_
    apply Continuous.clm_comp
    · fun_prop
    · fun_prop
  convert! hc.const_smul (p.coeff k) using 1

/--
@isnad1 id=continuo.1h5v.s9.3db8ac7ae389 from=translated src=- shape=f6bac56e vocab=cbd5f072
-/
theorem continuousAt_rationalMatrixEval (P Q : 𝕜[X]) (A : M)
    (hA : IsUnit (aeval A Q)) : ContinuousAt (rationalMatrixEval P Q) A := by
  unfold rationalMatrixEval
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact (P.hasFDerivAt_aeval_noncomm A).continuousAt.mul
    ((differentiableAt_inverse (𝕜 := 𝕜) (R := M) hA).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aeval_noncomm A).continuousAt)

/--
@isnad1 id=continuo.2h6v.s10.8eb03d944dd7 from=translated src=- shape=fa281f85 vocab=13f19a8d
-/
theorem continuousAt_rationalBlockMap (P Q : 𝕜[X]) (A B : M)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) :
    ContinuousAt (fun Z : M × M => rationalBlockMap P Q Z.1 Z.2) (A, B) := by
  have hfa : ContinuousAt (fun Z : M × M => rationalMatrixEval P Q Z.1) (A,B) :=
    by simpa only [Function.comp_def] using
      (continuousAt_rationalMatrixEval P Q A hA).comp
        (f := fun Z : M × M => Z.1) continuous_fst.continuousAt
  have hinvB : ContinuousAt (fun X : M => Ring.inverse (aeval X Q)) B :=
    (differentiableAt_inverse (𝕜 := 𝕜) (R := M) hB).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aeval_noncomm B).continuousAt
  have hqb : ContinuousAt (fun Z : M × M => Ring.inverse (aeval Z.2 Q)) (A,B) := by
    simpa only [Function.comp_def] using hinvB.comp
      (x := (A,B)) (f := fun Z : M × M => Z.2) continuous_snd.continuousAt
  simp only [← Matrix.nonsing_inv_eq_ringInverse] at hqb
  unfold rationalBlockMap
  fun_prop

/--
@isnad1 id=continuo.3h7v.s11.655821e4bdbb from=translated src=- shape=50c647c1 vocab=859fc12d
-/
theorem continuousAt_rationalSecondBlockMap (P Q : 𝕜[X]) (A B C : M)
    (hA : IsUnit (aeval A Q)) (hB : IsUnit (aeval B Q)) (hC : IsUnit (aeval C Q)) :
    ContinuousAt (fun Z : M × M × M => rationalSecondBlockMap P Q Z.1 Z.2.1 Z.2.2)
      (A, B, C) := by
  have hfa : ContinuousAt (fun Z : M × M × M => rationalMatrixEval P Q Z.1) (A,B,C) :=
    by simpa only [Function.comp_def] using
      (continuousAt_rationalMatrixEval P Q A hA).comp
        (f := fun Z : M × M × M => Z.1) continuous_fst.continuousAt
  have hinvC : ContinuousAt (fun X : M => Ring.inverse (aeval X Q)) C :=
    (differentiableAt_inverse (𝕜 := 𝕜) (R := M) hC).continuousAt.comp
      (f := fun X : M => aeval X Q)
      (Q.hasFDerivAt_aeval_noncomm C).continuousAt
  have hqc : ContinuousAt (fun Z : M × M × M => Ring.inverse (aeval Z.2.2 Q)) (A,B,C) := by
    simpa only [Function.comp_def] using hinvC.comp
      (x := (A,B,C)) (f := fun Z : M × M × M => Z.2.2) (continuous_snd.comp continuous_snd).continuousAt
  simp only [← Matrix.nonsing_inv_eq_ringInverse] at hqc
  have hfirst : ContinuousAt (fun Z : M × M × M => rationalBlockMap P Q Z.1 Z.2.1)
      (A,B,C) := by
    simpa only [Function.comp_def] using
      (continuousAt_rationalBlockMap P Q A B hA hB).comp
        (x := (A,B,C)) (f := fun Z : M × M × M => (Z.1,Z.2.1))
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousAt
  unfold rationalSecondBlockMap bilinearComp
  fun_prop

end NLAlib
