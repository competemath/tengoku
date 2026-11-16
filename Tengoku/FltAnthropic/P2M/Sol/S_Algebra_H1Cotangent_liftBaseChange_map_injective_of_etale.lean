import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale

set_option autoImplicit false

universe u

open TensorProduct

namespace EtaleH1GC7

open Polynomial RingTheory.Sequence

/--
@isnad1 id=isweakly.1h3v.s8.1059918b1d30 from=translated src=- shape=a9b5f2c0 vocab=dda4c304
-/
theorem isWeaklyRegular_pair {B : Type*} [CommRing B] (f g : B) (hf : f ∈ nonZeroDivisors B) :
    IsWeaklyRegular B[X] [C g * X - 1, C f] := by
  classical
  refine IsWeaklyRegular.cons ?_ ((isWeaklyRegular_singleton_iff _ _).mpr ?_)
  ·
    rw [isSMulRegular_iff_right_eq_zero_of_smul]
    intro h hh
    rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at hh
    have key : ∀ n, h.coeff n = 0 := by
      intro n
      induction n with
      | zero => rw [← hh, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero]
      | succ n ih => rw [← hh, mul_assoc, coeff_C_mul, coeff_X_mul, ih, mul_zero]
    ext n
    rw [key, coeff_zero]
  ·
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [smul_eq_mul, smul_eq_mul] at hy
    haveI := IsLocalization.adjoin_inv g
    have hfA : algebraMap B (AdjoinRoot (C g * X - 1)) f ∈ nonZeroDivisors (AdjoinRoot (C g * X - 1)) :=
      IsLocalization.map_nonZeroDivisors_le (Submonoid.powers g) (AdjoinRoot (C g * X - 1)) ⟨f, hf, rfl⟩
    have h0 : AdjoinRoot.mk (C g * X - 1) (C f * x) = 0 := by
      rw [← hy, AdjoinRoot.mk_eq_zero]
      exact dvd_mul_right _ y
    rw [map_mul, AdjoinRoot.mk_C] at h0
    rw [AdjoinRoot.algebraMap_eq] at hfA
    have hx0 : AdjoinRoot.mk (C g * X - 1) x = 0 := (mem_nonZeroDivisors_iff_left.mp hfA) _ h0
    obtain ⟨z, rfl⟩ := AdjoinRoot.mk_eq_zero.mp hx0
    exact Submodule.smul_mem_pointwise_smul z (C g * X - 1) ⊤ trivial

/--
@isnad1 id=isweakly.1h3v.s10.2aaf38926378 from=translated src=- shape=c1a3bf02 vocab=4fe6c19f
-/
theorem isWeaklyRegular_pair_mv {D : Type*} [CommRing D] (f g : D[X]) (hf : f.Monic) :
    IsWeaklyRegular (MvPolynomial (Fin 2) D)
      [Bivariate.equivMvPolynomial D (C g * X - 1), Bivariate.equivMvPolynomial D (C f)] := by
  have h := isWeaklyRegular_pair f g hf.mem_nonZeroDivisors
  refine ((Bivariate.equivMvPolynomial D).toRingEquiv.toAddEquiv.isWeaklyRegular_congr ?_).mp h
  refine List.Forall₂.cons (fun x => ?_) (List.Forall₂.cons (fun x => ?_) List.Forall₂.nil)
  · change Bivariate.equivMvPolynomial D ((C g * X - 1) * x) = _ * Bivariate.equivMvPolynomial D x
    rw [map_mul]
  · change Bivariate.equivMvPolynomial D (C f * x) = _ * Bivariate.equivMvPolynomial D x
    rw [map_mul]

end EtaleH1GC7

open EtaleH1GC7 in
/--
@isnad1 id=injectiv.0h3v.s10.517c6ba44171 from=translated src=- shape=383e4394 vocab=221c3633
-/
theorem solution (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) := by
  classical

  let s : Set T := {t | Algebra.IsStandardEtale D (Localization.Away t)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    haveI := hm.isPrime
    obtain ⟨t, htm, ht⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := D) m
    exact htm (hle (Ideal.subset_span ht))
  refine Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular
    s hs ?_
  intro t ht
  haveI : Algebra.IsStandardEtale D (Localization.Away t) := ht
  obtain ⟨Pr⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
    Nonempty (StandardEtalePresentation D (Localization.Away t)))
  let Q := Pr.toPresentation
  let F : List (MvPolynomial (Fin 2) D) :=
    [Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.g * Polynomial.X - 1),
      Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.f)]
  have hF : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin 2) D) F := isWeaklyRegular_pair_mv Pr.f Pr.g Pr.monic_f
  refine ⟨Fin 2, Q.val, F, ?_, ?_, ?_⟩
  ·
    intro y
    obtain ⟨x, hx⟩ := Q.algebraMap_surjective y
    exact ⟨x, by rw [← Q.algebraMap_apply]; exact hx⟩
  ·
    rw [← Q.ker_eq_ker_aeval_val, ← Q.span_range_relation_eq_ker]
    have hrel : Q.relation = ![Polynomial.Bivariate.equivMvPolynomial D (Polynomial.C Pr.f),
        Polynomial.Bivariate.equivMvPolynomial D (Polynomial.X * Polynomial.C Pr.g - 1)] := rfl
    rw [hrel, Ideal.ofList, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, mul_comm (Polynomial.X) (Polynomial.C Pr.g)]
    congr 1
    ext p
    simp only [F, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    tauto
  ·
    intro m _ hm
    haveI : Module.Flat (MvPolynomial (Fin 2) D) (Localization.AtPrime m) :=
      IsLocalization.flat (Localization.AtPrime m) m.primeCompl
    have h2 := hF.isWeaklyRegular_lTensor (M₂ := Localization.AtPrime m)
    have h3 := ((TensorProduct.rid (MvPolynomial (Fin 2) D) (Localization.AtPrime m)).isWeaklyRegular_congr
      F).mp h2
    exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (Localization.AtPrime m)
      (Localization.AtPrime m) F).mpr h3
