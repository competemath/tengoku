import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_DeformationRingData
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions
import Tengoku.Seed.LinearAlgebra.Matrix.Adjugate
import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.RingTheory.Length
import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.RingTheory.Ideal.Quotient.Basic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.RingTheory.Valuation.ValuationRing
import Tengoku.Seed.LinearAlgebra.Matrix.ToLinearEquiv
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.GroupTheory.Abelianization.Defs
import Tengoku.Seed.Algebra.Group.TypeTags.Basic
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.Tactic.Group
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.lean`: wrote out 14 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 11 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt

set_option autoImplicit false

open GaloisRep Module

namespace COTGlue

noncomputable def twAd {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Module.End A ρ.V →ₗ[A] Module.End A ρ.V :=
  (ρ.det σ : A) • {
    toFun := fun f => ρ.ρ σ * f * ρ.ρ σ⁻¹
    map_add' := fun f g => by simp only [mul_add, add_mul]
    map_smul' := fun c f => by
      simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, RingHom.id_apply] }

noncomputable abbrev adZero {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) :
    Submodule A (Module.End A ρ.V) :=
  LinearMap.ker (LinearMap.trace A ρ.V)

noncomputable def adZeroInertiaInv {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ)) : Submodule A (Module.End A ρ.V) :=
  adZero ρ ⊓ ⨅ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.ker (twAd ρ τ - LinearMap.id)

noncomputable def localCotangentTermDenom {A : Type} [CommRing A] [IsLocalRing A]
    (ρ : GaloisRepAdic A) (P : ValuationSubring (AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Submodule A (adZeroInertiaInv ρ P) :=
  Submodule.comap (adZeroInertiaInv ρ P).subtype
    ((adZeroInertiaInv ρ P).map (twAd ρ σ - LinearMap.id))

variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (b : Basis (Fin 2) A ρ.V)

noncomputable abbrev endToMatrix : Module.End A ρ.V ≃ₐ[A] Matrix (Fin 2) (Fin 2) A :=
  LinearMap.toMatrixAlgEquiv b

/--
@isnad1 id=eq.0h4v.s10.606105591b91 from=translated src=- shape=8b5b0b1a vocab=9b218db5
-/
theorem trace_endToMatrix (f : Module.End A ρ.V) :
    LinearMap.trace A ρ.V f = Matrix.trace (endToMatrix ρ b f) :=
  LinearMap.trace_eq_matrix_trace A b f

noncomputable def adZeroEquivSl2 :
    adZero ρ ≃ₗ[A] LinearMap.ker (Matrix.traceLinearMap (Fin 2) A A) :=
  LinearEquiv.ofBijective
    ((endToMatrix ρ b).toLinearEquiv.toLinearMap.restrict
      (p := adZero ρ) (q := LinearMap.ker (Matrix.traceLinearMap (Fin 2) A A))
      (fun f hf => by
        show Matrix.trace (endToMatrix ρ b f) = 0
        rw [← trace_endToMatrix ρ b]; exact hf))
    ⟨fun f g h => Subtype.ext ((endToMatrix ρ b).toLinearEquiv.injective (Subtype.ext_iff.mp h)),
     fun ⟨M, hM⟩ => ⟨⟨(endToMatrix ρ b).symm M, by
        simp only [adZero, LinearMap.mem_ker, trace_endToMatrix ρ b,
          AlgEquiv.apply_symm_apply]; exact hM⟩,
       Subtype.ext (by
        simp only [LinearMap.restrict_apply]
        exact (endToMatrix ρ b).apply_symm_apply M)⟩⟩

/--
@isnad1 id=eq.0h4v.s11.7d65ce5a0c7b from=translated src=- shape=873303b3 vocab=e2e94d23
-/
theorem coe_det_eq_matrix_det (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.det σ : A) = Matrix.det (endToMatrix ρ b (ρ.ρ σ)) := by
  have h1 : (ρ.det σ : A) = LinearMap.det (ρ.ρ σ) := rfl
  rw [h1, ← LinearMap.det_toMatrix b]
  rfl

/--
@isnad1 id=eq.0h5v.s12.59534b6923de from=translated src=- shape=7e7f21c2 vocab=c9415132
-/
theorem endToMatrix_twAd (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : Module.End A ρ.V) :
    endToMatrix ρ b (twAd ρ σ f) =
      endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b f * Matrix.adjugate (endToMatrix ρ b (ρ.ρ σ)) := by
  have hFG : endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b (ρ.ρ σ⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hadj : (endToMatrix ρ b (ρ.ρ σ)).adjugate
      = (endToMatrix ρ b (ρ.ρ σ)).det • endToMatrix ρ b (ρ.ρ σ⁻¹) := by
    have key : (endToMatrix ρ b (ρ.ρ σ)).adjugate *
        (endToMatrix ρ b (ρ.ρ σ) * endToMatrix ρ b (ρ.ρ σ⁻¹))
        = (endToMatrix ρ b (ρ.ρ σ)).det • endToMatrix ρ b (ρ.ρ σ⁻¹) := by
      rw [← mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, one_mul]
    rwa [hFG, mul_one] at key
  have hdet : (ρ.det σ : A) = (endToMatrix ρ b (ρ.ρ σ)).det := coe_det_eq_matrix_det ρ b σ
  simp only [twAd, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_smul, map_mul,
    hadj, hdet, Matrix.mul_smul]

end COTGlue

namespace WCOTGlueBCore
variable {R : Type} [CommRing R]
def conjAdj (F : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun X := F * X * F.adjugate
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
/--
@isnad1 id=eq.0h3v.s9.8021340544f4 from=translated src=- shape=56bb4ce8 vocab=6d17a53a
-/
@[scoped simp] theorem conjAdj_apply (F X : Matrix (Fin 2) (Fin 2) R) : conjAdj F X = F * X * F.adjugate := rfl
def trLin : Matrix (Fin 2) (Fin 2) R →ₗ[R] R where
  toFun X := X 0 0 + X 1 1
  map_add' X Y := by simp only [Matrix.add_apply]; ring
  map_smul' c X := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
def invM (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) : Submodule R (Matrix (Fin 2) (Fin 2) R) :=
  LinearMap.ker (trLin (R := R)) ⊓ ⨅ T ∈ 𝒯, LinearMap.ker (conjAdj T - LinearMap.id)
def denM (𝒯 : Set (Matrix (Fin 2) (Fin 2) R)) (F : Matrix (Fin 2) (Fin 2) R) : Submodule R (invM 𝒯) :=
  Submodule.comap (invM 𝒯).subtype ((invM 𝒯).map (conjAdj F - LinearMap.id))
end WCOTGlueBCore
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace COTGlue
open WCOTGlueBCore
variable {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (b : Basis (Fin 2) A ρ.V)

/--
@isnad1 id=iff.0h5v.s11.092d8312a7b0 from=translated src=- shape=b7e82f66 vocab=e3caf52f
-/
theorem mem_adZeroInertiaInv_iff_endToMatrix_mem_invM (P : ValuationSubring (AlgebraicClosure ℚ))
    (f : Module.End A ρ.V) :
    f ∈ adZeroInertiaInv ρ P ↔
      endToMatrix ρ b f ∈ invM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) := by
  unfold adZeroInertiaInv invM
  rw [Submodule.mem_inf, Submodule.mem_inf]
  apply and_congr
  ·
    rw [LinearMap.mem_ker, LinearMap.mem_ker, trace_endToMatrix ρ b, Matrix.trace_fin_two]
    rfl
  ·
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero, conjAdj_apply, Set.forall_mem_image]
    refine forall_congr' fun τ => forall_congr' fun _ => ?_
    rw [← endToMatrix_twAd ρ b]
    exact ⟨fun h => congrArg _ h, fun h => (endToMatrix ρ b).injective h⟩

/--
@isnad1 id=eq.0h4v.s11.57a5112e4609 from=translated src=- shape=ae3c7bc7 vocab=e0fa27bf
-/
theorem map_adZeroInertiaInv_eq_invM (P : ValuationSubring (AlgebraicClosure ℚ)) :
    Submodule.map (endToMatrix ρ b).toLinearMap (adZeroInertiaInv ρ P) =
      invM ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) := by
  ext M
  simp only [Submodule.mem_map, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P f).mp hf
  · intro hM
    exact ⟨(endToMatrix ρ b).symm M,
      (mem_adZeroInertiaInv_iff_endToMatrix_mem_invM ρ b P _).mpr
        (by rwa [AlgEquiv.apply_symm_apply]),
      (endToMatrix ρ b).apply_symm_apply M⟩

noncomputable def adZeroInertiaInvEquivInvM (P : ValuationSubring (AlgebraicClosure ℚ)) :
    (adZeroInertiaInv ρ P : Submodule A _) ≃ₗ[A]
      (invM (R := A) ((fun τ => endToMatrix ρ b (ρ.ρ τ)) '' (P.inertiaSubgroupIn ℚ)) :
        Submodule A _) :=
  ((endToMatrix ρ b).toLinearEquiv.submoduleMap (adZeroInertiaInv ρ P)).trans
    (LinearEquiv.ofEq _ _ (map_adZeroInertiaInv_eq_invM ρ b P))

end COTGlue
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTGlueBCore

variable {R : Type} [CommRing R]

private def _root_.WCOTGlueBCore.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

export _root_.WCOTGlueBCore (sl2M)

end WCOTGlueBCore
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTGlueBCore

open Polynomial

variable {R : Type} [CommRing R]

/--
@isnad1 id=eq.1h2v.s9.681c5fd929eb from=translated src=- shape=7c3bbf30 vocab=2b6ce213
-/
theorem sub_one_mul_sub_one_eq_zero_of_charpoly (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.charpoly = (X - 1) ^ 2) : (M - 1) * (M - 1) = 0 := by
  have h0 := M.aeval_self_charpoly
  rw [h, map_pow, map_sub, aeval_X, map_one] at h0
  simpa [sq] using h0

/--
@isnad1 id=eq.1h2v.s7.3e2dcbf73270 from=translated src=- shape=6c131984 vocab=049a6bfb
-/
theorem trace_eq_two_of_charpoly (M : Matrix (Fin 2) (Fin 2) R)
    (h : M.charpoly = (X - 1) ^ 2) : M.trace = 2 := by
  have ht := Matrix.trace_eq_neg_charpoly_coeff M
  rw [h] at ht
  have hc : ((X - 1 : Polynomial R) ^ 2).coeff 1 = -2 := by
    rw [sub_sq, mul_one, one_pow]
    simp [coeff_X_pow, coeff_one]
  simp only [Fintype.card_fin] at ht
  rw [hc] at ht
  rw [ht]
  ring

end WCOTGlueBCore
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTDevB6

variable {R : Type} [CommRing R] [NoZeroDivisors R]

private def _root_.WCOTDevB6.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

export _root_.WCOTDevB6 (sl2M)

/--
@isnad1 id=eq.1h2v.s7.7a35c47ceb5b from=translated src=- shape=738135f1 vocab=0f578b42
-/
theorem trace_eq_zero_of_mul_self_eq_zero (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0) : N.trace = 0 := by
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.trace_fin_two]
  by_contra h
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by rw [← h01]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by rw [← h10]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hb]; ring
    exact (mul_self_eq_zero.mp this)
  have hd : N 1 1 = 0 := by
    have : N 1 1 * N 1 1 = 0 := by rw [← h11, hc]; ring
    exact (mul_self_eq_zero.mp this)
  exact h (by rw [ha, hd, add_zero])

theorem eq_line_of_unipotent_mul (t : R) (ht : t ≠ 0) (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0)
    (hu : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2) : N = sl2M 0 (N 0 1) 0 := by
  have htrN : N 0 0 + N 1 1 = 0 := by rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero N hN
  have htr : ((1 + sl2M 0 t 0) * (1 + N)).trace = 2 + (N 0 0 + N 1 1) + t * N 1 0 := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sl2M, Matrix.one_apply]
    ring
  have hc : N 1 0 = 0 := by
    have : t * N 1 0 = 0 := by
      have h2 := hu; rw [htr, htrN, add_zero] at h2
      simpa using h2
    exact (mul_eq_zero.mp this).resolve_left ht
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hc]; ring
    exact mul_self_eq_zero.mp this
  have hd : N 1 1 = 0 := by rw [ha, zero_add] at htrN; exact htrN
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2M, ha, hc, hd]

end WCOTDevB6
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTGlueBAdapt

variable {R : Type} [CommRing R]

private def _root_.WCOTGlueBAdapt.sl2M (s t u : R) : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![s, t], ![u, -s]]

export _root_.WCOTGlueBAdapt (sl2M)

/--
@isnad1 id=eq.1h2v.s7.7a35c47ceb5b from=translated src=- shape=738135f1 vocab=0f578b42
-/
theorem trace_eq_zero_of_mul_self_eq_zero [NoZeroDivisors R] (N : Matrix (Fin 2) (Fin 2) R) (hN : N * N = 0) :
    N.trace = 0 := by
  have h00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : N 0 0 * N 0 1 + N 0 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : N 1 0 * N 0 0 + N 1 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hN 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : N 1 0 * N 0 1 + N 1 1 * N 1 1 = 0 := by
    have := congrFun (congrFun hN 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [Matrix.trace_fin_two]
  by_contra h
  have hb : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by rw [← h01]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have hc : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by rw [← h10]; ring
    exact (mul_eq_zero.mp this).resolve_right h
  have ha : N 0 0 = 0 := by
    have : N 0 0 * N 0 0 = 0 := by rw [← h00, hb]; ring
    exact (mul_self_eq_zero.mp this)
  have hd : N 1 1 = 0 := by
    have : N 1 1 * N 1 1 = 0 := by rw [← h11, hc]; ring
    exact (mul_self_eq_zero.mp this)
  exact h (by rw [ha, hd, add_zero])

/--
@isnad1 id=ex.2h2v.s9.77d735045b06 from=translated src=- shape=393b7707 vocab=fd1aa925
-/
theorem exists_conj_eq_sl2M [IsDomain R] [ValuationRing R] (M : Matrix (Fin 2) (Fin 2) R)
    (hM : M * M = 0) (hM0 : M ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) R, IsUnit P.det ∧ ∃ t : R, t ≠ 0 ∧ M * P = P * sl2M 0 t 0 := by

  have htr : M 0 0 + M 1 1 = 0 := by
    rw [← Matrix.trace_fin_two]; exact trace_eq_zero_of_mul_self_eq_zero M hM
  have hd : M 1 1 = -M 0 0 := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact htr
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 0 := by
    have := congrFun (congrFun hM 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hMe : M = Matrix.of ![![M 0 0, M 0 1], ![M 1 0, -M 0 0]] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hd]

  rcases ValuationRing.dvd_total (M 0 1) (M 0 0) with ⟨l, hl⟩ | ⟨m, hm⟩
  ·
    by_cases hb : M 0 1 = 0
    ·
      have ha : M 0 0 = 0 := by rw [hl, hb, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ·
      have hc : M 1 0 = -(l * l * M 0 1) := by
        have : M 0 1 * (M 1 0 + l * l * M 0 1) = 0 := by rw [← h00, hl]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left hb
        exact eq_neg_of_add_eq_zero_left h2
      refine ⟨Matrix.of ![![1, 0], ![-l, 1]], ?_, M 0 1, hb, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hl, hc] <;> ring
  ·
    by_cases ha : M 0 0 = 0
    ·
      have hb : M 0 1 = 0 := by rw [hm, ha, zero_mul]
      have hc : M 1 0 ≠ 0 := by
        intro hc; apply hM0; rw [hMe]; ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
      refine ⟨Matrix.of ![![0, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
    ·
      have hac : M 0 0 = -(m * M 1 0) := by
        have : M 0 0 * (M 0 0 + m * M 1 0) = 0 := by rw [← h00, hm]; ring
        have h2 := (mul_eq_zero.mp this).resolve_left ha
        exact eq_neg_of_add_eq_zero_left h2
      have hc : M 1 0 ≠ 0 := by intro hc; apply ha; rw [hac, hc, mul_zero, neg_zero]
      refine ⟨Matrix.of ![![-m, 1], ![1, 0]], ?_, M 1 0, hc, ?_⟩
      · simp [Matrix.det_fin_two]
      · rw [hMe]; ext i j
        fin_cases i <;> fin_cases j <;>
          simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two, hm, hac]
        all_goals ring

end WCOTGlueBAdapt
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTGlueBT1

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V] {n : Type} [Fintype n] [DecidableEq n]

/--
@isnad1 id=eq.1h6v.s9.155a10b39ac2 from=translated src=- shape=ab86a2d5 vocab=c4c25712
-/
theorem toMatrixAlgEquiv_basis_map (b₀ : Basis n A V) (P : Matrix n n A) (hP : IsUnit P.det)
    (f : Module.End A V) :
    LinearMap.toMatrixAlgEquiv (b₀.map (Matrix.toLinearEquiv b₀ P hP)) f =
      P⁻¹ * LinearMap.toMatrixAlgEquiv b₀ f * P := by
  have hg : ((Matrix.toLinearEquiv b₀ P hP : V ≃ₗ[A] V) : V →ₗ[A] V) = Matrix.toLin b₀ b₀ P :=
    LinearMap.ext fun _ => rfl
  have hgs : ((Matrix.toLinearEquiv b₀ P hP).symm : V →ₗ[A] V) = Matrix.toLin b₀ b₀ P⁻¹ :=
    LinearMap.ext fun _ => rfl
  change LinearMap.toMatrix _ _ f = P⁻¹ * LinearMap.toMatrix b₀ b₀ f * P
  rw [LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  change LinearMap.toMatrix b₀ b₀
      (((Matrix.toLinearEquiv b₀ P hP).symm : V →ₗ[A] V) * f * ((Matrix.toLinearEquiv b₀ P hP : V ≃ₗ[A] V) : V →ₗ[A] V))
    = _
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hg, hgs, LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]

/--
@isnad1 id=eq.2h7v.s9.9cb56ea31283 from=translated src=- shape=85a98075 vocab=53e756e9
-/
theorem toMatrixAlgEquiv_basis_map_eq (b₀ : Basis n A V) (P : Matrix n n A) (hP : IsUnit P.det)
    (f : Module.End A V) (T : Matrix n n A) (h : LinearMap.toMatrixAlgEquiv b₀ f * P = P * T) :
    LinearMap.toMatrixAlgEquiv (b₀.map (Matrix.toLinearEquiv b₀ P hP)) f = T := by
  rw [toMatrixAlgEquiv_basis_map, Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP,
    Matrix.one_mul]

end WCOTGlueBT1
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTGlueBFinal

open WCOTGlueBCore

variable {R : Type} [CommRing R]

/--
@isnad1 id=eq.0h4v.s5.1affed805b15 from=translated src=- shape=7a0b7423 vocab=7df2c901
-/
theorem sl2M_B6_eq (s t u : R) : WCOTDevB6.sl2M s t u = sl2M s t u := rfl

/--
@isnad1 id=eq.0h4v.s5.fbf13f706734 from=translated src=- shape=7a0b7423 vocab=f368d5d1
-/
theorem sl2M_adapt_eq (s t u : R) : WCOTGlueBAdapt.sl2M s t u = sl2M s t u := rfl

end WCOTGlueBFinal
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace COTGlue

open WCOTGlueBCore Polynomial

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

end COTGlue
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace WCOTTame3

variable {R : Type} [CommRing R]

theorem eq_zero_of_forall_pow_dvd [IsNoetherianRing R] [IsLocalRing R] (p : R)
    (hp : p ∈ IsLocalRing.maximalIdeal R) (d : R) (h : ∀ k : ℕ, p ^ k ∣ d) : d = 0 := by
  have hmem : d ∈ ⨅ k : ℕ, (IsLocalRing.maximalIdeal R) ^ k := by
    refine Ideal.mem_iInf.mpr fun k => ?_
    obtain ⟨e, rfl⟩ := h k
    exact Ideal.mul_mem_right e _ (Ideal.pow_mem_pow hp k)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hmem

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]

/--
@isnad1 id=eq.7h12v.s10.c868c1669e8f from=translated src=- shape=1de34ff9 vocab=93bd5ad4
-/
theorem conj_eq_pow_of_tameQ (N : Matrix n n R) (hN : N * N = 0) (hNreg : ∀ a : R, a • N = 0 → a = 0)
    (p : R) (hsep : ∀ d : R, (∀ k : ℕ, p ^ k ∣ d) → d = 0)
    (f : G →* Matrix n n R) (hline : ∀ g, ∃ a : R, f g = 1 + a • N)
    (F F' : Matrix n n R) (κ : G → G) (hκ : ∀ τ, f (κ τ) = F * f τ * F') (q : ℕ) (pn : ℕ → ℕ)
    (hpn : ∀ k, (pn k : R) = p ^ k)
    (htameQ : ∀ k : ℕ, ∀ τ : G, ∃ c ∈ commutator G, ∃ w : G, κ τ = τ ^ q * c * w ^ (pn k)) :
    ∀ τ, F * f τ * F' = (f τ) ^ q := by

  choose a ha using hline
  have hmulN : ∀ x y : R, (1 + x • N) * (1 + y • N) = 1 + (x + y) • N := by
    intro x y
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm, hN, smul_zero, add_zero, add_smul]
    abel
  have hadd : ∀ g h, a (g * h) = a g + a h := by
    intro g h
    have h1 : f (g * h) = 1 + (a g + a h) • N := by rw [map_mul, ha g, ha h, hmulN]
    rw [ha (g * h)] at h1
    have h2 : (a (g * h) - (a g + a h)) • N = 0 := by rw [sub_smul, sub_eq_zero]; exact add_left_cancel h1
    exact sub_eq_zero.mp (hNreg _ h2)
  have hone : a 1 = 0 := by
    have h1 := hadd 1 1
    rw [mul_one] at h1
    exact add_left_cancel (h1.symm.trans (add_zero _).symm)
  let φ : G →* Multiplicative R :=
    { toFun := fun g => Multiplicative.ofAdd (a g)
      map_one' := by simp [hone]
      map_mul' := fun g h => by simp [hadd, ofAdd_add] }
  have hcomm : ∀ c ∈ commutator G, a c = 0 := by
    intro c hc
    have := Abelianization.commutator_subset_ker φ hc
    rw [MonoidHom.mem_ker] at this
    exact ofAdd_eq_one.mp this
  have hpow : ∀ (w : G) (m : ℕ), a (w ^ m) = (m : R) * a w := by
    intro w m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ, hadd, ih]; push_cast; ring
  have hfpow : ∀ (g : G) (m : ℕ), (f g) ^ m = 1 + ((m : R) * a g) • N := by
    intro g m; rw [← map_pow, ha, hpow]

  intro τ
  set d : R := a (κ τ) - (q : R) * a τ with hd
  have hdvd : ∀ k : ℕ, p ^ k ∣ d := by
    intro k
    obtain ⟨c, hc, w, hw⟩ := htameQ k τ
    have : a (κ τ) = (q : R) * a τ + 0 + (pn k : R) * a w := by
      rw [hw, hadd, hadd, hpow, hcomm c hc, hpow]
    refine ⟨a w, ?_⟩
    rw [hd, this, hpn]; ring
  have hd0 : d = 0 := hsep d hdvd
  have hκa : a (κ τ) = (q : R) * a τ := by rw [← sub_eq_zero]; exact hd0
  rw [← hκ, ha (κ τ), hκa, hfpow]

end WCOTTame3
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

namespace COTGlue

open WCOTGlueBCore Polynomial

/--
@isnad1 id=eq.0h4v.s7.8272cd50c2f0 from=translated src=- shape=b59f24c1 vocab=6cb35879
-/
theorem conj_pow_aux {G : Type} [Group G] (a w : G) (n : ℕ) : (a⁻¹ * w * a) ^ n = a⁻¹ * w ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

/--
@isnad1 id=eq.0h2v.s7.76b4f9ffc87b from=translated src=- shape=f793ca5a vocab=a69ba8a7
-/
theorem sl2M_smul_eq {R : Type} [CommRing R] (b : R) : sl2M (0 : R) b 0 = b • sl2M 0 1 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M]

/--
@isnad1 id=eq.5h7v.s13.87e8da544ff6 from=translated src=- shape=7a318c11 vocab=cdc791f0
-/
theorem frob_tame_rel {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (X - 1) ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : ℕ) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ * ρ.ρ σ⁻¹ = ρ.ρ τ ^ q := by
  classical
  set I := P.inertiaSubgroupIn ℚ with hI

  have hconjI : ∀ τ ∈ I, σ * τ * σ⁻¹ ∈ I := by
    intro τ hτ
    obtain ⟨w, hwI, hw⟩ := hdivI 0 τ hτ
    rw [pow_zero, pow_one] at hw
    have : σ * τ * σ⁻¹ = w * τ ^ q := by rw [hw]; group
    rw [this]
    exact I.mul_mem hwI (I.pow_mem hτ q)
  by_cases hram : ∃ τ₀ ∈ I, ρ.ρ τ₀ ≠ 1
  swap
  ·
    simp only [not_exists, not_and, ne_eq, not_not] at hram
    rw [hram τ hτ, one_pow, mul_one, ← map_mul, mul_inv_cancel, map_one]
  obtain ⟨τ₀, hτ₀P, hτ₀ne⟩ := hram

  have hchar : ∀ (b : Basis (Fin 2) 𝒪 ρ.V), ∀ τ ∈ I, (endToMatrix ρ b (ρ.ρ τ)).charpoly = (X - 1) ^ 2 := by
    intro b τ hτ
    rw [show endToMatrix ρ b (ρ.ρ τ) = LinearMap.toMatrix b b (ρ.ρ τ) from rfl, LinearMap.charpoly_toMatrix]
    exact hunip P hP τ hτ
  let b₀ : Basis (Fin 2) 𝒪 ρ.V := Module.finBasisOfFinrankEq 𝒪 ρ.V ρ.finrank_eq
  have hN₀sq : (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) * (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) = 0 :=
    sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b₀ τ₀ hτ₀P)
  have hN₀ne : endToMatrix ρ b₀ (ρ.ρ τ₀) - 1 ≠ 0 := by
    intro h
    apply hτ₀ne
    apply (endToMatrix ρ b₀).injective
    rw [map_one]
    exact sub_eq_zero.mp h
  obtain ⟨Pm, hPm, t, ht, hconj⟩ := WCOTGlueBAdapt.exists_conj_eq_sl2M _ hN₀sq hN₀ne
  rw [WCOTGlueBFinal.sl2M_adapt_eq] at hconj
  let b : Basis (Fin 2) 𝒪 ρ.V := b₀.map (Matrix.toLinearEquiv b₀ Pm hPm)
  have hT₀b : endToMatrix ρ b (ρ.ρ τ₀) = 1 + sl2M 0 t 0 := by
    apply WCOTGlueBT1.toMatrixAlgEquiv_basis_map_eq b₀ Pm hPm
    change endToMatrix ρ b₀ (ρ.ρ τ₀) * Pm = Pm * (1 + sl2M 0 t 0)
    have h1 : endToMatrix ρ b₀ (ρ.ρ τ₀) = 1 + (endToMatrix ρ b₀ (ρ.ρ τ₀) - 1) := by
      rw [add_comm, sub_add_cancel]
    rw [h1, add_mul, one_mul, hconj, Matrix.mul_add, Matrix.mul_one]

  have hline' : ∀ τ ∈ I, ∃ a : 𝒪, endToMatrix ρ b (ρ.ρ τ) = 1 + a • sl2M 0 1 0 := by
    intro τ hτ
    set T := endToMatrix ρ b (ρ.ρ τ) with hT
    have hT1 : 1 + (T - 1) = T := by rw [add_comm, sub_add_cancel]
    have hN : (T - 1) * (T - 1) = 0 := sub_one_mul_sub_one_eq_zero_of_charpoly _ (hchar b τ hτ)
    have hu : ((1 + WCOTDevB6.sl2M 0 t 0) * (1 + (T - 1))).trace = 2 := by
      rw [hT1, WCOTGlueBFinal.sl2M_B6_eq, hT, ← hT₀b, ← map_mul, ← map_mul]
      exact trace_eq_two_of_charpoly _ (hchar b (τ₀ * τ) (I.mul_mem hτ₀P hτ))
    have key := WCOTDevB6.eq_line_of_unipotent_mul t ht (T - 1) hN hu
    refine ⟨(T - 1) 0 1, ?_⟩
    rw [← sl2M_smul_eq, ← WCOTGlueBFinal.sl2M_B6_eq, ← key, hT1]

  let f : I →* Matrix (Fin 2) (Fin 2) 𝒪 :=
    ((endToMatrix ρ b).toRingEquiv.toMonoidHom.comp ρ.ρ).comp I.subtype
  have hf : ∀ g : I, f g = endToMatrix ρ b (ρ.ρ g) := fun _ => rfl
  have hline : ∀ g : I, ∃ a : 𝒪, f g = 1 + a • sl2M 0 1 0 := fun g => by rw [hf]; exact hline' g g.2
  have hE2 : sl2M (0 : 𝒪) 1 0 * sl2M 0 1 0 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sl2M, Matrix.mul_apply, Fin.sum_univ_two]
  have hEreg : ∀ a : 𝒪, a • sl2M (0 : 𝒪) 1 0 = 0 → a = 0 := by
    intro a h
    have := congrFun (congrFun h 0) 1
    simpa [sl2M] using this
  have hsep : ∀ d : 𝒪, (∀ k : ℕ, (p : 𝒪) ^ k ∣ d) → d = 0 := WCOTTame3.eq_zero_of_forall_pow_dvd (p : 𝒪) hp𝔪
  let κ : I → I := fun g => ⟨σ * g * σ⁻¹, hconjI g g.2⟩
  have hκ : ∀ g : I, f (κ g) = endToMatrix ρ b (ρ.ρ σ) * f g * endToMatrix ρ b (ρ.ρ σ⁻¹) := by
    intro g
    rw [hf, hf]
    change endToMatrix ρ b (ρ.ρ (σ * g * σ⁻¹)) = _
    rw [map_mul, map_mul, map_mul, map_mul]
  have htameQ : ∀ (k : ℕ) (g : I), ∃ c ∈ commutator I, ∃ w : I, κ g = g ^ q * c * w ^ (p ^ k) := by
    intro k g
    obtain ⟨w, hwI, hw⟩ := hdivI k g g.2
    refine ⟨1, Subgroup.one_mem _,
      ⟨((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ^ q)⁻¹ * w * (g : _) ^ q,
        I.mul_mem (I.mul_mem (I.inv_mem (I.pow_mem g.2 q)) hwI) (I.pow_mem g.2 q)⟩, ?_⟩
    apply Subtype.ext
    simp only [κ, Subgroup.coe_mul, OneMemClass.coe_one, SubmonoidClass.coe_pow]
    rw [conj_pow_aux, hw]
    group

  have key := WCOTTame3.conj_eq_pow_of_tameQ (sl2M (0 : 𝒪) 1 0) hE2 hEreg (p : 𝒪) hsep f hline
    (endToMatrix ρ b (ρ.ρ σ)) (endToMatrix ρ b (ρ.ρ σ⁻¹)) κ hκ q (fun k => p ^ k) (fun k => by push_cast; rfl)
    htameQ ⟨τ, hτ⟩
  rw [hf] at key
  apply (endToMatrix ρ b).injective
  rw [map_mul, map_mul, map_pow]
  exact key

end COTGlue
open scoped _root_.P2MW.S_GaloisRepAdic_conj_mul_conj_eq_pow_of_isUnipotentOnInertiaAt.WCOTGlueBCore

/--
@isnad1 id=eq.5h7v.s13.87e8da544ff6 from=translated src=- shape=7a318c11 vocab=cdc791f0
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (ρ : GaloisRepAdic 𝒪) (q : ℕ)
    (hunip : ∀ P' : ValuationSubring (AlgebraicClosure ℚ), P'.LiesOverPrime q →
      ∀ τ ∈ P'.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ τ) = (Polynomial.X - 1) ^ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (p : ℕ) (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), τ ∈ P.inertiaSubgroupIn ℚ →
      ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, w ∈ P.inertiaSubgroupIn ℚ ∧
        w ^ (p ^ n) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    ρ.ρ σ * ρ.ρ τ * ρ.ρ σ⁻¹ = ρ.ρ τ ^ q := by
  exact COTGlue.frob_tame_rel ρ q hunip P hP σ p hp𝔪 hdivI τ hτ
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
