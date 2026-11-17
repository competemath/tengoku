import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ArtinL_EulerFactor
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Residual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArtinL_LSeriesSummable_coeff_of_one_lt_re.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArtinL_LSeriesSummable_coeff_of_one_lt_re

set_option autoImplicit false

namespace P2mArtinAbs

open Polynomial Finset

def bnd : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | e + 1, k => ∑ j ∈ Finset.range (k + 1), bnd e j

/--
@isnad1 id=eq.0h1v.s5.76c8914a23ab from=translated src=- shape=51addf3c vocab=467ed943
-/
@[scoped simp] theorem bnd_zero (k : ℕ) : bnd 0 k = if k = 0 then 1 else 0 := by rw [bnd]

/--
@isnad1 id=eq.0h2v.s5.d4dff475e7fb from=translated src=- shape=4379f55c vocab=e981d6fa
-/
theorem bnd_succ (e k : ℕ) : bnd (e + 1) k = ∑ j ∈ Finset.range (k + 1), bnd e j := by rw [bnd]

/--
@isnad1 id=eq.0h1v.s4.f5696e0a6970 from=translated src=- shape=1d838610 vocab=2d338553
-/
theorem bnd_zero_right (e : ℕ) : bnd e 0 = 1 := by
  induction e with
  | zero => simp
  | succ e ih => rw [bnd_succ, Finset.sum_range_one, ih]

/--
@isnad1 id=le.0h2v.s4.74e7567d1513 from=translated src=- shape=f4893ecc vocab=1611fba5
-/
theorem bnd_le_succ (e k : ℕ) : bnd e k ≤ bnd (e + 1) k := by
  rw [bnd_succ]
  exact Finset.single_le_sum (f := fun j => bnd e j) (fun _ _ => Nat.zero_le _)
    (Finset.self_mem_range_succ k)

/--
@isnad1 id=le.1h3v.s4.648524b1da71 from=translated src=- shape=79c5e0af vocab=2413ce29
-/
theorem bnd_mono {d e : ℕ} (h : d ≤ e) (k : ℕ) : bnd d k ≤ bnd e k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (bnd_le_succ _ k)

/--
@isnad1 id=le.0h2v.s5.a9789aecdab1 from=translated src=- shape=372e930b vocab=a43d6adc
-/
theorem ite_le_bnd (e k : ℕ) : (if k = 0 then 1 else 0) ≤ bnd e k := by
  split_ifs with hk
  · subst hk; rw [bnd_zero_right]
  · exact Nat.zero_le _

section PS

open PowerSeries

def geom (α : ℂ) : PowerSeries ℂ := PowerSeries.mk fun j => α ^ j

/--
@isnad1 id=eq.0h1v.s6.e38a14505870 from=translated src=- shape=500c0af6 vocab=6ee4882a
-/
theorem one_sub_mul_geom (α : ℂ) : (1 - PowerSeries.C α * PowerSeries.X) * geom α = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
  cases k with
  | zero => simp [geom]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, geom, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp [pow_succ, mul_comm]

/--
@isnad1 id=le.1h2v.s7.6d0107e77bd1 from=translated src=- shape=b0f0535e vocab=ee27785c
-/
theorem norm_coeff_prod_geom_le (S : Multiset ℂ) (hS : ∀ α ∈ S, ‖α‖ ≤ 1) (k : ℕ) :
    ‖PowerSeries.coeff k (S.map geom).prod‖ ≤ bnd (Multiset.card S) k := by
  induction S using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, PowerSeries.coeff_one, Multiset.card_zero,
      bnd_zero]
    split_ifs <;> simp
  | cons α S ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, bnd_succ, PowerSeries.coeff_mul]
    have hα : ‖α‖ ≤ 1 := hS α (Multiset.mem_cons_self α S)
    have hS' : ∀ β ∈ S, ‖β‖ ≤ 1 := fun β hβ => hS β (Multiset.mem_cons_of_mem hβ)
    calc ‖∑ p ∈ antidiagonal k, PowerSeries.coeff p.1 (geom α) * PowerSeries.coeff p.2 (S.map geom).prod‖
        ≤ ∑ p ∈ antidiagonal k, ‖PowerSeries.coeff p.1 (geom α) *
            PowerSeries.coeff p.2 (S.map geom).prod‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ antidiagonal k, (bnd (Multiset.card S) p.2 : ℝ) := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul, geom, PowerSeries.coeff_mk, norm_pow]
          calc ‖α‖ ^ p.1 * ‖PowerSeries.coeff p.2 (S.map geom).prod‖
              ≤ 1 * (bnd (Multiset.card S) p.2 : ℝ) := by
                gcongr
                · exact pow_le_one₀ (norm_nonneg α) hα
                · exact ih hS' p.2
            _ = _ := one_mul _
      _ = ((∑ j ∈ Finset.range (k + 1), bnd (Multiset.card S) j : ℕ) : ℝ) := by
          push_cast
          rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun _ j => (bnd (Multiset.card S) j : ℝ)),
            ← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun j hj => ?_
          have : j < k + 1 := Finset.mem_range.mp hj
          congr 2; omega

/--
@isnad1 id=eq.0h1v.s7.8ed9ed4d69b1 from=translated src=- shape=9f277159 vocab=8c7f932c
-/
theorem prod_geom_eq_inv (S : Multiset ℂ) :
    (S.map geom).prod = ((S.map fun α => 1 - PowerSeries.C α * PowerSeries.X).prod)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [← Multiset.prod_map_mul]
    have : ∀ α ∈ S, geom α * (1 - PowerSeries.C α * PowerSeries.X) = 1 := fun α _ => by
      rw [mul_comm, one_sub_mul_geom]
    rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.prod_replicate, one_pow]
  · rw [map_multiset_prod, Multiset.map_map]
    have : ∀ α ∈ S, (PowerSeries.constantCoeff ∘ fun α => 1 - PowerSeries.C α * PowerSeries.X) α
        = 1 := fun α _ => by simp
    rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.prod_replicate, one_pow]
    exact one_ne_zero

end PS

section Poly

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=eq.0h1v.s7.35d4a2cb7eec from=translated src=- shape=fbe1b938 vocab=60e0c3a7
-/
theorem reverse_X_sub_C (α : ℂ) : (X - C α : ℂ[X]).reverse = 1 - C α * X := by
  rw [Polynomial.reverse, natDegree_X_sub_C, reflect_sub, reflect_one_X, reflect_C, pow_one]

/--
@isnad1 id=eq.0h1v.s5.4fefc31eb559 from=translated src=- shape=ae8d35f8 vocab=4a228745
-/
theorem reverse_multiset_prod (S : Multiset ℂ[X]) : S.prod.reverse = (S.map Polynomial.reverse).prod := by
  induction S using Multiset.induction_on with
  | empty => simpa using reverse_C (1 : ℂ)
  | cons p S ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      reverse_mul_of_domain, ih]

/--
@isnad1 id=eq.0h2v.s7.d0d7753c06d4 from=translated src=- shape=8c5531d7 vocab=f9e69abc
-/
theorem charpolyRev_eq_prod_roots (M : Matrix ι ι ℂ) :
    M.charpolyRev = (M.charpoly.roots.map fun α => 1 - C α * X).prod := by
  rw [← Matrix.reverse_charpoly]
  conv_lhs => rw [(IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic M.charpoly_monic]
  rw [reverse_multiset_prod, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  exact reverse_X_sub_C α

/--
@isnad1 id=eq.0h2v.s7.bc56d9be3d00 from=translated src=- shape=14f4a8fd vocab=819f02c9
-/
theorem coe_charpolyRev_eq_prod_roots (M : Matrix ι ι ℂ) :
    (M.charpolyRev : PowerSeries ℂ) =
      (M.charpoly.roots.map fun α => 1 - PowerSeries.C α * PowerSeries.X).prod := by
  rw [charpolyRev_eq_prod_roots, ← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod,
    Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
  simp [Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X]

/--
@isnad1 id=eq.3h4v.s6.7bf7e8426b5e from=translated src=- shape=599361aa vocab=2374f620
-/
theorem norm_eq_one_of_mem_roots_charpoly (M : Matrix ι ι ℂ) {N : ℕ} (hN : N ≠ 0) (hM : M ^ N = 1)
    {α : ℂ} (hα : α ∈ M.charpoly.roots) : ‖α‖ = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : M.charpoly = 1 := by
      rw [Matrix.charpoly, Matrix.det_isEmpty]
    rw [this, roots_one] at hα
    exact absurd hα (Multiset.notMem_zero α)
  · have hroot : M.charpoly.IsRoot α := (mem_roots M.charpoly_monic.ne_zero).mp hα
    have hspec : α ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have hpow : α ^ N ∈ spectrum ℂ (M ^ N) :=
      spectrum.pow_image_subset M N ⟨α, hspec, rfl⟩
    rw [hM, spectrum.one_eq, Set.mem_singleton_iff] at hpow
    exact Complex.norm_eq_one_of_pow_eq_one hpow hN

/--
@isnad1 id=le.2h4v.s7.03ef3c6d5467 from=translated src=- shape=a4f7ffdb vocab=0389829e
-/
theorem norm_coeff_inv_charpolyRev_le (M : Matrix ι ι ℂ) {N : ℕ} (hN : N ≠ 0) (hM : M ^ N = 1)
    (k : ℕ) :
    ‖PowerSeries.coeff k ((M.charpolyRev : PowerSeries ℂ)⁻¹)‖ ≤ bnd (Fintype.card ι) k := by
  rw [coe_charpolyRev_eq_prod_roots, ← prod_geom_eq_inv]
  have hcard : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← M.charpoly_natDegree_eq_dim]
    exact (splits_iff_card_roots.mp (IsAlgClosed.splits M.charpoly))
  rw [← hcard]
  refine norm_coeff_prod_geom_le _ (fun α hα => ?_) k
  exact (norm_eq_one_of_mem_roots_charpoly M hN hM hα).le

end Poly

section Tau

open ArithmeticFunction

def tau (e : ℕ) : ArithmeticFunction ℕ := (ArithmeticFunction.zeta) ^ e

/--
@isnad1 id=ismultip.0h1v.s2.13a8b2650367 from=translated src=- shape=6da4ece3 vocab=fbf2e722
-/
theorem tau_isMultiplicative (e : ℕ) : (tau e).IsMultiplicative := by
  induction e with
  | zero => rw [tau, pow_zero]; exact isMultiplicative_one
  | succ e ih => rw [tau, pow_succ]; exact ih.mul isMultiplicative_zeta

/--
@isnad1 id=eq.1h3v.s5.f325be4aed9b from=translated src=- shape=c3b20d6f vocab=53018193
-/
theorem tau_prime_pow (e : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) : tau e (p ^ k) = bnd e k := by
  induction e generalizing k with
  | zero =>
    rw [tau, pow_zero, one_apply, bnd_zero]
    have : p ^ k = 1 ↔ k = 0 := by
      rw [Nat.pow_eq_one]; exact ⟨fun h => h.resolve_left hp.one_lt.ne', Or.inr⟩
    exact if_congr this rfl rfl
  | succ e ih =>
    rw [tau, pow_succ', ← tau, zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map,
      bnd_succ]
    exact Finset.sum_congr rfl fun j _ => ih j

/--
@isnad1 id=lseriess.1h2v.s5.df8bff657073 from=translated src=- shape=d43aad1c vocab=22c804be
-/
theorem tau_LSeriesSummable (e : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => ((tau e m : ℕ) : ℂ)) s := by
  have key : ∀ e : ℕ, LSeriesSummable (⇑(tau e : ArithmeticFunction ℂ)) s := by
    intro e
    induction e with
    | zero =>
      rw [tau, pow_zero, natCoe_one]
      refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun m _ => ?_) hs
      rw [one_apply]
      split_ifs <;> simp
    | succ e ih =>
      rw [tau, pow_succ', ← tau, natCoe_mul, ← ArithmeticFunction.coe_mul]
      refine LSeriesSummable.convolution ?_ ih
      exact LSeriesSummable_zeta_iff.mpr hs
  have h := key e
  refine (LSeriesSummable_congr s (fun {m} _ => ?_)).mpr h
  rw [natCoe_apply]

/--
@isnad1 id=eq.1h2v.s5.1e113e9e7976 from=translated src=- shape=ac01680b vocab=b56ce433
-/
theorem tau_apply_eq_prod (e : ℕ) {m : ℕ} (hm : m ≠ 0) :
    tau e m = m.factorization.prod fun _ k => bnd e k := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization (tau e)
    (tau_isMultiplicative e) hm]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.support_factorization] at hp
  exact tau_prime_pow e (Nat.prime_of_mem_primeFactors hp) _

end Tau

section Level

open scoped MatrixGroups

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/--
@isnad1 id=isalgebr.0h0v.s4.92f995461263 from=translated src=- shape=3905abf2 vocab=c7f7e443
-/
local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
/--
@isnad1 id=isalgclo.0h0v.s4.728a7497b292 from=translated src=- shape=3905abf2 vocab=50bd979f
-/
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
/--
@isnad1 id=isgalois.0h0v.s4.b04052bb8761 from=translated src=- shape=3905abf2 vocab=49029860
-/
local instance isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

/--
@isnad1 id=finite.1h2v.s9.c9d5cebc4894 from=translated src=- shape=4a05c9ef vocab=2aea2d73
-/
theorem finite_range (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    Finite ρ.range := by
  obtain ⟨L, hL, hker⟩ := hρ
  haveI := hL
  have hopen : IsOpen (ρ.ker : Set Γℚ) := by
    refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup) ?_
      (IntermediateField.fixingSubgroup_isOpen L)
    intro σ hσ
    rw [MonoidHom.mem_ker]
    exact hker σ (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx)
  have : Finite (Γℚ ⧸ ρ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv

/--
@isnad1 id=ex.1h3v.s10.839c39d72a49 from=translated src=- shape=a5e733d0 vocab=bd216e41
-/
theorem exists_pow_eq_one (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (σ : Γℚ) : ∃ N : ℕ, N ≠ 0 ∧ ρ σ ^ N = 1 := by
  haveI := finite_range ρ hρ
  have hfin : IsOfFinOrder (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range) := isOfFinOrder_of_finite _
  rw [← orderOf_pos_iff] at hfin
  refine ⟨orderOf (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range), hfin.ne', ?_⟩
  have h := pow_orderOf_eq_one (⟨ρ σ, ⟨σ, rfl⟩⟩ : ρ.range)
  exact congrArg Subtype.val h

end Level

section Local

open scoped MatrixGroups

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/--
@isnad1 id=le.0h2v.s6.02657e83f657 from=translated src=- shape=e4e65060 vocab=aef92b81
-/
theorem norm_coeff_one_le (e k : ℕ) :
    ‖PowerSeries.coeff k (((1 : ℂ[X]) : PowerSeries ℂ)⁻¹)‖ ≤ bnd e k := by
  rw [Polynomial.coe_one, inv_one, PowerSeries.coeff_one]
  refine le_trans ?_ (Nat.cast_le.mpr (ite_le_bnd e k))
  split_ifs <;> simp

/--
@isnad1 id=le.1h5v.s9.90849756d0cf from=translated src=- shape=800397d5 vocab=94c0822b
-/
theorem norm_coeff_inv_eulerFactorAt_le (ρ : Γℚ →* GL (Fin n) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Γℚ)
    (k : ℕ) :
    ‖PowerSeries.coeff k ((ArtinL.eulerFactorAt ρ A σ : PowerSeries ℂ)⁻¹)‖ ≤ bnd n k := by
  unfold ArtinL.eulerFactorAt
  split_ifs with h
  · obtain ⟨N, hN, hσN⟩ := exists_pow_eq_one ρ hρ σ
    set W := ArtinL.inertiaInvariants ρ A with hW
    set f := Deformation.matrixRepresentation ρ σ with hf
    have hfN : f ^ N = 1 := by
      rw [hf, ← map_pow, Deformation.matrixRepresentation_apply, map_pow, hσN, Units.val_one,
        Matrix.mulVecLin_one]
      rfl
    set T : W →ₗ[ℂ] W := f.restrict h with hT
    have hTN : T ^ N = 1 := by
      rw [hT, Module.End.pow_restrict N]
      refine LinearMap.ext fun x => Subtype.ext ?_
      rw [LinearMap.restrict_apply]
      change (f ^ N) (x : Fin n → ℂ) = x
      rw [hfN, Module.End.one_apply]
    unfold ArtinL.charpolyRev
    set b := Module.finBasis ℂ W
    have hMN : (LinearMap.toMatrix b b T) ^ N = 1 := by
      rw [LinearMap.toMatrix_pow, hTN, LinearMap.toMatrix_one]
    refine (norm_coeff_inv_charpolyRev_le _ hN hMN k).trans ?_
    rw [Fintype.card_fin]
    exact_mod_cast bnd_mono ((Submodule.finrank_le W).trans_eq (Module.finrank_fin_fun ℂ)) k
  · exact norm_coeff_one_le n k

/--
@isnad1 id=le.1h4v.s8.60f92519e354 from=translated src=- shape=6ad1ddf6 vocab=05c0c10a
-/
theorem norm_coeffPrimePow_le (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ)
    (p k : ℕ) : ‖ArtinL.coeffPrimePow ρ p k‖ ≤ bnd n k := by
  unfold ArtinL.coeffPrimePow ArtinL.eulerFactor
  split_ifs with h
  · exact norm_coeff_inv_eulerFactorAt_le ρ hρ _ _ k
  · exact norm_coeff_one_le n k

/--
@isnad1 id=le.1h3v.s8.c15b0bc94de8 from=translated src=- shape=4443c89b vocab=0a0ace92
-/
theorem norm_coeff_le (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ) (m : ℕ) :
    ‖ArtinL.coeff ρ m‖ ≤ (tau n m : ℝ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ArtinL.coeff, ite_eq_right hm, tau_apply_eq_prod n hm, Finsupp.prod, Finsupp.prod, norm_prod,
      Nat.cast_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ?_
    exact norm_coeffPrimePow_le ρ hρ p _

/--
@isnad1 id=lseriess.2h3v.s8.7b57a296bf90 from=translated src=- shape=d5637f12 vocab=69a5c117
-/
theorem main (ρ : Γℚ →* GL (Fin n) ℂ) (hρ : GaloisFactorsThroughFiniteLevel ρ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (ArtinL.coeff ρ) s := by
  have hτ := tau_LSeriesSummable n hs
  refine Summable.of_norm_bounded hτ.norm fun m => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hm
  · exact le_rfl
  · rw [Complex.norm_natCast]
    gcongr
    exact norm_coeff_le ρ hρ m

end Local

end P2mArtinAbs
open scoped _root_.P2MW.S_ArtinL_LSeriesSummable_coeff_of_one_lt_re.P2mArtinAbs

open scoped MatrixGroups in
/--
@isnad1 id=lseriess.2h3v.s8.7b57a296bf90 from=translated src=- shape=d5637f12 vocab=69a5c117
-/
theorem solution {n : ℕ}
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin n) ℂ)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (ArtinL.coeff ρ) s :=
  P2mArtinAbs.main ρ hρ hs
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
