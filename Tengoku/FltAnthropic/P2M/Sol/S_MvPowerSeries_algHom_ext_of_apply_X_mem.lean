import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.AdicCompletion.RingHom
import Tengoku.Seed.RingTheory.AdicCompletion.Completeness
import Tengoku.Seed.RingTheory.MvPowerSeries.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_algHom_ext_of_apply_X_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_algHom_ext_of_apply_X_mem

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing

section Vars

variable {σ : Type w} {R : Type u} [CommRing R]

/--
@isnad1 id=iff.0h5v.s8.03dd5da8e05d from=translated src=- shape=834ce8f4 vocab=06f1776e
-/
theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

/--
@isnad1 id=eq.0h5v.s8.94ab7fc6dcc7 from=translated src=- shape=7afaa1ba vocab=ce3d0afd
-/
theorem coeff_dropVar (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

/--
@isnad1 id=mem.1h4v.s8.c4a0d6fd455b from=translated src=- shape=6d6c7ac7 vocab=f42a41ea
-/
theorem mem_pow_span_X_of_coeff_eq_zero [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R)
    (hφ : ∀ m : σ →₀ ℕ, m.degree < k → coeff m φ = 0) :
    φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  classical
  haveI := Fintype.ofFinite σ
  set J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) with hJ
  induction k generalizing φ with
  | zero => simp
  | succ k ihk =>

    suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), (∀ m : σ →₀ ℕ, m.degree < k + 1 → coeff m ψ = 0) →
        (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) → ψ ∈ J ^ (k + 1) by
      exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro ψ h0 hs
      have : ψ = 0 := by
        ext m
        by_cases hm : m = 0
        · subst hm; rw [map_zero]; exact h0 0 (by simp)
        · rw [map_zero]
          refine hs m fun hsub => hm ?_
          ext j
          have : j ∉ m.support := fun hj => by simpa using hsub hj
          simpa [Finsupp.mem_support_iff] using this
      rw [this]; exact Ideal.zero_mem _
    | insert i s hi ih =>
      intro ψ h0 hs
      have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
        rw [X_dvd_iff]
        intro m hm
        rw [map_sub, coeff_dropVar, ite_eq_left hm, sub_self]
      obtain ⟨q, hq⟩ := hdiv

      have hqk : ∀ m : σ →₀ ℕ, m.degree < k → coeff m q = 0 := by
        intro m hm
        have h1 : coeff (Finsupp.single i 1 + m) (X i * q) = coeff m q := by
          rw [X, coeff_add_monomial_mul, one_mul]
        have h2 : coeff (Finsupp.single i 1 + m) (ψ - dropVar i ψ) = 0 := by
          rw [map_sub, coeff_dropVar, ite_eq_right (by simp), sub_zero]
          exact h0 _ (by rw [map_add, Finsupp.degree_single]; omega)
        rw [← h1, ← hq, h2]
      have hrest : dropVar i ψ ∈ J ^ (k + 1) := by
        refine ih _ ?_ ?_
        · intro m hm
          rw [coeff_dropVar]
          split_ifs
          · exact h0 m hm
          · rfl
        · intro m hm
          rw [coeff_dropVar]
          split_ifs with hmi
          · refine hs m fun hsub => hm fun j hj => ?_
            rcases Finset.mem_insert.mp (hsub hj) with rfl | h
            · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
            · exact h
          · rfl
      have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
      rw [this, pow_succ']
      exact Ideal.add_mem _ (pow_succ' J k ▸ hrest)
        (Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ihk q hqk))

/--
@isnad1 id=mem.0h4v.s8.f30ed1f03bac from=translated src=- shape=d6d72230 vocab=a67728b4
-/
theorem sub_truncTotal_mem_pow_span_X [Finite σ] (k : ℕ) (φ : MvPowerSeries σ R) :
    φ - (truncTotal k φ : MvPolynomial σ R) ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ k := by
  refine mem_pow_span_X_of_coeff_eq_zero k _ fun m hm => ?_
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hm, sub_self]

/--
@isnad1 id=le.1h6v.s9.2a9e87164b74 from=translated src=- shape=829c5532 vocab=6af4cc46
-/
theorem map_pow_span_X_le {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
    (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (I : Ideal A) (hφ : ∀ i, φ (X i) ∈ I) (k : ℕ) :
    (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝒪)) ^ k).map φ ≤ I ^ k := by
  rw [Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ k
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact hφ i

/--
@isnad1 id=eq.1h6v.s9.49891c60a53b from=translated src=- shape=bda8b11b vocab=5ae71750
-/
theorem algHom_apply_coe_eq {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (h : ∀ i, φ (X i) = ψ (X i)) (P : MvPolynomial σ 𝒪) :
    φ (P : MvPowerSeries σ 𝒪) = ψ (P : MvPowerSeries σ 𝒪) := by
  have : (φ.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝒪)) =
      (ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom 𝒪)) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [h i]
  simpa using congrArg (fun f => f P) this

end Vars

section Construction

variable {σ : Type w} [Finite σ] (𝒪 : Type u) {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
  (a : σ → A) (I : Ideal A) (ha : ∀ i, a i ∈ I)

include ha

omit [Finite σ] in
/--
@isnad1 id=le.1h6v.s9.f68e6593279a from=translated src=- shape=de5e6de9 vocab=0c568078
-/
theorem idealOfVars_pow_le (k : ℕ) :
    MvPolynomial.idealOfVars σ 𝒪 ^ k ≤ (I ^ k).comap (MvPolynomial.aeval (R := 𝒪) a).toRingHom := by
  refine le_trans (Ideal.pow_right_mono ?_ k) (Ideal.le_comap_pow _ k)
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using ha i

noncomputable def evalTrunc (k : ℕ) : MvPowerSeries σ 𝒪 →+* A ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (MvPolynomial.aeval (R := 𝒪) a).toRingHom
    (idealOfVars_pow_le 𝒪 a I ha k)).comp (truncTotalAlgHom σ 𝒪 k).toRingHom

/--
@isnad1 id=eq.1h7v.s10.1ccb109cbb1e from=translated src=- shape=4d8e4905 vocab=9db306c7
-/
theorem evalTrunc_apply (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    evalTrunc 𝒪 a I ha k p = Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  simp [evalTrunc]

/--
@isnad1 id=eq.2h7v.s9.b2d68ef50e59 from=translated src=- shape=78ed5ae7 vocab=891cc4e8
-/
theorem evalTrunc_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow I h).comp (evalTrunc 𝒪 a I ha l) = evalTrunc 𝒪 a I ha k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, evalTrunc_apply, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact idealOfVars_pow_le 𝒪 a I ha k (truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl p)

variable [IsAdicComplete I A]

noncomputable def lift : MvPowerSeries σ 𝒪 →+* A :=
  IsAdicComplete.liftRingHom I (evalTrunc 𝒪 a I ha) (fun h => evalTrunc_compat 𝒪 a I ha h)

/--
@isnad1 id=eq.1h7v.s10.0e3d641cf4bd from=translated src=- shape=804cb10c vocab=1ccd5082
-/
theorem mk_lift (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    Ideal.Quotient.mk (I ^ k) (lift 𝒪 a I ha p) =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  rw [lift, IsAdicComplete.mk_liftRingHom, evalTrunc_apply]

/--
@isnad1 id=eq.1h6v.s8.e22a88248b98 from=translated src=- shape=fa1ebe07 vocab=54d8d954
-/
theorem lift_coe (P : MvPolynomial σ 𝒪) :
    lift 𝒪 a I ha (P : MvPowerSeries σ 𝒪) = MvPolynomial.aeval (R := 𝒪) a P := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, ← Ideal.Quotient.eq, mk_lift, Ideal.Quotient.eq, ← map_sub]
  refine idealOfVars_pow_le 𝒪 a I ha k ?_
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx, MvPolynomial.coeff_coe]

/--
@isnad1 id=eq.1h6v.s8.7cebabb7a3ab from=translated src=- shape=8c066204 vocab=58d01939
-/
theorem lift_C (c : 𝒪) : lift 𝒪 a I ha (C c) = algebraMap 𝒪 A c := by
  rw [← MvPolynomial.coe_C, lift_coe, MvPolynomial.aeval_C]

noncomputable def liftAlgHom : MvPowerSeries σ 𝒪 →ₐ[𝒪] A :=
  { lift 𝒪 a I ha with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, lift_C] }

end Construction

section Heads

variable {σ : Type w} {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]

/--
@isnad1 id=eq.2h6v.s9.d1904e200583 from=translated src=- shape=f2e65655 vocab=16f6da9d
-/
theorem algHom_ext_of_X_mem [Finite σ] (I : Ideal A) [IsHausdorff I A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (X i) ∈ I) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ := by
  have hψ : ∀ i, ψ (X i) ∈ I := fun i => h i ▸ hφ i
  refine AlgHom.ext fun p => (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff]
  have hsplit : φ p - ψ p =
      φ (p - (truncTotal k p : MvPolynomial σ 𝒪)) - ψ (p - (truncTotal k p : MvPolynomial σ 𝒪)) := by
    rw [map_sub, map_sub, algHom_apply_coe_eq φ ψ h]; ring
  rw [hsplit]
  exact Ideal.sub_mem _
    (map_pow_span_X_le φ I hφ k (Ideal.mem_map_of_mem _ (sub_truncTotal_mem_pow_span_X k p)))
    (map_pow_span_X_le ψ I hψ k (Ideal.mem_map_of_mem _ (sub_truncTotal_mem_pow_span_X k p)))

end Heads

end M4cP4PS

/--
@isnad1 id=eq.2h6v.s9.1f6267554236 from=translated src=- shape=4a05cfd8 vocab=16f6da9d
-/
theorem solution {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ]
    [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsHausdorff I A]
    (φ ψ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ I)
    (h : ∀ i, φ (MvPowerSeries.X i) = ψ (MvPowerSeries.X i)) : φ = ψ :=
  M4cP4PS.algHom_ext_of_X_mem I φ ψ hφ h
