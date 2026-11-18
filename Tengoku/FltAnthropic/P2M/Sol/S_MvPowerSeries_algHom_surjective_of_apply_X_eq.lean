import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.AdicCompletion.RingHom
import Tengoku.Seed.RingTheory.AdicCompletion.Completeness
import Tengoku.Seed.RingTheory.MvPowerSeries.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_algHom_surjective_of_apply_X_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_algHom_surjective_of_apply_X_eq

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
@isnad1 id=eq.1h7v.s10.29ba2794cd83 from=translated src=- shape=4d8e4905 vocab=46e594d9
-/
theorem evalTrunc_apply (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    evalTrunc 𝒪 a I ha k p = Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  simp [evalTrunc]

/--
@isnad1 id=eq.2h7v.s9.4585ea1ab2bb from=translated src=- shape=78ed5ae7 vocab=de105856
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
@isnad1 id=eq.1h7v.s10.0fe3bdeaa7f9 from=translated src=- shape=804cb10c vocab=71d9c0af
-/
theorem mk_lift (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    Ideal.Quotient.mk (I ^ k) (lift 𝒪 a I ha p) =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  rw [lift, IsAdicComplete.mk_liftRingHom, evalTrunc_apply]

/--
@isnad1 id=eq.1h6v.s8.6113ede120a1 from=translated src=- shape=fa1ebe07 vocab=6eeb3d54
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
@isnad1 id=eq.1h6v.s8.f0bdd09ab445 from=translated src=- shape=8c066204 vocab=0db3b0ab
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
@isnad1 id=surjecti.3h5v.s9.8834c390389e from=translated src=- shape=8e3c78b9 vocab=ef5e4591
-/
theorem algHom_surjective_of_mk_comp_algebraMap_surjective [Finite σ] [IsLocalRing A]
    [IsNoetherianRing A] (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (a : σ → A) (hφ : ∀ i, φ (X i) = a i)
    (ha : ∀ i, a i ∈ maximalIdeal A)
    (h𝒪 : Function.Surjective (⇑(Ideal.Quotient.mk (Ideal.span (Set.range a))) ∘ ⇑(algebraMap 𝒪 A))) :
    Function.Surjective φ := by
  classical
  set Ia : Ideal A := Ideal.span (Set.range a) with hIa
  set J : Ideal (MvPowerSeries σ 𝒪) := Ideal.span (Set.range X) with hJdef
  have hIa𝔪 : Ia ≤ maximalIdeal A := by rw [hIa, Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ha i
  have hφ𝔪 : ∀ i, φ (X i) ∈ maximalIdeal A := fun i => (hφ i).symm ▸ ha i

  have step0 : ∀ x : A, ∃ b : MvPowerSeries σ 𝒪, x - φ b ∈ Ia := by
    intro x
    obtain ⟨c, hc⟩ := h𝒪 (Ideal.Quotient.mk Ia x)
    refine ⟨C c, ?_⟩
    rw [← Ideal.Quotient.eq, show (C c : MvPowerSeries σ 𝒪) = algebraMap 𝒪 _ c by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply], AlgHom.commutes]
    exact hc.symm

  have claim : ∀ (k : ℕ) (x : A), x ∈ Ia ^ k → ∃ b ∈ J ^ k, x - φ b ∈ Ia ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨b, hb⟩ := step0 x
      exact ⟨b, by simp, by simpa using hb⟩
    | succ k ih =>
      intro x hx
      rw [pow_succ, hIa] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro m hm z hz
        induction hz using Submodule.span_induction generalizing m with
        | mem _ h =>
          obtain ⟨i, rfl⟩ := h
          obtain ⟨b, hbJ, hb⟩ := ih m hm
          refine ⟨b * X i, ?_, ?_⟩
          · rw [pow_succ]; exact Ideal.mul_mem_mul hbJ (Ideal.subset_span ⟨i, rfl⟩)
          · rw [map_mul, hφ, show m * a i - φ b * a i = (m - φ b) * a i by ring, pow_succ]
            exact Ideal.mul_mem_mul hb (Ideal.subset_span ⟨i, rfl⟩)
        | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
        | add z₁ z₂ _ _ ih₁ ih₂ =>
          obtain ⟨b₁, hb₁J, hb₁⟩ := ih₁ m hm
          obtain ⟨b₂, hb₂J, hb₂⟩ := ih₂ m hm
          refine ⟨b₁ + b₂, Ideal.add_mem _ hb₁J hb₂J, ?_⟩
          rw [show m * (z₁ + z₂) - φ (b₁ + b₂) = (m * z₁ - φ b₁) + (m * z₂ - φ b₂) by
            rw [map_add]; ring]
          exact Ideal.add_mem _ hb₁ hb₂
        | smul c z _ ihz =>
          obtain ⟨b, hbJ, hb⟩ := ihz (c * m) (Ideal.mul_mem_left _ _ hm)
          refine ⟨b, hbJ, ?_⟩
          rwa [smul_eq_mul, show m * (c * z) = c * m * z by ring]
      · intro x y hx hy
        obtain ⟨b₁, hb₁J, hb₁⟩ := hx
        obtain ⟨b₂, hb₂J, hb₂⟩ := hy
        refine ⟨b₁ + b₂, Ideal.add_mem _ hb₁J hb₂J, ?_⟩
        rw [show x + y - φ (b₁ + b₂) = (x - φ b₁) + (y - φ b₂) by rw [map_add]; ring]
        exact Ideal.add_mem _ hb₁ hb₂
  choose β hβJ hβ using claim
  intro x

  let t : (k : ℕ) → {s : MvPowerSeries σ 𝒪 // x - φ s ∈ Ia ^ k} :=
    fun k => Nat.rec ⟨0, by simp⟩
      (fun k sk => ⟨sk.1 + β k (x - φ sk.1) sk.2, by
        rw [map_add, show x - (φ sk.1 + φ (β k (x - φ sk.1) sk.2)) =
          (x - φ sk.1) - φ (β k (x - φ sk.1) sk.2) by ring]
        exact hβ k _ sk.2⟩) k
  let s : ℕ → MvPowerSeries σ 𝒪 := fun k => (t k).1
  have hs_succ : ∀ k, s (k + 1) = s k + β k (x - φ (s k)) (t k).2 := fun k => rfl
  have hsI : ∀ k, x - φ (s k) ∈ Ia ^ k := fun k => (t k).2
  have hcauchy : ∀ m l, m ≤ l → s l - s m ∈ J ^ m := by
    intro m l hml
    induction l, hml using Nat.le_induction with
    | base => simp
    | succ k hmk ihk =>
      rw [hs_succ, show s k + β k (x - φ (s k)) (t k).2 - s m =
        (s k - s m) + β k (x - φ (s k)) (t k).2 by ring]
      exact Ideal.add_mem _ ihk (Ideal.pow_le_pow_right hmk (hβJ k _ (t k).2))

  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete J (MvPowerSeries σ 𝒪))
    (f := s) (fun {m l} hml => by
      rw [smodEq_pow_smul_top_iff]
      have := hcauchy m l hml
      rwa [← neg_sub, Ideal.neg_mem_iff])
  refine ⟨L, ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, show φ L - x = φ (L - s k) - (x - φ (s k)) by rw [map_sub]; ring]
  refine Ideal.sub_mem _ ?_ (Ideal.pow_right_mono hIa𝔪 k (hsI k))
  refine map_pow_span_X_le φ _ hφ𝔪 k (Ideal.mem_map_of_mem _ ?_)
  have := (smodEq_pow_smul_top_iff J k _ _).mp (hL k)
  rwa [← neg_sub, Ideal.neg_mem_iff] at this

end Heads

end M4cP4PS

/--
@isnad1 id=surjecti.3h5v.s9.ed006b7ae1e6 from=translated src=- shape=f34394bc vocab=ef5e4591
-/
theorem solution {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ]
    [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A]
    (φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A) (a : σ → A) (hφ : ∀ i, φ (MvPowerSeries.X i) = a i)
    (ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A)
    (h𝒪 : Function.Surjective (⇑(Ideal.Quotient.mk (Ideal.span (Set.range a))) ∘ ⇑(algebraMap 𝒪 A))) :
    Function.Surjective φ :=
  M4cP4PS.algHom_surjective_of_mk_comp_algebraMap_surjective φ a hφ ha h𝒪
