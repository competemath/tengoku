import Tengoku.Seed.RingTheory.MvPowerSeries.Inverse
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.AdicCompletion.RingHom
import Tengoku.Seed.RingTheory.AdicCompletion.Completeness
import Tengoku.Seed.RingTheory.MvPowerSeries.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_exists_algHom_apply_X_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_exists_algHom_apply_X_eq

set_option autoImplicit false

universe u v w

namespace M4cP4PS

open MvPowerSeries IsLocalRing

section Vars

variable {σ : Type w} {R : Type u} [CommRing R]

theorem smodEq_pow_smul_top_iff (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

def dropVar (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

end Vars

section Construction

variable {σ : Type w} [Finite σ] (𝒪 : Type u) {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]
  (a : σ → A) (I : Ideal A) (ha : ∀ i, a i ∈ I)

include ha

omit [Finite σ] in
theorem idealOfVars_pow_le (k : ℕ) :
    MvPolynomial.idealOfVars σ 𝒪 ^ k ≤ (I ^ k).comap (MvPolynomial.aeval (R := 𝒪) a).toRingHom := by
  refine le_trans (Ideal.pow_right_mono ?_ k) (Ideal.le_comap_pow _ k)
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simpa using ha i

noncomputable def evalTrunc (k : ℕ) : MvPowerSeries σ 𝒪 →+* A ⧸ I ^ k :=
  (Ideal.quotientMap (I ^ k) (MvPolynomial.aeval (R := 𝒪) a).toRingHom
    (idealOfVars_pow_le 𝒪 a I ha k)).comp (truncTotalAlgHom σ 𝒪 k).toRingHom

theorem evalTrunc_apply (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    evalTrunc 𝒪 a I ha k p = Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  simp [evalTrunc]

theorem evalTrunc_compat {k l : ℕ} (h : k ≤ l) :
    (Ideal.Quotient.factorPow I h).comp (evalTrunc 𝒪 a I ha l) = evalTrunc 𝒪 a I ha k := by
  ext p
  simp only [RingHom.coe_comp, Function.comp_apply, evalTrunc_apply, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact idealOfVars_pow_le 𝒪 a I ha k (truncTotal_sub_truncTotal_mem_pow_idealOfVars h le_rfl p)

variable [IsAdicComplete I A]

noncomputable def lift : MvPowerSeries σ 𝒪 →+* A :=
  IsAdicComplete.liftRingHom I (evalTrunc 𝒪 a I ha) (fun h => evalTrunc_compat 𝒪 a I ha h)

theorem mk_lift (k : ℕ) (p : MvPowerSeries σ 𝒪) :
    Ideal.Quotient.mk (I ^ k) (lift 𝒪 a I ha p) =
      Ideal.Quotient.mk (I ^ k) (MvPolynomial.aeval (R := 𝒪) a (truncTotal k p)) := by
  rw [lift, IsAdicComplete.mk_liftRingHom, evalTrunc_apply]

theorem lift_coe (P : MvPolynomial σ 𝒪) :
    lift 𝒪 a I ha (P : MvPowerSeries σ 𝒪) = MvPolynomial.aeval (R := 𝒪) a P := by
  refine (IsHausdorff.eq_iff_smodEq (I := I)).mpr fun k => ?_
  rw [smodEq_pow_smul_top_iff, ← Ideal.Quotient.eq, mk_lift, Ideal.Quotient.eq, ← map_sub]
  refine idealOfVars_pow_le 𝒪 a I ha k ?_
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  intro x hx
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx, MvPolynomial.coeff_coe]

theorem lift_X (i : σ) : lift 𝒪 a I ha (X i) = a i := by
  rw [← MvPolynomial.coe_X, lift_coe, MvPolynomial.aeval_X]

theorem lift_C (c : 𝒪) : lift 𝒪 a I ha (C c) = algebraMap 𝒪 A c := by
  rw [← MvPolynomial.coe_C, lift_coe, MvPolynomial.aeval_C]

noncomputable def liftAlgHom : MvPowerSeries σ 𝒪 →ₐ[𝒪] A :=
  { lift 𝒪 a I ha with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe]
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, lift_C] }

theorem liftAlgHom_X (i : σ) : liftAlgHom 𝒪 a I ha (X i) = a i := lift_X 𝒪 a I ha i

end Construction

section Heads

variable {σ : Type w} {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A]

theorem exists_algHom_X_eq [Finite σ] (I : Ideal A) [IsAdicComplete I A] (a : σ → A)
    (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (X i) = a i :=
  ⟨liftAlgHom 𝒪 a I ha, liftAlgHom_X 𝒪 a I ha⟩

end Heads

end M4cP4PS

theorem solution {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ]
    [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A] (a : σ → A)
    (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  M4cP4PS.exists_algHom_X_eq I a ha
