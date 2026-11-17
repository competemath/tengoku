import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_FunctionField
import Tengoku.FltAnthropic.Theorems.Thm_MvPolynomial_mem_span_map_of_aeval_X_pow_mem_span_map
import Tengoku.FltAnthropic.Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DrinfeldCurve_exists_algHom_drinfeldFunctionField_apply_x_eq_pow.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DrinfeldCurve_exists_algHom_drinfeldFunctionField_apply_x_eq_pow

set_option autoImplicit false

namespace DrinfeldCurve
export _root_.DrinfeldCurve (drinfeldFunctionField drinfeldPoly drinfeldIdeal CoordRing mk mk_surjective x y isDomain_coordRing_of_ne_one)
open _root_.DrinfeldCurve

namespace FrobAux

open MvPolynomial

variable (q : ℕ) [Fact q.Prime] (K : Type) [Field K] [CharP K q] [IsDomain (CoordRing q K)] (n : ℕ)

noncomputable def psi : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval fun i => (X i : MvPolynomial (Fin 2) K) ^ q ^ n

/--
@isnad1 id=eq.0h4v.s9.d3cc2afc8b51 from=translated src=- shape=e6e00fd1 vocab=bf1a07a4
-/
theorem psi_X (i : Fin 2) : psi q K n (X i) = X i ^ q ^ n := by
  rw [psi, aeval_X]

/--
@isnad1 id=eq.0h3v.s9.685171518dcf from=translated src=- shape=a59dfc5a vocab=595c66dc
-/
theorem psi_drinfeldPoly_sub_one : psi q K n (drinfeldPoly q K - 1) = (drinfeldPoly q K - 1) ^ q ^ n := by
  rw [drinfeldPoly, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_one, psi_X, psi_X,
    sub_pow_char_pow, sub_pow_char_pow, one_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
    mul_comm q (q ^ n)]

/--
@isnad1 id=mem.1h4v.s9.71bc6581e88d from=translated src=- shape=081ad687 vocab=8538f7fb
-/
theorem psi_mem (a : MvPolynomial (Fin 2) K) (ha : a ∈ drinfeldIdeal q K) : psi q K n a ∈ drinfeldIdeal q K := by
  rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [map_mul, psi_drinfeldPoly_sub_one, drinfeldIdeal]
  have hN : q ^ n ≠ 0 := pow_ne_zero n (Fact.out : q.Prime).ne_zero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN
  rw [hm, pow_succ, ← mul_assoc]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

noncomputable def phi0 : CoordRing q K →ₐ[K] CoordRing q K :=
  Ideal.Quotient.liftₐ (drinfeldIdeal q K) ((mk q K).comp (psi q K n)) (fun a ha => by
    rw [AlgHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (psi_mem q K n a ha))

/--
@isnad1 id=eq.0h4v.s10.16cfe245afac from=translated src=- shape=783cc4c1 vocab=e87de8c6
-/
theorem phi0_mk (a : MvPolynomial (Fin 2) K) : phi0 q K n (mk q K a) = mk q K (psi q K n a) := rfl

/--
@isnad1 id=eq.0h3v.s7.9adb2074ae99 from=translated src=- shape=5f3057bd vocab=d5ffbf17
-/
theorem phi0_x : phi0 q K n (x q K) = x q K ^ q ^ n := by
  rw [x, phi0_mk, psi_X, map_pow]

/--
@isnad1 id=eq.0h3v.s7.87ee51b3edcc from=translated src=- shape=5f3057bd vocab=7a6c6212
-/
theorem phi0_y : phi0 q K n (y q K) = y q K ^ q ^ n := by
  rw [y, phi0_mk, psi_X, map_pow]

/--
@isnad1 id=eq.0h2v.s9.ba7cec3be68d from=translated src=- shape=71a458ff vocab=b24ad47b
-/
theorem map_drinfeldPoly_sub_one [Algebra (ZMod q) K] :
    MvPolynomial.map (algebraMap (ZMod q) K) (drinfeldPoly q (ZMod q) - 1) = drinfeldPoly q K - 1 := by
  rw [drinfeldPoly, drinfeldPoly, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_X, map_X, map_one]

/--
@isnad1 id=ne.0h2v.s8.73f387b34fbb from=translated src=- shape=78065fe5 vocab=bb38ffd7
-/
theorem drinfeldPoly_sub_one_ne_zero (k : Type) [Field k] : drinfeldPoly q k - 1 ≠ 0 := by
  intro h
  have := congrArg MvPolynomial.constantCoeff h
  rw [drinfeldPoly, map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, constantCoeff_X, constantCoeff_X,
    map_one, zero_pow (Fact.out : q.Prime).ne_zero] at this
  simp at this

/--
@isnad1 id=prime.0h1v.s8.242fa69638b7 from=translated src=- shape=d970c7c6 vocab=7c31dc6a
-/
theorem prime_drinfeldPoly_sub_one_zmod : Prime (drinfeldPoly q (ZMod q) - 1) := by
  haveI : IsDomain (CoordRing q (ZMod q)) := isDomain_coordRing_of_ne_one q (Fact.out : q.Prime).one_lt.ne' (ZMod q)
  have hI : (drinfeldIdeal q (ZMod q)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (drinfeldIdeal q (ZMod q))).mp (show IsDomain (CoordRing q (ZMod q)) from inferInstance)
  rw [drinfeldIdeal, Ideal.span_singleton_prime (drinfeldPoly_sub_one_ne_zero q (ZMod q))] at hI
  exact hI

/--
@isnad1 id=injectiv.0h3v.s7.d41b92e588e8 from=translated src=- shape=2457633d vocab=862de5cc
-/
theorem phi0_injective : Function.Injective (phi0 q K n) := by
  letI : Algebra (ZMod q) K := ZMod.algebra K q
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := mk_surjective q K a
  rw [phi0_mk] at ha
  have hg : psi q K n g ∈ drinfeldIdeal q K := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  have key := MvPolynomial.mem_span_map_of_aeval_X_pow_mem_span_map (K := K) n (drinfeldPoly q (ZMod q) - 1)
    (prime_drinfeldPoly_sub_one_zmod q) g (by
      rw [map_drinfeldPoly_sub_one]
      exact hg)
  rw [map_drinfeldPoly_sub_one] at key
  exact Ideal.Quotient.eq_zero_iff_mem.mpr key

/--
@isnad1 id=injectiv.0h3v.s9.180c6f3ebe69 from=translated src=- shape=8171ef56 vocab=017dae06
-/
theorem comp_injective :
    Function.Injective ((algebraMap (CoordRing q K) (drinfeldFunctionField q K)).comp (phi0 q K n).toRingHom) :=
  (IsFractionRing.injective (CoordRing q K) (drinfeldFunctionField q K)).comp (phi0_injective q K n)

noncomputable def phiF : drinfeldFunctionField q K →+* drinfeldFunctionField q K :=
  IsFractionRing.lift (comp_injective q K n)

/--
@isnad1 id=eq.0h4v.s10.750821a15db6 from=translated src=- shape=bc91cf34 vocab=d4e9d331
-/
theorem phiF_algebraMap (a : CoordRing q K) :
    phiF q K n (algebraMap (CoordRing q K) (drinfeldFunctionField q K) a) =
      algebraMap (CoordRing q K) (drinfeldFunctionField q K) (phi0 q K n a) :=
  IsFractionRing.lift_algebraMap (comp_injective q K n) a

noncomputable def phiAlg : drinfeldFunctionField q K →ₐ[K] drinfeldFunctionField q K :=
  { phiF q K n with
    commutes' := fun c => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply K (CoordRing q K) (drinfeldFunctionField q K), phiF_algebraMap,
        AlgHom.commutes] }

/--
@isnad1 id=eq.0h4v.s10.663bdf189444 from=translated src=- shape=52ddcb5b vocab=1af7dbf9
-/
theorem phiAlg_apply (z : drinfeldFunctionField q K) : phiAlg q K n z = phiF q K n z := rfl

end FrobAux

end DrinfeldCurve

open _root_.DrinfeldCurve _root_.P2MW.S_DrinfeldCurve_exists_algHom_drinfeldFunctionField_apply_x_eq_pow.DrinfeldCurve in

/--
@isnad1 id=ex.0h3v.s12.4d198a23ac40 from=translated src=- shape=499c97af vocab=736a2a4a
-/
theorem solution (q : ℕ) [Fact q.Prime] (K : Type) [Field K]
    [CharP K q] [IsDomain (CoordRing q K)] (n : ℕ) :
    ∃ φ : drinfeldFunctionField q K →ₐ[K] drinfeldFunctionField q K,
      φ (algebraMap (CoordRing q K) (drinfeldFunctionField q K) (x q K)) =
          algebraMap (CoordRing q K) (drinfeldFunctionField q K) (x q K) ^ q ^ n ∧
        φ (algebraMap (CoordRing q K) (drinfeldFunctionField q K) (y q K)) =
          algebraMap (CoordRing q K) (drinfeldFunctionField q K) (y q K) ^ q ^ n := by
  refine ⟨FrobAux.phiAlg q K n, ?_, ?_⟩
  · rw [FrobAux.phiAlg_apply, FrobAux.phiF_algebraMap, FrobAux.phi0_x, map_pow]
  · rw [FrobAux.phiAlg_apply, FrobAux.phiF_algebraMap, FrobAux.phi0_y, map_pow]
