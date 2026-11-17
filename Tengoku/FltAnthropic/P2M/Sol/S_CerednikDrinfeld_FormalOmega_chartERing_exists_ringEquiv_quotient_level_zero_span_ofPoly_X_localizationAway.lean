import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_exists_ringEquiv_quotient_level_zero_span_ofPoly_X_localizationAway

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace BranchIso29

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ)

/--
@isnad1 id=eq.0h3v.s8.2ca991c7c3ec from=translated src=- shape=bcfce955 vocab=f9549467
-/
theorem algebraMap_pi_eq_zero (T : Type) [CommRing T] [Algebra 𝒪 T] [Algebra (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T] [IsScalarTower 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T] :
    algebraMap 𝒪 T π = 0 := by
  rw [IsScalarTower.algebraMap_apply 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) T, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]

noncomputable def pt (hr : 1 < r) (i : Fin 2) : (chartE 𝒪 π r).obj (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  ⟨(if i = 0 then 0 else algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()),
    if i = 0 then algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()) else 0), by
    have hπ0 : algebraMap 𝒪 (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) π = 0 := algebraMap_pi_eq_zero 𝒪 π (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))
    have hu0 : IsUnit ((0 : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))) ^ (r - 1) - 1) := by
      rw [zero_pow (by omega), zero_sub]; exact isUnit_one.neg
    have hut : IsUnit ((algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ())) ^ (r - 1) - 1) := by
      rw [← map_pow, ← map_one (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))), ← map_sub]
      exact IsLocalization.Away.algebraMap_isUnit _
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp [hπ0]
    · split_ifs <;> assumption
    · split_ifs <;> assumption⟩

/--
@isnad1 id=eq.1h4v.s16.672f2d6abfcf from=translated src=- shape=b9bc5aa5 vocab=fc1bbf59
-/
theorem evalPoly_pt_X_self (hr : 1 < r) (i : Fin 2) :
    chartERing.evalPoly (pt 𝒪 π r hr i) (MvPolynomial.X i) = 0 := by
  fin_cases i <;> simp [chartERing.evalPoly, pt, MvPolynomial.aeval_X]

/--
@isnad1 id=eq.1h4v.s16.9b32dfcc2a21 from=translated src=- shape=ec983ec7 vocab=733dd7da
-/
theorem evalPoly_pt_X_other (hr : 1 < r) (i : Fin 2) :
    chartERing.evalPoly (pt 𝒪 π r hr i) (MvPolynomial.X (1 - i)) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ()) := by
  fin_cases i <;> simp [chartERing.evalPoly, pt, MvPolynomial.aeval_X]

noncomputable def F₀ (hr : 1 < r) (i : Fin 2) : chartERing 𝒪 π r →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) := chartERing.lift (pt 𝒪 π r hr i)

noncomputable def F₁ (hr : 1 < r) (i : Fin 2) : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  Ideal.Quotient.liftₐ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (F₀ 𝒪 π r hr i) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, AlgHom.commutes, algebraMap_pi_eq_zero 𝒪 π (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)), zero_pow (by omega), mul_zero])

/--
@isnad1 id=eq.1h5v.s16.ab7523a6c0b9 from=translated src=- shape=2cff4ca8 vocab=f40c4a5e
-/
theorem F₁_mk (hr : 1 < r) (i : Fin 2) (x : chartERing 𝒪 π r) :
    F₁ 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) x) = F₀ 𝒪 π r hr i x := rfl

noncomputable def F (hr : 1 < r) (i : Fin 2) : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) →ₐ[𝒪] (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) :=
  Ideal.Quotient.liftₐ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (F₁ 𝒪 π r hr i) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, F₁_mk, F₀, chartERing.lift_ofPoly, evalPoly_pt_X_self, mul_zero])

/--
@isnad1 id=eq.1h5v.s18.11e4f3784b24 from=translated src=- shape=24620e19 vocab=31166b6f
-/
theorem F_mk_mk (hr : 1 < r) (i : Fin 2) (x : chartERing 𝒪 π r) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) x)) = chartERing.lift (pt 𝒪 π r hr i) x := rfl

/--
@isnad1 id=eq.1h5v.s18.9c44815a31ea from=translated src=- shape=3a3e0e26 vocab=cb9f0222
-/
theorem F_algebraMap (hr : 1 < r) (i : Fin 2) (a : 𝒪) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
      algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a) := by
  rw [F_mk_mk, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)), Ideal.Quotient.algebraMap_eq]

/--
@isnad1 id=eq.1h4v.s18.80d567cd3f52 from=translated src=- shape=065a6e71 vocab=cb9f0222
-/
theorem F_X_other (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) := by
  rw [F_mk_mk, chartERing.lift_ofPoly, evalPoly_pt_X_other]

/--
@isnad1 id=eq.1h4v.s18.e61de2cc1150 from=translated src=- shape=13387abd vocab=cb9f0222
-/
theorem F_X_self (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i)))) = 0 := by
  rw [F_mk_mk, chartERing.lift_ofPoly, evalPoly_pt_X_self]

/--
@isnad1 id=eq.0h4v.s16.5f54718586af from=translated src=- shape=5dce7f80 vocab=3f5a4d79
-/
theorem algebraMap_C (c : (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) :
    algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.C c) = algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) c := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/--
@isnad1 id=eq.3h5v.s19.07173aed88c6 from=translated src=- shape=e2b15c5c vocab=e2431c6a
-/
theorem F_comp_G (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    (F 𝒪 π r hr i).toRingHom.comp G = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1))
  apply MvPolynomial.ringHom_ext
  · intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hGC,
      F_algebraMap, algebraMap_C]
  · intro u
    cases u
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hGX, F_X_other]

/--
@isnad1 id=or.0h2v.s6.85c474eefe97 from=translated src=- shape=66153986 vocab=dcfa4cf8
-/
theorem fin2_cases (i j : Fin 2) : j = i ∨ j = 1 - i := by
  fin_cases i <;> fin_cases j <;> decide

/--
@isnad1 id=eq.0h4v.s11.cdca3f9569be from=translated src=- shape=9feeb60b vocab=3f889d03
-/
theorem ofPoly_eq (p : MvPolynomial (Fin 2) 𝒪) :
    chartERing.ofPoly 𝒪 π r p = algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r) (Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π}) p) := rfl

/--
@isnad1 id=eq.1h4v.s18.9bd94fbfe476 from=translated src=- shape=bca93b85 vocab=b0c1bfa8
-/
theorem F_X_self' (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X i))))) = 0 :=
  F_X_self 𝒪 π r hr i

/--
@isnad1 id=eq.1h4v.s18.531d6251128d from=translated src=- shape=28236359 vocab=b0c1bfa8
-/
theorem F_X_other' (hr : 1 < r) (i : Fin 2) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X (1 - i)))))) =
      algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) :=
  F_X_other 𝒪 π r hr i

/--
@isnad1 id=eq.0h4v.s17.afa3a32cb391 from=translated src=- shape=8c4a9f73 vocab=c7b5f08c
-/
theorem mk_mk_X_self (i : Fin 2) :
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X i)))) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/--
@isnad1 id=eq.1h5v.s18.b7d0c54bc32e from=translated src=- shape=23ed5826 vocab=54f3dfae
-/
theorem F_algebraMap' (hr : 1 < r) (i : Fin 2) (a : 𝒪) :
    F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a))))) =
      algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a) := by
  have h1 : (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)) = algebraMap 𝒪 (chartERing 𝒪 π r) a := by
    rw [← ofPoly_eq, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [h1]; exact F_algebraMap 𝒪 π r hr i a

/--
@isnad1 id=eq.0h5v.s18.665011844ef6 from=translated src=- shape=5849bc4c vocab=9f6b3d47
-/
theorem mk_mk_C (i : Fin 2) (a : 𝒪) :
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  have h1 : (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)) = algebraMap 𝒪 (chartERing 𝒪 π r) a := by
    rw [← ofPoly_eq, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [h1]

/--
@isnad1 id=eq.3h5v.s20.a47f83684c44 from=translated src=- shape=4ea10d16 vocab=e2431c6a
-/
theorem G_comp_F (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    G.comp (F 𝒪 π r hr i).toRingHom = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (edgeQuot.discr 𝒪 π r))
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_))
  · show G (F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a)))))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.C a))))
    exact ((congrArg G (F_algebraMap' 𝒪 π r hr i a)).trans ((congrArg G (algebraMap_C 𝒪 π r _).symm).trans (hGC a))).trans
      (mk_mk_C 𝒪 π r i a).symm
  · show G (F 𝒪 π r hr i (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X j)))))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) ((algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) ((Ideal.Quotient.mk (Ideal.span {edgeRel 𝒪 π})) (MvPolynomial.X j))))
    rcases fin2_cases i j with hj | hj
    · subst hj
      exact ((congrArg G (F_X_self' 𝒪 π r hr j)).trans (map_zero G)).trans (mk_mk_X_self 𝒪 π r j).symm
    · subst hj
      exact (congrArg G (F_X_other' 𝒪 π r hr i)).trans hGX

/--
@isnad1 id=ex.3h5v.s21.5ce74029c003 from=translated src=- shape=b26daed8 vocab=22f5358e
-/
theorem assemble (hr : 1 < r) (i : Fin 2) (G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})))
    (hGC : ∀ a : 𝒪, G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.C (Ideal.Quotient.mk _ a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)))
    (hGX : G (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) :
    ∃ e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) ≃+* (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)),
      (∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) ∧
      e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
          algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) :=
  ⟨RingEquiv.ofRingHom (F 𝒪 π r hr i).toRingHom G (F_comp_G 𝒪 π r hr i G hGC hGX) (G_comp_F 𝒪 π r hr i G hGC hGX),
    fun a => F_algebraMap 𝒪 π r hr i a, F_X_other 𝒪 π r hr i⟩

end BranchIso29

namespace BranchIso29G

section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (i : Fin 2)

/--
@isnad1 id=isunit.0h4v.s10.bbfd2f51c816 from=translated src=- shape=42b06c33 vocab=4afeed18
-/
theorem isUnit_ofPoly_X_pow_sub_one (j : Fin 2) :
    IsUnit ((chartERing.ofPoly 𝒪 π r (MvPolynomial.X j)) ^ (r - 1) - 1) := by
  fin_cases j
  · exact isUnit_of_mul_isUnit_left (chartERing.isUnit_discr 𝒪 π r)
  · exact isUnit_of_mul_isUnit_right (chartERing.isUnit_discr 𝒪 π r)

noncomputable def cG : (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  Ideal.Quotient.lift (Ideal.span {π ^ (0 + 1)})
    ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp ((Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})).comp (algebraMap 𝒪 (chartERing 𝒪 π r))))
    (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      have h : algebraMap 𝒪 (chartERing 𝒪 π r) (b * π ^ (0 + 1)) ∈ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) := by
        rw [map_mul (algebraMap 𝒪 (chartERing 𝒪 π r)), map_pow (algebraMap 𝒪 (chartERing 𝒪 π r))]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero])

noncomputable def gG : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  MvPolynomial.eval₂Hom (cG 𝒪 π r i)
    (fun _ => Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))))

/--
@isnad1 id=eq.0h4v.s18.f51deec64bc3 from=translated src=- shape=b500ebb1 vocab=886502a3
-/
theorem gG_X : gG 𝒪 π r i (MvPolynomial.X ()) =
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))) := by
  rw [gG, MvPolynomial.eval₂Hom_X']

/--
@isnad1 id=eq.0h5v.s18.df227ec0b994 from=translated src=- shape=c723d3bc vocab=7a4330de
-/
theorem gG_C (a : 𝒪) : gG 𝒪 π r i (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {π ^ (0 + 1)}) a)) =
    Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  rw [gG, MvPolynomial.eval₂Hom_C]; rfl

set_option synthInstance.maxHeartbeats 1600000 in
/--
@isnad1 id=isunit.0h4v.s17.c7e82692f840 from=translated src=- shape=77198b24 vocab=1381adfc
-/
theorem isUnit_gG : IsUnit (gG 𝒪 π r i ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) := by
  have h : gG 𝒪 π r i ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1) =
      (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) ^ (r - 1) - 1 := by
    rw [map_sub (gG 𝒪 π r i), map_pow (gG 𝒪 π r i), map_one (gG 𝒪 π r i), gG_X]
  have hu := (isUnit_ofPoly_X_pow_sub_one 𝒪 π r (1 - i)).map
    ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})))
  rw [map_sub ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))),
    map_pow ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))),
    map_one ((Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})).comp (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))), RingHom.comp_apply] at hu
  rw [h]
  exact hu

noncomputable def G : (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) →+* (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))})) :=
  IsLocalization.Away.lift ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1) (isUnit_gG 𝒪 π r i)

/--
@isnad1 id=eq.0h5v.s18.0aa60d4d26ea from=translated src=- shape=18a30219 vocab=0636293a
-/
theorem G_algebraMap (p : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) p) = gG 𝒪 π r i p :=
  IsLocalization.Away.lift_eq _ (isUnit_gG 𝒪 π r i) p

/--
@isnad1 id=eq.0h5v.s18.97b4571b6257 from=translated src=- shape=b548ff59 vocab=16cc742a
-/
theorem G_algebraMap_C (a : 𝒪) :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {π ^ (0 + 1)}) a))) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a)) := by
  rw [G_algebraMap, gG_C]

/--
@isnad1 id=eq.0h4v.s18.d75ccf5f335c from=translated src=- shape=ebec83c3 vocab=628ea821
-/
theorem G_algebraMap_X :
    G 𝒪 π r i (algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) (Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1)) (MvPolynomial.X ())) =
      Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i)))) := by
  rw [G_algebraMap, gG_X]

end

end BranchIso29G

/--
@isnad1 id=ex.2h4v.s20.9d479ca77ec7 from=translated src=- shape=240cc7fb vocab=5e786e33
-/
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) (hr : 1 < r) (i : Fin 2) :
    ∃ e : (((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) ⧸ Ideal.span {Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X i))}) ≃+*
        Localization.Away ((MvPolynomial.X () : MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) ^ (r - 1) - 1),
      (∀ a : 𝒪, e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r) a))) =
          algebraMap (𝒪 ⧸ Ideal.span {π ^ (0 + 1)}) _ (Ideal.Quotient.mk _ a)) ∧
      e (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}) (chartERing.ofPoly 𝒪 π r (MvPolynomial.X (1 - i))))) =
          algebraMap (MvPolynomial Unit (𝒪 ⧸ Ideal.span {π ^ (0 + 1)})) _ (MvPolynomial.X ()) := by
  obtain ⟨e, he₁, he₂⟩ := BranchIso29.assemble 𝒪 π r hr i (BranchIso29G.G 𝒪 π r i)
    (BranchIso29G.G_algebraMap_C 𝒪 π r i) (BranchIso29G.G_algebraMap_X 𝒪 π r i)
  exact ⟨e, he₁, he₂⟩
