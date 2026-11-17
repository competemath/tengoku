import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_FormalOmega_exists_algHom_chartERing_chartVRing_isLocalization_away.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_algHom_chartERing_chartVRing_isLocalization_away

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace VertexInEdgeAux

noncomputable section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (n : ℕ)

/--
@isnad1 id=eq.3h6v.s10.ca8e43df84b2 from=translated src=- shape=5d7cdc74 vocab=b6e6948c
-/
theorem ringHom_ext_E {T : Type} [CommRing T] {g₁ g₂ : chartERing 𝒪 π r →+* T}
    (h : g₁.comp (algebraMap 𝒪 (chartERing 𝒪 π r)) = g₂.comp (algebraMap 𝒪 (chartERing 𝒪 π r)))
    (hξ : g₁ (chartERing.ξ 𝒪 π r) = g₂ (chartERing.ξ 𝒪 π r))
    (hη : g₁ (chartERing.η 𝒪 π r) = g₂ (chartERing.η 𝒪 π r)) : g₁ = g₂ := by
  letI : Algebra 𝒪 T := (g₁.comp (algebraMap 𝒪 (chartERing 𝒪 π r))).toAlgebra
  let a₁ : chartERing 𝒪 π r →ₐ[𝒪] T := ⟨g₁, fun _ => rfl⟩
  let a₂ : chartERing 𝒪 π r →ₐ[𝒪] T := ⟨g₂, fun x => (RingHom.congr_fun h x).symm⟩
  have h12 : a₁ = a₂ :=
    (chartERing.corepEquiv 𝒪 π r T).injective (Subtype.ext (Prod.ext (by exact hξ) (by exact hη)))
  exact RingHom.ext fun z => AlgHom.congr_fun h12 z

/--
@isnad1 id=eq.2h5v.s10.1d48318a9417 from=translated src=- shape=7be2b7ce vocab=71c4901f
-/
theorem ringHom_ext_V {T : Type} [CommRing T] {g₁ g₂ : chartVRing 𝒪 r →+* T}
    (h : g₁.comp (algebraMap 𝒪 (chartVRing 𝒪 r)) = g₂.comp (algebraMap 𝒪 (chartVRing 𝒪 r)))
    (hζ : g₁ (chartVRing.ζ 𝒪 r) = g₂ (chartVRing.ζ 𝒪 r)) : g₁ = g₂ := by
  letI : Algebra 𝒪 T := (g₁.comp (algebraMap 𝒪 (chartVRing 𝒪 r))).toAlgebra
  let a₁ : chartVRing 𝒪 r →ₐ[𝒪] T := ⟨g₁, fun _ => rfl⟩
  let a₂ : chartVRing 𝒪 r →ₐ[𝒪] T := ⟨g₂, fun x => (RingHom.congr_fun h x).symm⟩
  have h12 : a₁ = a₂ :=
    (chartVRing.corepEquiv 𝒪 r T).injective (Subtype.ext (by exact hζ))
  exact RingHom.ext fun z => AlgHom.congr_fun h12 z

abbrev IE : Ideal (chartERing 𝒪 π r) := Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}

abbrev IV : Ideal (chartVRing 𝒪 r) := Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}

abbrev An : Type := chartERing 𝒪 π r ⧸ IE 𝒪 π r n

abbrev Pn : Type := chartVRing 𝒪 r ⧸ IV 𝒪 π r n

abbrev ξb : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)

abbrev ηb : An 𝒪 π r n := Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)

abbrev ζb : Pn 𝒪 π r n := Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r)

/--
@isnad1 id=eq.0h4v.s9.22388e4e1ee0 from=translated src=- shape=365be426 vocab=aead0b5d
-/
theorem algebraMap_An_pow_eq_zero : (algebraMap 𝒪 (An 𝒪 π r n) π) ^ (n + 1) = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/--
@isnad1 id=eq.0h4v.s10.37007ad91d40 from=translated src=- shape=64f70985 vocab=0d4e8f57
-/
theorem algebraMap_Pn_pow_eq_zero : (algebraMap 𝒪 (Pn 𝒪 π r n) π) ^ (n + 1) = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/--
@isnad1 id=isnilpot.0h4v.s10.35326c687568 from=translated src=- shape=b4465f04 vocab=616779e3
-/
theorem isNilpotent_algebraMap_Pn : IsNilpotent (algebraMap 𝒪 (Pn 𝒪 π r n) π) :=
  ⟨n + 1, algebraMap_Pn_pow_eq_zero 𝒪 π r n⟩

/--
@isnad1 id=isunit.1h2v.s7.06cbfc212663 from=translated src=- shape=7d1c1082 vocab=5b4b51b5
-/
theorem isUnit_ζ (hr : 1 ≤ r) : IsUnit (chartVRing.ζ 𝒪 r) := by
  have h := chartVRing.isUnit_ζ_pow_sub 𝒪 r
  have hpow : chartVRing.ζ 𝒪 r ^ r = chartVRing.ζ 𝒪 r * chartVRing.ζ 𝒪 r ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hfac : chartVRing.ζ 𝒪 r ^ r - chartVRing.ζ 𝒪 r =
      chartVRing.ζ 𝒪 r * (chartVRing.ζ 𝒪 r ^ (r - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac] at h
  exact isUnit_of_mul_isUnit_left h

/--
@isnad1 id=isunit.0h3v.s9.fc9f5e2aace8 from=translated src=- shape=7c2b8ffa vocab=135c58b9
-/
theorem isUnit_ξ_pow_sub_one : IsUnit (chartERing.ξ 𝒪 π r ^ (r - 1) - 1) :=
  isUnit_of_mul_isUnit_left (chartERing.isUnit_discr 𝒪 π r)

/--
@isnad1 id=isunit.1h4v.s7.801a9d767d61 from=translated src=- shape=494b3fce vocab=4c3ee344
-/
theorem isUnit_ζb (hr : 1 ≤ r) : IsUnit (ζb 𝒪 π r n) := (isUnit_ζ 𝒪 r hr).map _

/--
@isnad1 id=isunit.0h4v.s8.4671ac1f0b07 from=translated src=- shape=118f5b3e vocab=1b8d3f67
-/
theorem isUnit_ζb_pow_sub : IsUnit (ζb 𝒪 π r n ^ r - ζb 𝒪 π r n) := by
  have h := (chartVRing.isUnit_ζ_pow_sub 𝒪 r).map (Ideal.Quotient.mk (IV 𝒪 π r n))
  rwa [map_sub, map_pow] at h

def xV (hr : 1 ≤ r) : (chartVUnit 𝒪 r).obj (Pn 𝒪 π r n) :=
  ⟨ζb 𝒪 π r n, isUnit_ζb_pow_sub 𝒪 π r n, isUnit_ζb 𝒪 π r n hr⟩

def xE (hr : 2 ≤ r) : (chartE 𝒪 π r).obj (Pn 𝒪 π r n) :=
  vertexToEdge π hr (Pn 𝒪 π r n) (isNilpotent_algebraMap_Pn 𝒪 π r n) (xV 𝒪 π r n (le_trans one_le_two hr))

def ι₀ (hr : 2 ≤ r) : chartERing 𝒪 π r →ₐ[𝒪] Pn 𝒪 π r n := chartERing.lift (xE 𝒪 π r n hr)

/--
@isnad1 id=eq.1h4v.s10.f967d84cb59b from=translated src=- shape=f62bb4c0 vocab=6a09539a
-/
theorem ι₀_ξ (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.ξ 𝒪 π r) = ζb 𝒪 π r n := chartERing.lift_ξ _

/--
@isnad1 id=eq.1h4v.s11.0450b5637ac7 from=translated src=- shape=dea3f5e7 vocab=0131dd39
-/
theorem ι₀_η (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.η 𝒪 π r) =
    algebraMap 𝒪 (Pn 𝒪 π r n) π * ↑((isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).unit⁻¹) :=
  chartERing.lift_η _

/--
@isnad1 id=eq.1h4v.s10.9a843b97e2c3 from=translated src=- shape=9bda5410 vocab=9f7fad6f
-/
theorem ι₀_η_mul_ζb (hr : 2 ≤ r) : ι₀ 𝒪 π r n hr (chartERing.η 𝒪 π r) * ζb 𝒪 π r n =
    algebraMap 𝒪 (Pn 𝒪 π r n) π := by
  rw [ι₀_η, mul_assoc]
  have : (↑((isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).unit⁻¹) : Pn 𝒪 π r n) * ζb 𝒪 π r n = 1 :=
    (isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).val_inv_mul
  rw [this, mul_one]

/--
@isnad1 id=eq.2h5v.s10.7f1c5db07154 from=translated src=- shape=502e9d04 vocab=435bb522
-/
theorem ι₀_vanishes (hr : 2 ≤ r) : ∀ a ∈ IE 𝒪 π r n, ι₀ 𝒪 π r n hr a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, AlgHom.commutes, algebraMap_Pn_pow_eq_zero, mul_zero]

def ι (hr : 2 ≤ r) : An 𝒪 π r n →ₐ[𝒪] Pn 𝒪 π r n :=
  Ideal.Quotient.liftₐ (IE 𝒪 π r n) (ι₀ 𝒪 π r n hr) (ι₀_vanishes 𝒪 π r n hr)

/--
@isnad1 id=eq.1h5v.s11.328452524aa6 from=translated src=- shape=fb1201e6 vocab=cc5fd591
-/
theorem ι_mk (hr : 2 ≤ r) (a : chartERing 𝒪 π r) :
    ι 𝒪 π r n hr (Ideal.Quotient.mk _ a) = ι₀ 𝒪 π r n hr a := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=eq.1h4v.s10.d45bf1b7c736 from=translated src=- shape=3f11fd9a vocab=15c095c3
-/
theorem ι_ξb (hr : 2 ≤ r) : ι 𝒪 π r n hr (ξb 𝒪 π r n) = ζb 𝒪 π r n := by
  rw [ξb, ι_mk, ι₀_ξ]

/--
@isnad1 id=eq.1h4v.s10.4f473a42be3d from=translated src=- shape=af237913 vocab=e17dba3e
-/
theorem ι_ηb_mul_ζb (hr : 2 ≤ r) : ι 𝒪 π r n hr (ηb 𝒪 π r n) * ζb 𝒪 π r n = algebraMap 𝒪 (Pn 𝒪 π r n) π := by
  rw [ηb, ι_mk, ι₀_η_mul_ζb]

abbrev L : Type := Localization.Away (ξb 𝒪 π r n)

/--
@isnad1 id=isunit.1h4v.s12.ac590390fc1e from=translated src=- shape=1578eaf0 vocab=3d007cbd
-/
theorem isUnit_pow_sub_algebraMap_ξb (hr : 1 ≤ r) :
    IsUnit ((algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)) ^ r -
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)) := by
  set z := algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) with hz
  have hzU : IsUnit z := IsLocalization.Away.algebraMap_isUnit (ξb 𝒪 π r n)
  have h2 : IsUnit (z ^ (r - 1) - 1) := by
    have h := ((isUnit_ξ_pow_sub_one 𝒪 π r).map (Ideal.Quotient.mk (IE 𝒪 π r n))).map
      (algebraMap (An 𝒪 π r n) (L 𝒪 π r n))
    rwa [map_sub, map_pow, map_one, map_sub, map_pow, map_one] at h
  have hpow : z ^ r = z * z ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hfac : z ^ r - z = z * (z ^ (r - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac]
  exact hzU.mul h2

def g₀ (hr : 1 ≤ r) : chartVRing 𝒪 r →ₐ[𝒪] L 𝒪 π r n :=
  chartVRing.lift ⟨algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n), isUnit_pow_sub_algebraMap_ξb 𝒪 π r n hr⟩

/--
@isnad1 id=eq.1h4v.s12.f9b119e83e61 from=translated src=- shape=e3d9659c vocab=8e314bc9
-/
theorem g₀_ζ (hr : 1 ≤ r) :
    g₀ 𝒪 π r n hr (chartVRing.ζ 𝒪 r) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) :=
  chartVRing.lift_ζ _

/--
@isnad1 id=eq.2h5v.s11.71572ba2ffc5 from=translated src=- shape=728f812e vocab=6fc9eb59
-/
theorem g₀_vanishes (hr : 1 ≤ r) : ∀ a ∈ IV 𝒪 π r n, g₀ 𝒪 π r n hr a = 0 := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  rw [map_mul, map_pow, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n),
    ← map_pow, algebraMap_An_pow_eq_zero, map_zero, mul_zero]

def g (hr : 1 ≤ r) : Pn 𝒪 π r n →ₐ[𝒪] L 𝒪 π r n :=
  Ideal.Quotient.liftₐ (IV 𝒪 π r n) (g₀ 𝒪 π r n hr) (g₀_vanishes 𝒪 π r n hr)

/--
@isnad1 id=eq.1h5v.s12.d91ebe006981 from=translated src=- shape=acf6f9ee vocab=a9fe4a59
-/
theorem g_mk (hr : 1 ≤ r) (a : chartVRing 𝒪 r) :
    g 𝒪 π r n hr (Ideal.Quotient.mk _ a) = g₀ 𝒪 π r n hr a := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=eq.1h4v.s12.bed2a25550f0 from=translated src=- shape=a421d616 vocab=6908e66d
-/
theorem g_ζb (hr : 1 ≤ r) :
    g 𝒪 π r n hr (ζb 𝒪 π r n) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n) := by
  rw [ζb, g_mk, g₀_ζ]

/--
@isnad1 id=isunit.1h4v.s10.9712d795e9ae from=translated src=- shape=e64ed0c9 vocab=42c0f4eb
-/
theorem isUnit_ι_ξb (hr : 2 ≤ r) : IsUnit ((ι 𝒪 π r n hr).toRingHom (ξb 𝒪 π r n)) := by
  show IsUnit (ι 𝒪 π r n hr (ξb 𝒪 π r n))
  rw [ι_ξb]
  exact isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)

def f (hr : 2 ≤ r) : L 𝒪 π r n →+* Pn 𝒪 π r n :=
  IsLocalization.Away.lift (ξb 𝒪 π r n) (isUnit_ι_ξb 𝒪 π r n hr)

/--
@isnad1 id=eq.1h5v.s12.2875a8116a91 from=translated src=- shape=4e1148eb vocab=d0cbef3f
-/
theorem f_algebraMap (hr : 2 ≤ r) (a : An 𝒪 π r n) :
    f 𝒪 π r n hr (algebraMap (An 𝒪 π r n) (L 𝒪 π r n) a) = ι 𝒪 π r n hr a :=
  IsLocalization.Away.lift_eq _ _ a

/--
@isnad1 id=eq.1h4v.s12.a1cd000f9560 from=translated src=- shape=ff6dfe0c vocab=e64d0f39
-/
theorem g_comp_ι (hr : 2 ≤ r) :
    (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom.comp (ι 𝒪 π r n hr).toRingHom =
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) := by
  apply Ideal.Quotient.ringHom_ext
  apply ringHom_ext_E 𝒪 π r
  · ext x
    show g 𝒪 π r n _ (ι 𝒪 π r n hr (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartERing 𝒪 π r) x))) =
      algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartERing 𝒪 π r) x))
    rw [Ideal.Quotient.mk_algebraMap, AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n)]
  · show g 𝒪 π r n _ (ι 𝒪 π r n hr (ξb 𝒪 π r n)) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ξb 𝒪 π r n)
    rw [ι_ξb, g_ζb]
  · show g 𝒪 π r n _ (ι 𝒪 π r n hr (ηb 𝒪 π r n)) = algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ηb 𝒪 π r n)

    have hU : IsUnit (g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n)) :=
      (isUnit_ζb 𝒪 π r n (le_trans one_le_two hr)).map _
    have h1 : g 𝒪 π r n (le_trans one_le_two hr) (ι 𝒪 π r n hr (ηb 𝒪 π r n)) *
        g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n) = algebraMap 𝒪 (L 𝒪 π r n) π := by
      rw [← map_mul, ι_ηb_mul_ζb, AlgHom.commutes]
    have h2 : algebraMap (An 𝒪 π r n) (L 𝒪 π r n) (ηb 𝒪 π r n) *
        g 𝒪 π r n (le_trans one_le_two hr) (ζb 𝒪 π r n) = algebraMap 𝒪 (L 𝒪 π r n) π := by
      rw [g_ζb, ← map_mul]
      have : ηb 𝒪 π r n * ξb 𝒪 π r n = algebraMap 𝒪 (An 𝒪 π r n) π := by
        rw [ηb, ξb, ← map_mul, mul_comm, chartERing.ξ_mul_η, Ideal.Quotient.mk_algebraMap]
      rw [this, ← IsScalarTower.algebraMap_apply]
    exact (IsUnit.mul_left_injective hU) (h1.trans h2.symm)

/--
@isnad1 id=eq.1h4v.s11.2db77614356e from=translated src=- shape=71256d36 vocab=f0bf7e6b
-/
theorem g_comp_f (hr : 2 ≤ r) :
    (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom.comp (f 𝒪 π r n hr) = RingHom.id (L 𝒪 π r n) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (ξb 𝒪 π r n))
  rw [RingHom.comp_assoc, f, IsLocalization.Away.lift_comp, RingHom.id_comp]
  exact g_comp_ι 𝒪 π r n hr

/--
@isnad1 id=eq.1h4v.s11.3d76861e257e from=translated src=- shape=d50e759c vocab=f0bf7e6b
-/
theorem f_comp_g (hr : 2 ≤ r) :
    (f 𝒪 π r n hr).comp (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom = RingHom.id (Pn 𝒪 π r n) := by
  apply Ideal.Quotient.ringHom_ext
  apply ringHom_ext_V 𝒪 r
  · ext x
    show f 𝒪 π r n hr (g 𝒪 π r n _ (Ideal.Quotient.mk _ (algebraMap 𝒪 (chartVRing 𝒪 r) x))) =
      Ideal.Quotient.mk _ (algebraMap 𝒪 (chartVRing 𝒪 r) x)
    rw [Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
      IsScalarTower.algebraMap_apply 𝒪 (An 𝒪 π r n) (L 𝒪 π r n), f_algebraMap, AlgHom.commutes]
  · show f 𝒪 π r n hr (g 𝒪 π r n _ (ζb 𝒪 π r n)) = ζb 𝒪 π r n
    rw [g_ζb, f_algebraMap, ι_ξb]

def e (hr : 2 ≤ r) : L 𝒪 π r n ≃+* Pn 𝒪 π r n :=
  RingEquiv.ofRingHom (f 𝒪 π r n hr) (g 𝒪 π r n (le_trans one_le_two hr)).toRingHom
    (f_comp_g 𝒪 π r n hr) (g_comp_f 𝒪 π r n hr)

/--
@isnad1 id=away.1h4v.s10.61c5ec887ff9 from=translated src=- shape=7c6a1820 vocab=239e3152
-/
theorem isLocalization_away (hr : 2 ≤ r) :
    @IsLocalization.Away (An 𝒪 π r n) _ (ξb 𝒪 π r n) (Pn 𝒪 π r n) _ (ι 𝒪 π r n hr).toRingHom.toAlgebra := by
  letI : Algebra (An 𝒪 π r n) (Pn 𝒪 π r n) := (ι 𝒪 π r n hr).toRingHom.toAlgebra
  let e' : L 𝒪 π r n ≃ₐ[An 𝒪 π r n] Pn 𝒪 π r n :=
    AlgEquiv.ofRingEquiv (f := e 𝒪 π r n hr) (fun a => f_algebraMap 𝒪 π r n hr a)
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (ξb 𝒪 π r n)) e'

end

end VertexInEdgeAux

open VertexInEdgeAux in
/--
@isnad1 id=ex.0h4v.s16.187fd35d6ac6 from=translated src=- shape=342f489c vocab=409e98f8
-/
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) {r : ℕ} [Fact r.Prime] (n : ℕ) :
    ∃ ι : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}),
      ι (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) = Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) ∧
      ι (Ideal.Quotient.mk _ (chartERing.η 𝒪 π r)) * Ideal.Quotient.mk _ (chartVRing.ζ 𝒪 r) = algebraMap 𝒪 (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) π ∧
      @IsLocalization.Away ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (Ideal.Quotient.mk _ (chartERing.ξ 𝒪 π r)) (chartVRing 𝒪 r ⧸ Ideal.span {(algebraMap 𝒪 (chartVRing 𝒪 r) π) ^ (n + 1)}) _ ι.toRingHom.toAlgebra := by
  have hr : 2 ≤ r := (Fact.out : r.Prime).two_le
  exact ⟨VertexInEdgeAux.ι 𝒪 π r n hr, ι_ξb 𝒪 π r n hr, ι_ηb_mul_ζb 𝒪 π r n hr, isLocalization_away 𝒪 π r n hr⟩
