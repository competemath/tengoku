import Tengoku.NsP23.P23.OneTie.RhoFourPureGeometry
import Tengoku.NsP23.P23.Artin.ThreeBorderTraceTools
import Tengoku.NsP23.P23.Presentation.QuotientDualTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Pure three-border endpoint forcing by actual canonical-dual coefficients. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
set_option maxHeartbeats 1200000
variable {a b : ℕ} [NeZero a] {k : Type*} [Field k]

namespace PureThreeBorderData
variable {S : Finset (Normal a b 0)} (P : PureThreeBorderData S)

/--
@isnad1 id=mem.4h4v.s6.d36b5ef5a3af from=translated src=- shape=8a7c7fad vocab=69c7741f
-/
theorem xRoot_mem (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (ha : IsRootAntichain S) (huv : P.u < P.v) : P.xRoot ∈ S :=
  Eq.mp (congrArg (fun T => P.xRoot ∈ T) (pure_three_border_roots_exact P hS hd ha huv).symm)
    (by simp [threeRoots])
/--
@isnad1 id=mem.4h4v.s6.e2b378c89cb7 from=translated src=- shape=8a7c7fad vocab=5ced0ce4
-/
theorem yRoot_mem (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (ha : IsRootAntichain S) (huv : P.u < P.v) : P.yRoot ∈ S :=
  Eq.mp (congrArg (fun T => P.yRoot ∈ T) (pure_three_border_roots_exact P hS hd ha huv).symm)
    (by simp [threeRoots])
/--
@isnad1 id=mem.4h4v.s6.f00884bed38d from=translated src=- shape=8a7c7fad vocab=ce4f2a96
-/
theorem zRoot_mem (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (ha : IsRootAntichain S) (huv : P.u < P.v) : P.zRoot ∈ S :=
  Eq.mp (congrArg (fun T => P.zRoot ∈ T) (pure_three_border_roots_exact P hS hd ha huv).symm)
    (by simp [threeRoots])

/--
@isnad1 id=and.2h4v.s8.54bc1e7fa6c4 from=translated src=- shape=fb0885da vocab=05a81b1d
-/
theorem annihilator_scalars_survive (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) :
    (yAxis P.u : Normal a b 0) ∈ standardFinset S ∧
    (yAxis P.v : Normal a b 0) ∈ standardFinset S ∧
    (zAxis P.w : Normal a b 0) ∈ standardFinset S := by
  have hb := P.b_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hvu := P.v_lt
  have hr := P.r_pos
  have hw := P.w_pos
  have hwC := P.w_lt
  constructor
  · rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [yAxis]
    omega
  · constructor
    · rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
      simp [yAxis]
      omega
    · rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
      simp [zAxis]
      omega

/--
@isnad1 id=eq.8h8v.s11.ca0ba16934e0 from=translated src=- shape=3358cc35 vocab=7186348c
-/
theorem root_coeff_zero_of_annihilator_products (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b 0) (ha : IsRootAntichain S) (huv : P.u < P.v)
    (e : MonomialIndex S)
    (hyu : yAxis P.u * e.1 ∈ standardFinset S)
    (hyv : yAxis P.v * e.1 ∈ standardFinset S)
    (hzw : zAxis P.w * e.1 ∈ standardFinset S)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b 0) (hs : s ∈ S) :
    coeffAt (k := k) S e (F (U (k := k) S (rootIndex S s hs))) = 0 := by
  have hu := P.u_pos
  have hv := P.v_pos
  have hw := P.w_pos
  obtain ⟨huS,hvS,hwS⟩ := P.annihilator_scalars_survive hS hd
  have he := pure_three_border_roots_exact P hS hd ha huv
  have hs' : s = P.xRoot ∨ s = P.yRoot ∨ s = P.zRoot := by
    simpa [he,threeRoots] using hs
  rcases hs' with rfl | rfl | rfl
  · apply root_coeff_zero_of_nondvd_and_surviving_product S F P.xRoot hs ⟨yAxis P.u,huS⟩ e _ hyu
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,yAxis,xRoot]
    omega
  · apply root_coeff_zero_of_nondvd_and_surviving_product S F P.yRoot hs ⟨yAxis P.v,hvS⟩ e _ hyv
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,yAxis,yRoot]
    omega
  · apply root_coeff_zero_of_nondvd_and_surviving_product S F P.zRoot hs ⟨zAxis P.w,hwS⟩ e _ hzw
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,zAxis,zRoot]
    omega
end PureThreeBorderData

/--
@isnad1 id=eq.5h5v.s9.90f625287b8b from=translated src=- shape=fab9eafe vocab=ce9166a3
-/
theorem pure_three_border_x_trace_forces_r_one {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hxtrace : let hxS := (mem_standardFinset_iff_standardSet S Normal.xGenerator).mpr hl.1
      X (k := ℚ) S Normal.xGenerator hxS ∈ TraceSubmodule ℚ S) : P.r = 1 := by
  have huv := (pure_three_border_type_three_iff P hS hd hl ha).mp ht
  have hr := P.r_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hvb := P.v_lt
  have hb := P.b_pos
  have hw := P.w_pos
  have hwC := P.w_lt
  have ha1 : a ≠ 1 := by have := hd.1; omega
  have hdiv : 1 / a = 0 := Nat.div_eq_of_lt (by have := hd.1; omega)
  have hmod : 1 % a = 1 := Nat.mod_eq_of_lt (by have := hd.1; omega)
  by_contra hn
  have hr2 : 1 < P.r := by omega
  let ei : MonomialIndex S := ⟨Normal.xGenerator,
    (mem_standardFinset_iff_standardSet S _).mpr hl.1⟩
  have hyu : yAxis P.u * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,yAxis,Normal.xGenerator,ha1,hdiv,hmod]
    omega
  have hyv : yAxis P.v * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,yAxis,Normal.xGenerator,ha1,hdiv,hmod]
    omega
  have hzw : zAxis P.w * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,zAxis,Normal.xGenerator,ha1,hdiv,hmod]
    omega
  have hcard : S.card = 3 := (quotientType_eq_three_iff S hS hd hl ha).mp ht
  obtain ⟨F,s,hs,hcoeff⟩ := exists_root_image_with_variable_coeff_of_mem_trace S hS
    (by omega) ha hd .x _ hxtrace
  exact hcoeff (P.root_coeff_zero_of_annihilator_products hS hd ha huv ei hyu hyv hzw F s hs)

/--
@isnad1 id=eq.5h5v.s9.11830c4d175e from=translated src=- shape=1085ba1d vocab=533e2356
-/
theorem pure_three_border_y_trace_forces_v_endpoint {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hytrace : let hyS := (mem_standardFinset_iff_standardSet S Normal.yGenerator).mpr hl.2.1
      X (k := ℚ) S Normal.yGenerator hyS ∈ TraceSubmodule ℚ S) : P.v = P.u+b-1 := by
  have huv := (pure_three_border_type_three_iff P hS hd hl ha).mp ht
  have hr := P.r_pos
  have hu := P.u_pos
  have hv := P.v_pos
  have hvb := P.v_lt
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  have hw := P.w_pos
  have hwC := P.w_lt
  by_contra hn
  have hv1 : P.v+1 < P.u+b := by omega
  let ei : MonomialIndex S := ⟨Normal.yGenerator,
    (mem_standardFinset_iff_standardSet S _).mpr hl.2.1⟩
  have hyu : yAxis P.u * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,yAxis,Normal.yGenerator]
    omega
  have hyv : yAxis P.v * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,yAxis,Normal.yGenerator]
    omega
  have hzw : zAxis P.w * ei.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [ei,zAxis,Normal.yGenerator]
    omega
  have hcard : S.card = 3 := (quotientType_eq_three_iff S hS hd hl ha).mp ht
  obtain ⟨F,s,hs,hcoeff⟩ := exists_root_image_with_variable_coeff_of_mem_trace S hS
    (by omega) ha hd .y _ hytrace
  exact hcoeff (P.root_coeff_zero_of_annihilator_products hS hd ha huv ei hyu hyv hzw F s hs)
/--
@isnad1 id=eq.7h5v.s9.765370ceba36 from=translated src=- shape=4f829131 vocab=4c052f37
-/
theorem pure_three_border_z_trace_forces_w_endpoint {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hr : P.r = 1) (hv : P.v = P.u+b-1)
    (hztrace : let hzS := (mem_standardFinset_iff_standardSet S Normal.zGenerator).mpr hl.2.2.1
      X (k := ℚ) S Normal.zGenerator hzS ∈ TraceSubmodule ℚ S) : P.w = P.C-1 := by
  have huv := (pure_three_border_type_three_iff P hS hd hl ha).mp ht
  have hu := P.u_pos
  have hw := P.w_pos
  have hwC := P.w_lt
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  have ha2 := hd.1
  have ha1 : a ≠ 1 := by omega
  have ham : a-1 < a := by omega
  have hra : P.r < a := P.r_lt
  have hdiv : 1 / a = 0 := Nat.div_eq_of_lt (by omega)
  have hmod : 1 % a = 1 := Nat.mod_eq_of_lt (by omega)
  by_contra hn
  have hw1 : P.w+1 < P.C := by omega
  let xi : MonomialIndex S := ⟨Normal.xGenerator,(mem_standardFinset_iff_standardSet S _).mpr hl.1⟩
  let yi : MonomialIndex S := ⟨Normal.yGenerator,(mem_standardFinset_iff_standardSet S _).mpr hl.2.1⟩
  let zi : MonomialIndex S := ⟨Normal.zGenerator,(mem_standardFinset_iff_standardSet S _).mpr hl.2.2.1⟩
  obtain ⟨huS,hvS,hwS⟩ := P.annihilator_scalars_survive hS hd
  let yu : MonomialIndex S := ⟨yAxis P.u,huS⟩
  let zw : MonomialIndex S := ⟨zAxis P.w,hwS⟩
  have hyuz : yu.1 * zi.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [yu,zi,yAxis,Normal.zGenerator]
    omega
  have hzwz : zw.1 * zi.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [zw,zi,zAxis,Normal.zGenerator]
    omega
  have hxz : xi.1 * zi.1 ∈ standardFinset S := by
    rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
    simp [xi,zi,Normal.xGenerator,Normal.zGenerator,ha1,hdiv,hmod]
    omega
  let xzi : MonomialIndex S := ⟨xi.1 * zi.1,hxz⟩
  have hxmem := P.xRoot_mem hS hd ha huv
  have hymem := P.yRoot_mem hS hd ha huv
  let Ui := rootIndex S P.xRoot hxmem
  let Vi := rootIndex S P.yRoot hymem
  have hrel : X (k := ℚ) S yi.1 yi.2 • U (k := ℚ) S Ui =
      X (k := ℚ) S xi.1 xi.2 • U (k := ℚ) S Vi := by
    by_cases hu1 : P.u = 1
    · have hynd : ¬yi.1 ∣ P.xRoot := by
        simp [Normal.exact_divides_iff,Normal.DividesCriterion,yi,Normal.yGenerator,
          PureThreeBorderData.xRoot,hu1]
      have hxnd : ¬xi.1 ∣ P.yRoot := by
        simp [Normal.exact_divides_iff,Normal.DividesCriterion,xi,Normal.xGenerator,
          PureThreeBorderData.yRoot,hr,hu1,ha1,hdiv,hmod]
        omega
      rw [(X_smul_rootDual_eq_zero_iff S P.xRoot hxmem yi).mpr hynd,
        (X_smul_rootDual_eq_zero_iff S P.yRoot hymem xi).mpr hxnd]
    · let q : Normal a b 0 := ⟨a-1,P.u-2,P.C-1,by omega⟩
      have hqS : q ∈ standardFinset S := by
        rw [mem_standardFinset_iff_standardSet,pure_three_border_standard_slices P hS hd]
        simp [q]
        omega
      apply dual_relation_of_common_quotient S yi xi ⟨q,hqS⟩ Ui Vi
      · apply Normal.ext <;> simp [yi,q,Ui,rootIndex,Normal.yGenerator,
          PureThreeBorderData.xRoot,Nat.div_eq_of_lt ham,Nat.mod_eq_of_lt ham] <;> omega
      · have hsum : 1 + (a-1) = a := by omega
        apply Normal.ext <;>
          simp [xi,q,Vi,rootIndex,Normal.xGenerator,PureThreeBorderData.yRoot,
            Normal.mul,Normal.raw,Normal.normalize,ha1,hdiv,hmod,hsum,hr,
            Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne a))] <;> omega
  have hcard : S.card = 3 := (quotientType_eq_three_iff S hS hd hl ha).mp ht
  obtain ⟨F,s,hs,hcoeff⟩ := exists_root_image_with_variable_coeff_of_mem_trace S hS
    (by omega) ha hd .z _ hztrace
  have he := pure_three_border_roots_exact P hS hd ha huv
  have hs' : s = P.xRoot ∨ s = P.yRoot ∨ s = P.zRoot := by
    simpa [he,PureThreeBorderData.threeRoots] using hs
  rcases hs' with rfl | rfl | rfl
  · apply hcoeff
    apply root_coeff_zero_of_nondvd_and_surviving_product S F P.xRoot hs yu zi _ hyuz
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,yu,yAxis,PureThreeBorderData.xRoot]
    omega
  · apply hcoeff
    have hmap : X (k := ℚ) S yi.1 yi.2 * F (U (k := ℚ) S Ui) =
        X (k := ℚ) S xi.1 xi.2 * F (U (k := ℚ) S Vi) := by
      simpa [smul_eq_mul] using congrArg F hrel
    have hh := congrArg (coeffAt (k := ℚ) S xzi) hmap
    rw [coeffAt_X_mul S xi zi xzi rfl] at hh
    have hny : ¬yi.1 ∣ xzi.1 := by
      simp [Normal.exact_divides_iff,Normal.DividesCriterion,yi,xzi,xi,zi,
        Normal.yGenerator,Normal.xGenerator,Normal.zGenerator,ha1,hdiv,hmod]
    rw [coeffAt_X_mul_eq_zero_of_not_dvd S yi xzi hny] at hh
    exact hh.symm
  · apply hcoeff
    apply root_coeff_zero_of_nondvd_and_surviving_product S F P.zRoot hs zw zi _ hzwz
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,zw,zAxis,PureThreeBorderData.zRoot]
    omega

/--
@isnad1 id=and.6h4v.s7.820608ba144f from=translated src=- shape=397291b3 vocab=567cd3a3
-/
theorem pure_three_border_ng_forces_endpoints {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) :
    P.r = 1 ∧ P.v = P.u+b-1 ∧ P.w = P.C-1 := by
  have hn' := (quotientNearlyGorenstein_iff_directNearlyGorenstein S hS hd hl).mp hn
  have htr := (directNearlyGorenstein_iff_variablesInTrace S hS hd hl).mp hn'
  have hr := pure_three_border_x_trace_forces_r_one P hS hd hl ha ht htr.1
  have hv := pure_three_border_y_trace_forces_v_endpoint P hS hd hl ha ht htr.2.1
  exact ⟨hr,hv,pure_three_border_z_trace_forces_w_endpoint P hS hd hl ha ht hr hv htr.2.2⟩
end
end P23.OneTie
