import Tengoku.NsP23.P23.OneTie.RhoFourMixedGeometry
import Tengoku.NsP23.P23.Artin.ThreeBorderTraceTools
import Tengoku.NsP23.P23.Presentation.QuotientDualTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Mixed three-border canonical-dual coefficient obstruction, including
the gap-one endpoint. No coefficient matrix or bounded search is used. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
set_option maxHeartbeats 1200000
variable {a b c : ℕ} [NeZero a] {k : Type*} [Field k]

theorem mixed_three_border_z_coeff_zero {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hl : IsLiveTie S) (hanti : IsRootAntichain S) (hbB : b < M.B) (hcvC : c+M.v < M.C)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S) :
    let hzS := (mem_standardFinset_iff_standardSet S Normal.zGenerator).mpr hl.2.2.1
    coeffAt (k := k) S ⟨Normal.zGenerator,hzS⟩ (F (U (k := k) S (rootIndex S s hs))) = 0 := by
  classical
  dsimp only
  have hr := M.r_pos
  have hra := M.r_lt
  have hb := M.b_pos
  have hc := M.c_pos
  have hB := M.B_pos
  have hv := M.v_pos
  have hvC := M.v_lt
  have hrl : M.r-1 < a := by omega
  have hBB : M.B-b < M.B := by omega
  let gap := M.C-c-M.v
  have hgap : 0 < gap := by dsimp [gap]; omega
  have hgapC : gap < M.C := by dsimp [gap]; omega
  let yb : Normal a b c := yAxis b
  let xr : Normal a b c := ⟨M.r,0,0,hra⟩
  let zv : Normal a b c := zAxis M.v
  let zd : Normal a b c := zAxis gap
  let ye : Normal a b c := yAxis (M.B-b)
  let yz : Normal a b c := ⟨0,b,1,by omega⟩
  let zz : Normal a b c := zAxis (M.v+1)
  let xy : Normal a b c := ⟨M.r,M.B-b,0,hra⟩
  let yz' : Normal a b c := ⟨0,M.B-b,1,by omega⟩
  let q : Normal a b c := ⟨M.r-1,b-1,c+M.v-1,hrl⟩
  have surv (p : Normal a b c) (hp : p.y < M.B ∧ p.z < M.C ∧
      ((p.x < M.r ∧ (p.y < b ∨ p.z < c+M.v)) ∨ (M.r ≤ p.x ∧ p.z < M.v))) :
      p ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S p).mpr ((mixed_three_border_standard_slices M hS hd p).mpr hp)
  have hyb := surv yb (by dsimp [yb,yAxis]; omega)
  have hxr := surv xr (by dsimp [xr]; omega)
  have hzv := surv zv (by dsimp [zv,zAxis]; omega)
  have hzd := surv zd (by dsimp [zd,zAxis]; omega)
  have hye := surv ye (by dsimp [ye,yAxis]; omega)
  have hyz := surv yz (by dsimp [yz]; omega)
  have hzz := surv zz (by dsimp [zz,zAxis]; omega)
  have hxy := surv xy (by dsimp [xy]; omega)
  have hyz' := surv yz' (by dsimp [yz']; omega)
  have hq := surv q (by dsimp [q]; omega)
  let zi : MonomialIndex S := ⟨Normal.zGenerator,
    (mem_standardFinset_iff_standardSet S _).mpr hl.2.2.1⟩
  let ybi : MonomialIndex S := ⟨yb,hyb⟩
  let xri : MonomialIndex S := ⟨xr,hxr⟩
  let zvi : MonomialIndex S := ⟨zv,hzv⟩
  let zdi : MonomialIndex S := ⟨zd,hzd⟩
  let yei : MonomialIndex S := ⟨ye,hye⟩
  let yzi : MonomialIndex S := ⟨yz,hyz⟩
  let zzi : MonomialIndex S := ⟨zz,hzz⟩
  let xyi : MonomialIndex S := ⟨xy,hxy⟩
  let yz'i : MonomialIndex S := ⟨yz',hyz'⟩
  let qi : MonomialIndex S := ⟨q,hq⟩
  have he := mixed_three_border_roots_exact M hS hd hanti hbB hcvC
  have hU : M.yCornerRoot ∈ S := Eq.mp (congrArg (fun T => M.yCornerRoot ∈ T) he.symm)
    (show M.yCornerRoot ∈ M.threeRoots from by simp [MixedThreeBorderData.threeRoots])
  have hV : M.zCornerRoot ∈ S := Eq.mp (congrArg (fun T => M.zCornerRoot ∈ T) he.symm)
    (show M.zCornerRoot ∈ M.threeRoots from by simp [MixedThreeBorderData.threeRoots])
  have hW : M.highRoot ∈ S := Eq.mp (congrArg (fun T => M.highRoot ∈ T) he.symm)
    (show M.highRoot ∈ M.threeRoots from by simp [MixedThreeBorderData.threeRoots])
  let Ui := rootIndex S M.yCornerRoot hU
  let Vi := rootIndex S M.zCornerRoot hV
  let Wi := rootIndex S M.highRoot hW
  have hUy : X (k := k) S yb hyb • U (k := k) S Ui = 0 := by
    apply (X_smul_rootDual_eq_zero_iff S M.yCornerRoot hU ybi).mpr
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,ybi,yb,yAxis,
      MixedThreeBorderData.yCornerRoot]
    omega
  have hUx : X (k := k) S xr hxr • U (k := k) S Ui = 0 := by
    apply (X_smul_rootDual_eq_zero_iff S M.yCornerRoot hU xri).mpr
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,xri,xr,
      MixedThreeBorderData.yCornerRoot]
    omega
  have hWz : X (k := k) S zv hzv • U (k := k) S Wi = 0 := by
    apply (X_smul_rootDual_eq_zero_iff S M.highRoot hW zvi).mpr
    simp [Normal.exact_divides_iff,Normal.DividesCriterion,zvi,zv,zAxis,
      MixedThreeBorderData.highRoot]
    omega
  have hrel : X (k := k) S zd hzd • U (k := k) S Ui =
      X (k := k) S ye hye • U (k := k) S Vi := by
    apply dual_relation_of_common_quotient S zdi yei qi Ui Vi
    · apply Normal.ext <;> simp [zdi,qi,Ui,rootIndex,zd,zAxis,q,
        MixedThreeBorderData.yCornerRoot,Normal.mul,Normal.raw,Normal.normalize,
        Nat.mod_eq_of_lt hrl,Nat.div_eq_of_lt hrl] <;> dsimp [gap] <;> omega
    · apply Normal.ext <;> simp [yei,qi,Vi,rootIndex,ye,yAxis,q,
        MixedThreeBorderData.zCornerRoot,Normal.mul,Normal.raw,Normal.normalize,
        Nat.mod_eq_of_lt hrl,Nat.div_eq_of_lt hrl] <;> omega
  have hUz : coeffAt (k := k) S zi (F (U (k := k) S Ui)) = 0 := by
    apply coeff_eq_zero_of_annihilator S F ybi zi yzi Ui hUy
    apply Normal.ext <;> simp [ybi,zi,yzi,yb,yAxis,yz,Normal.zGenerator]
  have hWzcoeff : coeffAt (k := k) S zi (F (U (k := k) S Wi)) = 0 := by
    apply coeff_eq_zero_of_annihilator S F zvi zi zzi Wi hWz
    apply Normal.ext <;> simp [zvi,zi,zzi,zv,zAxis,zz,Normal.zGenerator]
  have hVcoeff : coeffAt (k := k) S zi (F (U (k := k) S Vi)) = 0 := by
    have hmap : X (k := k) S zd hzd * F (U (k := k) S Ui) =
        X (k := k) S ye hye * F (U (k := k) S Vi) := by
      simpa [smul_eq_mul] using congrArg F hrel
    have hh := congrArg (coeffAt (k := k) S yz'i) hmap
    have hp : yei.1 * zi.1 = yz'i.1 := by
      apply Normal.ext <;> simp [yei,zi,yz'i,ye,yAxis,yz',Normal.zGenerator]
    rw [coeffAt_X_mul S yei zi yz'i hp] at hh
    by_cases hg : gap = 1
    · have hp' : zdi.1 * yei.1 = yz'i.1 := by
        apply Normal.ext <;> simp [zdi,yei,yz'i,zd,zAxis,ye,yAxis,yz',hg]
      rw [coeffAt_X_mul S zdi yei yz'i hp'] at hh
      have hvan : coeffAt (k := k) S yei (F (U (k := k) S Ui)) = 0 := by
        apply coeff_eq_zero_of_annihilator S F xri yei xyi Ui hUx
        apply Normal.ext <;> simp [xri,yei,xyi,xr,ye,yAxis,xy,Normal.mul,
          Normal.raw,Normal.normalize,Nat.mod_eq_of_lt hra,Nat.div_eq_of_lt hra]
      exact hh.symm.trans hvan
    · have hnodiv : ¬zdi.1 ∣ yz'i.1 := by
        simp [Normal.exact_divides_iff,Normal.DividesCriterion,zdi,yz'i,zd,zAxis,yz']
        omega
      rw [coeffAt_X_mul_eq_zero_of_not_dvd S zdi yz'i hnodiv] at hh
      exact hh.symm
  have hs' : s = M.highRoot ∨ s = M.yCornerRoot ∨ s = M.zCornerRoot := by
    simpa [he,MixedThreeBorderData.threeRoots] using hs
  rcases hs' with rfl | rfl | rfl
  · exact hWzcoeff
  · exact hUz
  · exact hVcoeff

theorem mixed_three_border_z_not_trace {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hl : IsLiveTie S) (hanti : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3) :
    let hzS := (mem_standardFinset_iff_standardSet S Normal.zGenerator).mpr hl.2.2.1
    X (k := ℚ) S Normal.zGenerator hzS ∉ TraceSubmodule ℚ S := by
  dsimp only
  intro htrace
  obtain ⟨hb,hc⟩ := (mixed_three_border_type_three_iff M hS hd hl hanti).mp ht
  have hcard : S.card = 3 := (quotientType_eq_three_iff S hS hd hl hanti).mp ht
  obtain ⟨F,s,hs,hcoeff⟩ := exists_root_image_with_variable_coeff_of_mem_trace S hS
    (by omega) hanti hd .z _ htrace
  exact hcoeff (mixed_three_border_z_coeff_zero M hS hd hl hanti hb hc F s hs)
theorem mixed_three_border_not_nearlyGorenstein {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hl : IsLiveTie S) (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3) :
    ¬QuotientNearlyGorenstein ℚ S hS hd hl := by
  intro hn
  have hn' := (quotientNearlyGorenstein_iff_directNearlyGorenstein S hS hd hl).mp hn
  have htr := (directNearlyGorenstein_iff_variablesInTrace S hS hd hl).mp hn'
  exact mixed_three_border_z_not_trace M hS hd hl ha ht htr.2.2
end
end P23.OneTie
