import Tengoku.NsP23.P23.OneTie.RhoFourMixed
import Tengoku.NsP23.P23.OneTie.H5Cover
import Tengoku.NsP23.P23.Artin.ThreeBorderSymmetry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exhaustive support-pattern reduction of the mixed three-border case. -/
namespace P23.OneTie
noncomputable section
open P23.Presentation P23.Artin
variable {a b c : ℕ} [NeZero a]
set_option maxHeartbeats 1200000

theorem mixed_three_border_support_classification (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : 0 < c)
    (ht : quotientType ℚ S hS hd hl = 3) (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q) :
    Nonempty (MixedThreeBorderData S) ∨
      Nonempty (MixedThreeBorderData (swapYZFinset S)) := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  obtain ⟨B,hB,hY⟩ := mixed_pure_y_border_exists S hS hd hc
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  have hYZ : (yAxis B : Normal a b c) ≠ zAxis C := by
    intro he; have := congrArg Normal.y he; simp [yAxis,zAxis] at this; omega
  obtain ⟨q,hq,hqY,hqZ,he⟩ := three_border_exists_third S hcard (yAxis B) (zAxis C) hY hZ hYZ
  have hqy : q.y < B := by
    by_contra hn
    have hdq : yAxis B ∣ q := (Normal.exact_divides_iff _ _).mpr
      (by simp [Normal.DividesCriterion,yAxis]; omega)
    exact hqY (border_dvd_border_eq hS hd.1 hY hq hdq).symm
  have hqz : q.z < C := by
    by_contra hn
    have hdq : zAxis C ∣ q := (Normal.exact_divides_iff _ _).mpr
      (by simp [Normal.DividesCriterion,zAxis]; omega)
    exact hqZ (border_dvd_border_eq hS hd.1 hZ hq hdq).symm
  have hx : 0 < q.x := by
    by_contra hn
    have hx0 : q.x = 0 := by omega
    have hy : 0 < q.y := by
      by_contra hy
      have hy0 : q.y = 0 := by omega
      have hqe : q = zAxis q.z := by apply Normal.ext <;> simp [zAxis,hx0,hy0]
      have hzC := pure_z_border_unique hS hd.1 (hqe ▸ hq) hZ
      exact hqZ (hqe.trans (congrArg zAxis hzC))
    have hz : 0 < q.z := by
      by_contra hz
      have hz0 : q.z = 0 := by omega
      have hqe : q = yAxis q.y := by apply Normal.ext <;> simp [yAxis,hx0,hz0]
      have hyB := pure_y_border_unique hS hd.1 (hqe ▸ hq) hY
      exact hqY (hqe.trans (congrArg yAxis hyB))
    have hqe : q = yzPoint q.y q.z := by apply Normal.ext <;> simp [yzPoint,hx0]
    have he' : borderFinset S = {yAxis B,zAxis C,yzPoint q.y q.z} := by
      rw [he,hqe]
      rfl
    have htt := mixed_three_border_no_x_type_le_two S hS hd hl ha B C q.y q.z
      hy hqy hz hqz he'
    omega
  have hnp := border_not_pure_x hS hl hq
  have hn := hnf q hq
  unfold NormalHasFullSupport at hn
  by_cases hy0 : q.y = 0
  · have hz : 0 < q.z := by unfold NormalIsPureX at hnp; omega
    left
    refine ⟨⟨B,C,q.x,q.z,hb,hc,hB,hx,q.x_lt,hz,hqz,?_⟩⟩
    have hqe : q = (⟨q.x,0,q.z,q.x_lt⟩ : Normal a b c) := by
      apply Normal.ext <;> simp [hy0]
    rw [he,hqe]
  · have hz0 : q.z = 0 := by omega
    have hy : 0 < q.y := by omega
    right
    refine ⟨⟨C,B,q.x,q.y,hc,hb,hC,hx,q.x_lt,hy,hqy,?_⟩⟩
    rw [borderFinset_swapYZ_exact,he,swapYZFinset_triple]
    ext p
    simp [swapYZ,yAxis,zAxis,hz0]
    tauto
theorem rho_four_mixed_canonical_impossible (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : 0 < c)
    (ht : quotientType ℚ S hS hd hl = 3) (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q)
    (hn : QuotientNearlyGorenstein ℚ S hS hd hl) : False := by
  rcases mixed_three_border_support_classification S hS hd hl ha hc ht hcard hnf with
    hM | hM
  · obtain ⟨M⟩ := hM
    exact mixed_three_border_not_nearlyGorenstein M hS hd hl ha ht hn
  · obtain ⟨M⟩ := hM
    have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
    have hd' : IsLiveParameterDomain a c b := ⟨hd.1,Or.inl ⟨by omega,by omega⟩⟩
    have hS' : (swapYZFinset S).Nonempty := by
      obtain ⟨s,hs⟩ := hS
      exact ⟨swapYZ s,Finset.mem_map.mpr ⟨s,hs,rfl⟩⟩
    have hl' := swapYZIsLiveTie S hd hl
    have ha' := swapYZIsRootAntichain S ha
    have ht' : quotientType ℚ (swapYZFinset S) hS' hd' hl' = 3 := by
      rw [quotientType_eq_rootCard _ _ _ _ ha',swapYZFinset,Finset.card_map]
      exact (quotientType_eq_three_iff S hS hd hl ha).mp ht
    have hn' := (quotientNearlyGorenstein_iff_directNearlyGorenstein S hS hd hl).mp hn
    have htr := (directNearlyGorenstein_iff_variablesInTrace S hS hd hl).mp hn'
    have htr' := swapYZVariablesInTrace S hd hl hl' htr
    exact mixed_three_border_z_not_trace M hS' hd' hl' ha' ht' htr'.2.2
end
end P23.OneTie
