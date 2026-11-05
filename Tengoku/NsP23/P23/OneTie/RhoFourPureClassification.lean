import Tengoku.NsP23.P23.OneTie.RhoFourPureEliminations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exhaustion of pure three-border support patterns before trace. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a]
set_option maxHeartbeats 1600000

/--
@isnad1 id=not.7h4v.s8.a2830872186c from=translated src=- shape=c6664acc vocab=51a82855
-/
theorem pure_three_border_no_y_axis (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q) :
    ∀ B, yAxis B ∉ borderFinset S := by
  intro B hY
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  have hbB : b < B := by
    by_contra hn
    have hdv : yAxis B ∣ (liveTiePoint : Normal a b 0) :=
      (Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,yAxis,liveTiePoint]; omega)
    exact ((mem_borderFinset_iff hS _).mp hY).1 (standardSet_dvd_closed S hl.2.2.2 hdv)
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  have hYZ : (yAxis B : Normal a b 0) ≠ zAxis C := by
    intro he; have := congrArg Normal.y he; simp [yAxis,zAxis] at this; omega
  obtain ⟨q,hq,hqY,hqZ,he⟩ := three_border_exists_third S hcard (yAxis B) (zAxis C) hY hZ hYZ
  have hyB : q.y < B := by
    by_contra hn
    have hdq : yAxis B ∣ q := (Normal.exact_divides_iff _ _).mpr
      (by simp [Normal.DividesCriterion,yAxis]; omega)
    exact hqY (border_dvd_border_eq hS hd.1 hY hq hdq).symm
  have hzC : q.z < C := by
    by_contra hn
    have hdq : zAxis C ∣ q := (Normal.exact_divides_iff _ _).mpr
      (by simp [Normal.DividesCriterion,zAxis]; omega)
    exact hqZ (border_dvd_border_eq hS hd.1 hZ hq hdq).symm
  have hn := hnf q hq
  have hnp := border_not_pure_x hS hl hq
  by_cases hx0 : q.x = 0
  · have hy : 0 < q.y := by
      by_contra hy
      have hy0 : q.y = 0 := by omega
      have heq : q = zAxis q.z := by apply Normal.ext <;> simp [zAxis,hx0,hy0]
      have hzc := pure_z_border_unique hS hd.1 (heq ▸ hq) hZ
      exact hqZ (heq.trans (congrArg zAxis hzc))
    have hz : 0 < q.z := by
      by_contra hz
      have hz0 : q.z = 0 := by omega
      have heq : q = yAxis q.y := by apply Normal.ext <;> simp [yAxis,hx0,hz0]
      have hyb := pure_y_border_unique hS hd.1 (heq ▸ hq) hY
      exact hqY (heq.trans (congrArg yAxis hyb))
    have heq : q = yzPoint q.y q.z := by apply Normal.ext <;> simp [yzPoint,hx0]
    have he' : borderFinset S = {yAxis B,zAxis C,yzPoint q.y q.z} := by rw [he,heq]; rfl
    have htt := mixed_three_border_no_x_type_le_two S hS hd hl ha B C q.y q.z hy hyB hz hzC he'
    omega
  · have hx : 0 < q.x := by omega
    by_cases hy0 : q.y = 0
    · have hz : 0 < q.z := by unfold NormalIsPureX at hnp; omega
      have heq : q = (⟨q.x,0,q.z,q.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hy0]
      have he' : borderFinset S = {yAxis B,zAxis C,(⟨q.x,0,q.z,q.x_lt⟩ : Normal a b 0)} := by rw [he,heq]
      have htt := pure_y_xz_three_border_type_le_two S hS hd hl ha B C q.x q.z hx q.x_lt hz hzC hbB he'
      omega
    · have hy : 0 < q.y := by omega
      have hz0 : q.z = 0 := by unfold NormalHasFullSupport at hn; omega
      have heq : q = (⟨q.x,q.y,0,q.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hz0]
      have he' : borderFinset S = {yAxis B,zAxis C,(⟨q.x,q.y,0,q.x_lt⟩ : Normal a b 0)} := by rw [he,heq]
      have htt := pure_y_xy_three_border_type_le_two S hS hd hl ha B C q.x q.y hx q.x_lt hy hC hbB he'
      omega

structure PureXZThreeBorderData (S : Finset (Normal a b 0)) where
  C : ℕ
  r : ℕ
  u : ℕ
  s : ℕ
  w : ℕ
  b_pos : 0 < b
  r_pos : 0 < r
  r_lt : r < a
  u_pos : 0 < u
  s_pos : 0 < s
  s_lt : s < a
  w_pos : 0 < w
  w_lt : w < C
  border : borderFinset S =
    {(⟨r,u,0,r_lt⟩ : Normal a b 0),zAxis C,(⟨s,0,w,s_lt⟩ : Normal a b 0)}

/--
@isnad1 id=or.7h3v.s7.f5081a9ff837 from=translated src=- shape=08b55605 vocab=259fbb2e
-/
theorem pure_three_border_support_classification (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (ht : quotientType ℚ S hS hd hl = 3)
    (hcard : (borderFinset S).card = 3)
    (hnf : ∀ q ∈ borderFinset S, ¬NormalHasFullSupport q) :
    Nonempty (PureThreeBorderData S) ∨ Nonempty (PureXZThreeBorderData S) := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  have hny := pure_three_border_no_y_axis S hS hd hl ha ht hcard hnf
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  let N := S.sup Normal.y + 1
  have hk : (yAxis N : Normal a b 0) ∉ standardSet S := by
    rintro ⟨s,hs,hdv⟩
    have hh := (Normal.exact_divides_iff _ _).mp hdv |>.1
    have hh' := Finset.le_sup (f := Normal.y) hs
    change N ≤ s.y at hh
    dsimp [N] at hh
    omega
  obtain ⟨p,hp,hdp⟩ := killed_has_border_divisor S hS hd (yAxis N) hk
  have hpz : p.z = 0 := by
    have hh := (Normal.exact_divides_iff _ _).mp hdp |>.2.1
    change p.z ≤ 0 at hh; omega
  have hpx : 0 < p.x := by
    by_contra hn
    have hx0 : p.x = 0 := by omega
    have heq : p = yAxis p.y := by apply Normal.ext <;> simp [yAxis,hx0,hpz]
    exact hny p.y (heq ▸ hp)
  have hpy : 0 < p.y := by
    have hh := border_not_pure_x hS hl hp
    unfold NormalIsPureX at hh
    omega
  have hpZ : p ≠ zAxis C := by intro heq; have := congrArg Normal.x heq; simp [zAxis] at this; omega
  obtain ⟨q,hq,hqp,hqZ,he⟩ := three_border_exists_third S hcard p (zAxis C) hp hZ hpZ
  have hqzC : q.z < C := by
    by_contra hn
    have hdq : zAxis C ∣ q := (Normal.exact_divides_iff _ _).mpr
      (by simp [Normal.DividesCriterion,zAxis]; omega)
    exact hqZ (border_dvd_border_eq hS hd.1 hZ hq hdq).symm
  have hpq : ¬p ∣ q := fun hh => hqp (border_dvd_border_eq hS hd.1 hp hq hh).symm
  have hqp' : ¬q ∣ p := fun hh => hqp (border_dvd_border_eq hS hd.1 hq hp hh)
  have hqz : 0 < q.z := by
    by_contra hn
    have hqz0 : q.z = 0 := by omega
    have hqx : 0 < q.x := by
      by_contra hnx
      have hx0 : q.x = 0 := by omega
      have heq : q = yAxis q.y := by apply Normal.ext <;> simp [yAxis,hx0,hqz0]
      exact hny q.y (heq ▸ hq)
    have hqy : 0 < q.y := by
      have hh := border_not_pure_x hS hl hq
      unfold NormalIsPureX at hh; omega
    have hneq : p.x ≠ q.x := by
      intro hx
      have h1 := hpq
      have h2 := hqp'
      simp [Normal.exact_divides_iff,Normal.DividesCriterion,hpz,hqz0,hx] at h1 h2
      omega
    have hpdef : p = (⟨p.x,p.y,0,p.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hpz]
    have hqdef : q = (⟨q.x,q.y,0,q.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hqz0]
    have h1 := hpq
    have h2 := hqp'
    simp only [Normal.exact_divides_iff,Normal.DividesCriterion,hpz,hqz0] at h1 h2
    rcases Nat.lt_or_gt_of_ne hneq with hlt | hgt
    · have he' : borderFinset S = {(⟨p.x,p.y,0,p.x_lt⟩ : Normal a b 0),zAxis C,⟨q.x,q.y,0,q.x_lt⟩} := by
        rw [he,hpdef,hqdef]
      have htt := pure_two_xy_three_border_type_le_two S hS hd hl ha C p.x q.x p.y q.y
        hpx hlt q.x_lt hqy (by omega) (by omega) hC he'
      omega
    · have he' : borderFinset S = {(⟨q.x,q.y,0,q.x_lt⟩ : Normal a b 0),zAxis C,⟨p.x,p.y,0,p.x_lt⟩} := by
        rw [he,hpdef,hqdef]
        ext t; simp; tauto
      have htt := pure_two_xy_three_border_type_le_two S hS hd hl ha C q.x p.x q.y p.y
        hqx hgt p.x_lt hpy (by omega) (by omega) hC he'
      omega
  have hpdef : p = (⟨p.x,p.y,0,p.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hpz]
  by_cases hqx0 : q.x = 0
  · have hqy : 0 < q.y := by
      by_contra hn
      have hy0 : q.y = 0 := by omega
      have heq : q = zAxis q.z := by apply Normal.ext <;> simp [zAxis,hqx0,hy0]
      have hzc := pure_z_border_unique hS hd.1 (heq ▸ hq) hZ
      exact hqZ (heq.trans (congrArg zAxis hzc))
    have hqyp : q.y < p.y+b := by
      simp only [Normal.exact_divides_iff,Normal.DividesCriterion,hpz,hqx0] at hpq
      omega
    left
    refine ⟨⟨C,p.x,p.y,q.y,q.z,hb,hpx,p.x_lt,hpy,hqy,hqyp,hqz,hqzC,?_⟩⟩
    have hqdef : q = (⟨0,q.y,q.z,Nat.pos_of_ne_zero (NeZero.ne a)⟩ : Normal a b 0) := by
      apply Normal.ext <;> simp [hqx0]
    rw [he,hpdef,hqdef]
  · have hqx : 0 < q.x := by omega
    have hqy0 : q.y = 0 := by
      have hh := hnf q hq
      unfold NormalHasFullSupport at hh; omega
    right
    refine ⟨⟨C,p.x,p.y,q.x,q.z,hb,hpx,p.x_lt,hpy,hqx,q.x_lt,hqz,hqzC,?_⟩⟩
    have hqdef : q = (⟨q.x,0,q.z,q.x_lt⟩ : Normal a b 0) := by apply Normal.ext <;> simp [hqy0]
    rw [he,hpdef,hqdef]
end
end P23.OneTie
