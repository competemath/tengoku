import Tengoku.NsP23.P23.OneTie.BorderDeterminesDownset
import Tengoku.NsP23.P23.OneTie.PrincipalBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact live two-border classification; no canonical trace hypotheses. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]

theorem mixed_live_border_card_ge_two (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hc : 0 < c) :
    2 ≤ (borderFinset S).card := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  obtain ⟨B,hB,hY⟩ := mixed_pure_y_border_exists S hS hd hc
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  have hn : (yAxis B : Normal a b c) ≠ zAxis C := by
    intro he; have := congrArg Normal.y he; simp [yAxis,zAxis] at this; omega
  have hsub : ({yAxis B,zAxis C} : Finset (Normal a b c)) ⊆ borderFinset S := by
    intro p hp; simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  simpa [hn] using Finset.card_le_card hsub

theorem pure_live_border_card_ge_two (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) :
    2 ≤ (borderFinset S).card := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  let B := S.sup Normal.y + 1
  have hk : (yAxis B : Normal a b 0) ∉ standardSet S := by
    rintro ⟨s,hs,hdiv⟩
    have hy := ((Normal.exact_divides_iff _ _).mp hdiv).1
    have hh := Finset.le_sup (f := Normal.y) hs
    change B ≤ s.y at hy
    dsimp [B] at hy
    omega
  obtain ⟨g,hg,hgp⟩ := killed_has_border_divisor S hS hd (yAxis B) hk
  have hz : g.z = 0 := by
    have hh := ((Normal.exact_divides_iff _ _).mp hgp).2.1
    change g.z ≤ 0 at hh
    omega
  have hn : g ≠ zAxis C := by
    intro he; have := congrArg Normal.z he; simp [zAxis,hz] at this; omega
  have hsub : ({g,zAxis C} : Finset (Normal a b 0)) ⊆ borderFinset S := by
    intro p hp; simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption
  simpa [hn] using Finset.card_le_card hsub

theorem live_one_tie_border_card_ge_two (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (_hl : IsLiveTie S) :
    2 ≤ (borderFinset S).card := by
  rcases hd.2 with hm | hp
  · exact mixed_live_border_card_ge_two S hS hd (by omega)
  · obtain ⟨_,rfl⟩ := hp
    exact pure_live_border_card_ge_two S hS hd

theorem two_border_eq_pair {S : Finset (Normal a b c)}
    (hc : (borderFinset S).card = 2) {p q : Normal a b c}
    (hp : p ∈ borderFinset S) (hq : q ∈ borderFinset S) (hn : p ≠ q) :
    borderFinset S = {p,q} := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  · simp [hc,hn]

theorem singleton_normal_root_antichain (R : Normal a b c) :
    IsRootAntichain ({R} : Finset (Normal a b c)) := by
  intro p hp q hq hn _
  simp only [Finset.mem_singleton] at hp hq
  exact hn (hp.trans hq.symm)

theorem mixed_live_two_border_root_card_one (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hc : 0 < c) (hg : (borderFinset S).card = 2) :
    S.card = 1 := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  obtain ⟨B,hB,hY⟩ := mixed_pure_y_border_exists S hS hd hc
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd hb
  have hn : (yAxis B : Normal a b c) ≠ zAxis C := by
    intro he; have := congrArg Normal.y he; simp [yAxis,zAxis] at this; omega
  have he := two_border_eq_pair hg hY hZ hn
  have hbB : b < B := by
    by_contra hn
    have hdv : yAxis B ∣ (liveTiePoint : Normal a b c) :=
      (Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,yAxis,liveTiePoint]; omega)
    exact ((mem_borderFinset_iff hS _).mp hY).1 (standardSet_dvd_closed S hl.2.2.2 hdv)
  have hcC : c < C := by
    by_contra hn
    have hdv : zAxis C ∣ (liveTiePoint : Normal a b c) :=
      (Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,zAxis,liveTiePoint]; omega)
    exact ((mem_borderFinset_iff hS _).mp hZ).1 (standardSet_dvd_closed S hl.2.2.2 hdv)
  let R : Normal a b c := mixedCore (a-1) (B-1) (C-1) (by have := hd.1; omega)
  have hp : borderFinset ({R} : Finset (Normal a b c)) = {yAxis B,zAxis C} := by
    rw [mixedPrincipalBorder_last hd.1 (by omega) (by omega) (by omega) (by omega) rfl]
    have hYeq : mixedY (a:=a) (b:=b) (c:=c) (B-1) = yAxis B := by
      apply Normal.ext <;> simp [mixedY,yAxis] <;> omega
    have hZeq : mixedZ (a:=a) (b:=b) (c:=c) (C-1) = zAxis C := by
      apply Normal.ext <;> simp [mixedZ,zAxis] <;> omega
    rw [hYeq,hZeq]
  have hs := standardSet_eq_of_borderFinset_eq hS (by simp : ({R} : Finset _).Nonempty)
    hd (he.trans hp.symm)
  have hr := rootFinset_eq_of_standardSet_eq hd ha (singleton_normal_root_antichain R) hs
  rw [hr]
  simp

theorem pure_live_two_border_root_card_one (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hg : (borderFinset S).card = 2) : S.card = 1 := by
  classical
  have hb : 2 ≤ b := by rcases hd.2 with hm | hp <;> omega
  obtain ⟨C,hC,hZ⟩ := pure_z_border_exists S hS hd (by omega)
  let B := S.sup Normal.y + 1
  have hk : (yAxis B : Normal a b 0) ∉ standardSet S := by
    rintro ⟨s,hs,hdiv⟩
    have hy := ((Normal.exact_divides_iff _ _).mp hdiv).1
    have hh := Finset.le_sup (f := Normal.y) hs
    change B ≤ s.y at hy
    dsimp [B] at hy
    omega
  obtain ⟨H,hH,hHd⟩ := killed_has_border_divisor S hS hd (yAxis B) hk
  have hHz : H.z = 0 := by
    have hz := ((Normal.exact_divides_iff _ _).mp hHd).2.1
    change H.z ≤ 0 at hz
    omega
  have hn : H ≠ zAxis C := by
    intro he; have := congrArg Normal.z he; simp [zAxis,hHz] at this; omega
  have he := two_border_eq_pair hg hH hZ hn
  have hnotx := border_not_pure_x hS hl hH
  have hHy : 0 < H.y := by
    by_contra hy
    have hy0 : H.y = 0 := by omega
    by_cases hx : 0 < H.x
    · exact hnotx ⟨hx,hy0,hHz⟩
    · have hone : H = 1 := by apply Normal.ext <;> simp [hy0,hHz] <;> omega
      have hz := ((mem_borderFinset_iff hS _).mp hH).1
      exact hz (hone.symm ▸ one_mem_standardSet_of_nonempty hS)
  have finish (R : Normal a b 0)
      (hp : borderFinset ({R} : Finset (Normal a b 0)) = {H,zAxis C}) : S.card = 1 := by
    have hs := standardSet_eq_of_borderFinset_eq hS (by simp : ({R} : Finset _).Nonempty)
      hd (he.trans hp.symm)
    have hr := rootFinset_eq_of_standardSet_eq hd ha (singleton_normal_root_antichain R) hs
    rw [hr]; simp
  by_cases hx : H.x = 0
  · have hB : b < H.y := by
      by_contra hn
      have hdv : H ∣ (liveTiePoint : Normal a b 0) :=
        (Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,liveTiePoint,hx,hHz]; omega)
      exact ((mem_borderFinset_iff hS _).mp hH).1 (standardSet_dvd_closed S hl.2.2.2 hdv)
    let R : Normal a b 0 := pureCore (a-1) (H.y-1) (C-1) (by have := hd.1; omega)
    apply finish R
    rw [purePrincipalBorder_last hd.1 hb (by omega) rfl]
    have hh : pureH (a:=a) (b:=b) (a-1) (H.y-1) (by have := hd.1; omega) = H := by
      apply Normal.ext <;> simp [pureH,hx,hHz] <;> omega
    have hz : pureZ (a:=a) (b:=b) (C-1) = zAxis C := by
      apply Normal.ext <;> simp [pureZ,zAxis] <;> omega
    rw [hh,hz]
  · have hpos : 0 < H.x := by omega
    let r := H.x-1
    let u := H.y+b-1
    have hr : r < a-1 := by have := H.x_lt; dsimp [r]; omega
    have hu : b ≤ u := by dsimp [u]; omega
    let R : Normal a b 0 := pureCore r u (C-1) (by omega)
    apply finish R
    rw [purePrincipalBorder_below hd.1 hb hu hr]
    have hh : pureH (a:=a) (b:=b) r u (by omega) = H := by
      apply Normal.ext <;> simp [pureH,hr,r,u,hHz] <;> omega
    have hz : pureZ (a:=a) (b:=b) (C-1) = zAxis C := by
      apply Normal.ext <;> simp [pureZ,zAxis] <;> omega
    rw [hh,hz]

theorem live_two_border_root_card_one (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hg : (borderFinset S).card = 2) : S.card = 1 := by
  rcases hd.2 with hm | hp
  · exact mixed_live_two_border_root_card_one S hS hd hl ha (by omega) hg
  · obtain ⟨_,rfl⟩ := hp
    exact pure_live_two_border_root_card_one S hS hd hl ha hg

theorem live_two_border_quotient_type_eq_one (k : Type*) [Field k]
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (hg : (borderFinset S).card = 2) :
    quotientType k S hS hd hl = 1 := by
  rw [quotientType_eq_rootCard S hS hd hl ha]
  exact live_two_border_root_card_one S hS hd hl ha hg

end
end P23.OneTie
