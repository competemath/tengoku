import Tengoku.NsP23.P23.OneTie.ThreeBorderSupport
import Tengoku.NsP23.P23.Presentation.QuotientLocalSocle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Symbolic axis and downset facts used by the three-border classification. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b c : ℕ} [NeZero a]

def yAxis (n : ℕ) : Normal a b c := ⟨0,n,0,Nat.pos_of_ne_zero (NeZero.ne a)⟩
def zAxis (n : ℕ) : Normal a b c := ⟨0,0,n,Nat.pos_of_ne_zero (NeZero.ne a)⟩

theorem standard_iff_no_border_divisor (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (p : Normal a b c) :
    p ∈ standardSet S ↔ ∀ g ∈ borderFinset S, ¬g ∣ p := by
  constructor
  · intro hp g hg hgp
    exact ((mem_borderFinset_iff hS g).mp hg).1 (standardSet_dvd_closed S hp hgp)
  · intro hp
    by_contra hn
    obtain ⟨g,hg,hgp⟩ := killed_has_border_divisor S hS hd p hn
    exact hp g hg hgp

theorem border_dvd_border_eq {S : Finset (Normal a b c)} (hS : S.Nonempty)
    (ha : 2 ≤ a) {p q : Normal a b c}
    (hp : p ∈ borderFinset S) (hq : q ∈ borderFinset S) (h : p ∣ q) : p = q := by
  by_contra hn
  have hqmin := (isMinimalBorder_iff_isDivisibilityMinimalKilled S q
    (variableGenerators_ne_one_of_two_le ha)).mp ((mem_borderFinset_iff hS q).mp hq)
  exact ((mem_borderFinset_iff hS p).mp hp).1 (hqmin.2 p h hn)

theorem pure_y_border_unique {S : Finset (Normal a b c)} (hS : S.Nonempty)
    (ha : 2 ≤ a) {u v : ℕ} (hu : yAxis u ∈ borderFinset S)
    (hv : yAxis v ∈ borderFinset S) : u = v := by
  rcases Nat.le_total u v with h | h
  · have he : (yAxis u : Normal a b c) = yAxis v := border_dvd_border_eq hS ha hu hv
      ((Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,yAxis,h]))
    exact congrArg Normal.y he
  · have he : (yAxis v : Normal a b c) = yAxis u := border_dvd_border_eq hS ha hv hu
      ((Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,yAxis,h]))
    exact (congrArg Normal.y he).symm

theorem pure_z_border_unique {S : Finset (Normal a b c)} (hS : S.Nonempty)
    (ha : 2 ≤ a) {u v : ℕ} (hu : zAxis u ∈ borderFinset S)
    (hv : zAxis v ∈ borderFinset S) : u = v := by
  rcases Nat.le_total u v with h | h
  · have he : (zAxis u : Normal a b c) = zAxis v := border_dvd_border_eq hS ha hu hv
      ((Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,zAxis,h]))
    exact congrArg Normal.z he
  · have he : (zAxis v : Normal a b c) = zAxis u := border_dvd_border_eq hS ha hv hu
      ((Normal.exact_divides_iff _ _).mpr (by simp [Normal.DividesCriterion,zAxis,h]))
    exact (congrArg Normal.z he).symm

theorem three_border_exists_third (S : Finset (Normal a b c))
    (hcard : (borderFinset S).card = 3) (Y Z : Normal a b c)
    (hY : Y ∈ borderFinset S) (hZ : Z ∈ borderFinset S) (hne : Y ≠ Z) :
    ∃ q ∈ borderFinset S, q ≠ Y ∧ q ≠ Z ∧ borderFinset S = {Y,Z,q} := by
  classical
  let G := borderFinset S
  let E := (G.erase Y).erase Z
  have hZ' : Z ∈ G.erase Y := Finset.mem_erase.mpr ⟨hne.symm,hZ⟩
  have hcard' : E.card = 1 := by
    dsimp [E]
    rw [Finset.card_erase_of_mem hZ',Finset.card_erase_of_mem hY,hcard]
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hcard'
  have hqE : q ∈ E := hq.symm ▸ Finset.mem_singleton_self q
  have hqG : q ∈ G := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hqE)
  have hqY : q ≠ Y := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hqE)
  have hqZ : q ≠ Z := Finset.ne_of_mem_erase hqE
  have hr : insert Y (insert Z E) = G := by
    dsimp [E]
    rw [Finset.insert_erase hZ',Finset.insert_erase hY]
  rw [hq] at hr
  exact ⟨q,hqG,hqY,hqZ,hr.symm⟩

theorem mixed_pure_y_border_exists (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hc : 0 < c) :
    ∃ B, 0 < B ∧ yAxis B ∈ borderFinset S := by
  classical
  let B := S.sup Normal.y + 1
  have hk : (yAxis B : Normal a b c) ∉ standardSet S := by
    rintro ⟨s,hs,hdiv⟩
    have hy := (Normal.exact_divides_iff _ _).mp hdiv |>.1
    have hb := Finset.le_sup (f := Normal.y) hs
    change B ≤ s.y at hy
    dsimp [B] at hy
    omega
  obtain ⟨g,hg,hgdiv⟩ := killed_has_border_divisor S hS hd (yAxis B) hk
  have hh := (Normal.exact_divides_iff _ _).mp hgdiv
  have gx : g.x = 0 := by
    simp only [Normal.DividesCriterion, yAxis] at hh
    omega
  have gz : g.z = 0 := by
    simp only [Normal.DividesCriterion, yAxis] at hh
    omega
  have gy : 0 < g.y := by
    by_contra hn
    have ge : g = 1 := by apply Normal.ext <;> simp [gx,gz] <;> omega
    have hkill := ((mem_borderFinset_iff hS g).mp hg).1
    rw [ge] at hkill
    exact hkill (one_mem_standardSet_of_nonempty hS)
  refine ⟨g.y,gy,?_⟩
  have ge : (yAxis g.y : Normal a b c) = g := by apply Normal.ext <;> simp [yAxis,gx,gz]
  rwa [ge]

theorem pure_z_border_exists (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hb : 0 < b) :
    ∃ C, 0 < C ∧ zAxis C ∈ borderFinset S := by
  classical
  let C := S.sup Normal.z + 1
  have hk : (zAxis C : Normal a b c) ∉ standardSet S := by
    rintro ⟨s,hs,hdiv⟩
    have hz := (Normal.exact_divides_iff _ _).mp hdiv |>.2.1
    have hc := Finset.le_sup (f := Normal.z) hs
    change C ≤ s.z at hz
    dsimp [C] at hz
    omega
  obtain ⟨g,hg,hgdiv⟩ := killed_has_border_divisor S hS hd (zAxis C) hk
  have hh := (Normal.exact_divides_iff _ _).mp hgdiv
  have gx : g.x = 0 := by
    simp only [Normal.DividesCriterion, zAxis] at hh
    omega
  have gy : g.y = 0 := by
    simp only [Normal.DividesCriterion, zAxis] at hh
    omega
  have gz : 0 < g.z := by
    by_contra hn
    have ge : g = 1 := by apply Normal.ext <;> simp [gx,gy] <;> omega
    have hkill := ((mem_borderFinset_iff hS g).mp hg).1
    rw [ge] at hkill
    exact hkill (one_mem_standardSet_of_nonempty hS)
  refine ⟨g.z,gz,?_⟩
  have ge : (zAxis g.z : Normal a b c) = g := by apply Normal.ext <;> simp [zAxis,gx,gy]
  rwa [ge]

theorem normal_dvd_antisymm_live (hd : IsLiveParameterDomain a b c)
    {p q : Normal a b c} (hpq : p ∣ q) (hqp : q ∣ p) : p = q := by
  have h := (Normal.exact_divides_iff _ _).mp hpq
  have h' := (Normal.exact_divides_iff _ _).mp hqp
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  unfold Normal.DividesCriterion at h h'
  apply Normal.ext <;> omega

theorem roots_subset_of_standardSet_eq {S T : Finset (Normal a b c)}
    (hd : IsLiveParameterDomain a b c) (hS : IsRootAntichain S)
    (he : standardSet S = standardSet T) : S ⊆ T := by
  intro s hs
  have hsstd : s ∈ standardSet T := he ▸ (show s ∈ standardSet S from ⟨s,hs,dvd_refl _⟩)
  obtain ⟨t,ht,hst⟩ := hsstd
  have htstd : t ∈ standardSet S := he.symm ▸ (show t ∈ standardSet T from ⟨t,ht,dvd_refl _⟩)
  obtain ⟨s',hs',hts⟩ := htstd
  have hss : s = s' := by
    by_contra hn
    exact hS s hs s' hs' hn (dvd_trans hst hts)
  have heq : s = t := normal_dvd_antisymm_live hd hst (hss.symm ▸ hts)
  rwa [heq]

theorem roots_card_le_of_standardSet_eq {S T : Finset (Normal a b c)}
    (hd : IsLiveParameterDomain a b c) (hS : IsRootAntichain S)
    (he : standardSet S = standardSet T) : S.card ≤ T.card :=
  Finset.card_le_card (roots_subset_of_standardSet_eq hd hS he)

theorem roots_eq_of_standardSet_eq {S T : Finset (Normal a b c)}
    (hd : IsLiveParameterDomain a b c) (hS : IsRootAntichain S) (hT : IsRootAntichain T)
    (he : standardSet S = standardSet T) : S = T := by
  have hsub (S T : Finset (Normal a b c)) (hS : IsRootAntichain S)
      (he : standardSet S = standardSet T) : S ⊆ T := by
    intro s hs
    have hsstd : s ∈ standardSet T := he ▸ (show s ∈ standardSet S from ⟨s,hs,dvd_refl _⟩)
    obtain ⟨t,ht,hst⟩ := hsstd
    have htstd : t ∈ standardSet S := he.symm ▸ (show t ∈ standardSet T from ⟨t,ht,dvd_refl _⟩)
    obtain ⟨s',hs',hts⟩ := htstd
    have hss : s = s' := by
      by_contra hn
      exact hS s hs s' hs' hn (dvd_trans hst hts)
    have heq : s = t := normal_dvd_antisymm_live hd hst (hss.symm ▸ hts)
    rwa [heq]
  exact Finset.Subset.antisymm (hsub S T hS he) (hsub T S hT he.symm)
end
end P23.OneTie
