import Tengoku.NsP23.P23.OneTie.RhoFourPureGeometry
import Tengoku.NsP23.P23.OneTie.RhoFourMixedGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Symbolic two-root bounds for the rejected pure support patterns. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
variable {a b : ℕ} [NeZero a]
set_option maxHeartbeats 1200000

def pureYXZRoots (B C r v : ℕ) (hra : r < a) : Finset (Normal a b 0) :=
  {⟨a-1,B-1,v-1,by have := NeZero.pos a; omega⟩,⟨r-1,b-1,C-1,by omega⟩}

/--
@isnad1 id=eq.9h7v.s8.bd0537a51ea3 from=translated src=- shape=569d89cf vocab=98524c66
-/
theorem pure_y_xz_three_border_roots_exact (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (ha : IsRootAntichain S) (B C r v : ℕ) (hr : 0 < r) (hra : r < a)
    (hv : 0 < v) (hvC : v < C) (hbB : b < B)
    (he : borderFinset S = {yAxis B,zAxis C,(⟨r,0,v,hra⟩ : Normal a b 0)}) :
    S = pureYXZRoots B C r v hra := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  have hT : IsRootAntichain (pureYXZRoots (b := b) B C r v hra) := by
    intro p hp q hq hn hdvd
    simp only [pureYXZRoots,Finset.mem_insert,Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact hn rfl
    · have h := (Normal.exact_divides_iff _ _).mp hdvd
      simp [Normal.DividesCriterion] at h
      omega
    · have h := (Normal.exact_divides_iff _ _).mp hdvd
      simp [Normal.DividesCriterion] at h
      omega
    · exact hn rfl
  apply roots_eq_of_standardSet_eq hd ha hT
  ext p
  rw [standard_iff_no_border_divisor S hS hd,he]
  simp [standardSet,pureYXZRoots,yAxis,zAxis,Normal.exact_divides_iff,Normal.DividesCriterion]
  have := p.x_lt
  omega

/--
@isnad1 id=le.10h7v.s8.b2d7877d4962 from=translated src=- shape=d3404e50 vocab=b8a47a3e
-/
theorem pure_y_xz_three_border_type_le_two (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (B C r v : ℕ) (hr : 0 < r) (hra : r < a)
    (hv : 0 < v) (hvC : v < C) (hbB : b < B)
    (he : borderFinset S = {yAxis B,zAxis C,(⟨r,0,v,hra⟩ : Normal a b 0)}) :
    quotientType ℚ S hS hd hl ≤ 2 := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  let T : Finset (Normal a b 0) :=
    {⟨a-1,B-1,v-1,by omega⟩,⟨r-1,b-1,C-1,by omega⟩}
  have hs : standardSet S = standardSet T := by
    ext p
    rw [standard_iff_no_border_divisor S hS hd,he]
    simp [standardSet,T,yAxis,zAxis,Normal.exact_divides_iff,Normal.DividesCriterion]
    have := p.x_lt
    omega
  rw [quotientType_eq_rootCard S hS hd hl ha]
  exact (roots_card_le_of_standardSet_eq hd ha hs).trans (by
    simpa [T] using Finset.card_insert_le
      (⟨a-1,B-1,v-1,by omega⟩ : Normal a b 0) {⟨r-1,b-1,C-1,by omega⟩})

/--
@isnad1 id=le.10h7v.s8.ed5b4a66b8ee from=translated src=- shape=687ecdfd vocab=b8a47a3e
-/
theorem pure_y_xy_three_border_type_le_two (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (B C r u : ℕ) (hr : 0 < r) (hra : r < a)
    (hu : 0 < u) (hC : 0 < C) (hbB : b < B)
    (he : borderFinset S = {yAxis B,zAxis C,(⟨r,u,0,hra⟩ : Normal a b 0)}) :
    quotientType ℚ S hS hd hl ≤ 2 := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  let E := min B (u+b)
  let V := min B u
  have hE : 0 < E := by dsimp [E]; omega
  have hV : 0 < V := by dsimp [V]; omega
  let T : Finset (Normal a b 0) :=
    {⟨r-1,E-1,C-1,by omega⟩,⟨a-1,V-1,C-1,by omega⟩}
  have hs : standardSet S = standardSet T := by
    ext p
    rw [standard_iff_no_border_divisor S hS hd,he]
    simp [standardSet,T,yAxis,zAxis,Normal.exact_divides_iff,Normal.DividesCriterion]
    have := p.x_lt
    dsimp [E,V] at *
    omega
  rw [quotientType_eq_rootCard S hS hd hl ha]
  exact (roots_card_le_of_standardSet_eq hd ha hs).trans (by
    simpa [T] using Finset.card_insert_le
      (⟨r-1,E-1,C-1,by omega⟩ : Normal a b 0) {⟨a-1,V-1,C-1,by omega⟩})

/--
@isnad1 id=le.12h8v.s8.47bd30689fa9 from=translated src=- shape=00c3506f vocab=eeb69a57
-/
theorem pure_two_xy_three_border_type_le_two (S : Finset (Normal a b 0))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (C r s u v : ℕ) (hr : 0 < r) (hsr : r < s)
    (hsa : s < a) (hv : 0 < v) (hvu : v < u) (huvb : u < v+b) (hC : 0 < C)
    (he : borderFinset S =
      {(⟨r,u,0,by omega⟩ : Normal a b 0),zAxis C,(⟨s,v,0,hsa⟩ : Normal a b 0)}) :
    quotientType ℚ S hS hd hl ≤ 2 := by
  have hb : 0 < b := by rcases hd.2 with hm | hp <;> omega
  let T : Finset (Normal a b 0) :=
    {⟨r-1,v+b-1,C-1,by omega⟩,⟨s-1,u-1,C-1,by omega⟩}
  have hs : standardSet S = standardSet T := by
    ext p
    rw [standard_iff_no_border_divisor S hS hd,he]
    simp [standardSet,T,zAxis,Normal.exact_divides_iff,Normal.DividesCriterion]
    have := p.x_lt
    omega
  rw [quotientType_eq_rootCard S hS hd hl ha]
  exact (roots_card_le_of_standardSet_eq hd ha hs).trans (by
    simpa [T] using Finset.card_insert_le
      (⟨r-1,v+b-1,C-1,by omega⟩ : Normal a b 0) {⟨s-1,u-1,C-1,by omega⟩})
end
end P23.OneTie
