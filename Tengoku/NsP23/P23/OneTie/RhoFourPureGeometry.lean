import Tengoku.NsP23.P23.OneTie.ThreeBorderGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Pure xy/z/yz three-border slice geometry and exact type. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
set_option maxHeartbeats 800000
variable {a b : ℕ} [NeZero a]

structure PureThreeBorderData (S : Finset (Normal a b 0)) where
  C : ℕ
  r : ℕ
  u : ℕ
  v : ℕ
  w : ℕ
  b_pos : 0 < b
  r_pos : 0 < r
  r_lt : r < a
  u_pos : 0 < u
  v_pos : 0 < v
  v_lt : v < u+b
  w_pos : 0 < w
  w_lt : w < C
  border : borderFinset S =
    {(⟨r,u,0,r_lt⟩ : Normal a b 0),zAxis C,
      (⟨0,v,w,Nat.pos_of_ne_zero (NeZero.ne a)⟩ : Normal a b 0)}

namespace PureThreeBorderData
variable {S : Finset (Normal a b 0)} (P : PureThreeBorderData S)
def xRoot : Normal a b 0 := ⟨a-1,P.u-1,P.C-1,by have := P.r_lt; omega⟩
def yRoot : Normal a b 0 := ⟨P.r-1,P.v-1,P.C-1,by have := P.r_lt; omega⟩
def zRoot : Normal a b 0 := ⟨P.r-1,P.u+b-1,P.w-1,by have := P.r_lt; omega⟩
def smallRoot : Normal a b 0 := ⟨a-1,P.v-1,P.C-1,by have := P.r_lt; omega⟩
def threeRoots : Finset (Normal a b 0) := {P.xRoot,P.yRoot,P.zRoot}
def twoRoots : Finset (Normal a b 0) := {P.smallRoot,P.zRoot}
end PureThreeBorderData

/--
@isnad1 id=iff.2h5v.s7.3c3626c9744e from=translated src=- shape=3f9b2a0c vocab=b0332a6b
-/
theorem pure_three_border_standard_slices {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (p : Normal a b 0) : p ∈ standardSet S ↔
      p.y < P.u+b ∧ p.z < P.C ∧ (p.x < P.r ∨ p.y < P.u) ∧
        (p.y < P.v ∨ p.z < P.w) := by
  rw [standard_iff_no_border_divisor S hS hd p,P.border]
  simp [Normal.exact_divides_iff,Normal.DividesCriterion,zAxis]
  omega

/--
@isnad1 id=eq.4h4v.s6.416f70a190e5 from=translated src=- shape=eb444c3a vocab=ea215dfc
-/
theorem pure_three_border_roots_exact {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hanti : IsRootAntichain S) (huv : P.u < P.v) : S = P.threeRoots := by
  have hanti' : IsRootAntichain P.threeRoots := by
    intro s hs t ht hne hdiv
    simp only [PureThreeBorderData.threeRoots,Finset.mem_insert,Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    all_goals try exact hne rfl
    all_goals have hh := (Normal.exact_divides_iff _ _).mp hdiv
    all_goals simp only [Normal.DividesCriterion,PureThreeBorderData.xRoot,
      PureThreeBorderData.yRoot,PureThreeBorderData.zRoot] at hh
    all_goals
      have := P.r_pos
      have := P.r_lt
      have := P.b_pos
      have := P.u_pos
      have := P.v_pos
      have := P.v_lt
      have := P.w_pos
      have := P.w_lt
      omega
  apply roots_eq_of_standardSet_eq hd hanti hanti'
  ext p
  rw [pure_three_border_standard_slices P hS hd]
  have := P.r_pos
  have := P.r_lt
  have := P.b_pos
  have := P.u_pos
  have := P.v_pos
  have := P.v_lt
  have := P.w_pos
  have := P.w_lt
  have hx := p.x_lt
  simp [standardSet,PureThreeBorderData.threeRoots,PureThreeBorderData.xRoot,
    PureThreeBorderData.yRoot,PureThreeBorderData.zRoot,
    Normal.exact_divides_iff,Normal.DividesCriterion] <;> omega

/--
@isnad1 id=eq.4h4v.s6.8c020997fd20 from=translated src=- shape=eb444c3a vocab=37e1f704
-/
theorem pure_three_border_two_roots_exact {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hanti : IsRootAntichain S) (hvu : P.v ≤ P.u) : S = P.twoRoots := by
  have hanti' : IsRootAntichain P.twoRoots := by
    intro s hs t ht hne hdiv
    simp only [PureThreeBorderData.twoRoots,Finset.mem_insert,Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    all_goals try exact hne rfl
    all_goals have hh := (Normal.exact_divides_iff _ _).mp hdiv
    all_goals simp only [Normal.DividesCriterion,PureThreeBorderData.smallRoot,
      PureThreeBorderData.zRoot] at hh
    all_goals
      have := P.r_pos
      have := P.r_lt
      have := P.b_pos
      have := P.u_pos
      have := P.v_pos
      have := P.v_lt
      have := P.w_pos
      have := P.w_lt
      omega
  apply roots_eq_of_standardSet_eq hd hanti hanti'
  ext p
  rw [pure_three_border_standard_slices P hS hd]
  have := P.r_pos
  have := P.r_lt
  have := P.b_pos
  have := P.u_pos
  have := P.v_pos
  have := P.v_lt
  have := P.w_pos
  have := P.w_lt
  have hx := p.x_lt
  simp [standardSet,PureThreeBorderData.twoRoots,PureThreeBorderData.smallRoot,
    PureThreeBorderData.zRoot,Normal.exact_divides_iff,Normal.DividesCriterion] <;> omega

/--
@isnad1 id=eq.4h4v.s7.220e3b312917 from=translated src=- shape=c3821e4a vocab=bee74f8a
-/
theorem pure_three_border_type_formula {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (hanti : IsRootAntichain S) :
    quotientType ℚ S hS hd hl = 2 + if P.u < P.v then 1 else 0 := by
  rw [quotientType_eq_rootCard S hS hd hl hanti]
  by_cases huv : P.u < P.v
  · rw [ite_eq_left huv,pure_three_border_roots_exact P hS hd hanti huv]
    have h12 : P.xRoot ≠ P.yRoot := by
      intro he
      have hh := congrArg Normal.x he
      dsimp [PureThreeBorderData.xRoot,PureThreeBorderData.yRoot] at hh
      have := P.r_pos
      have := P.r_lt
      omega
    have h13 : P.xRoot ≠ P.zRoot := by
      intro he
      have hh := congrArg Normal.x he
      dsimp [PureThreeBorderData.xRoot,PureThreeBorderData.zRoot] at hh
      have := P.r_pos
      have := P.r_lt
      omega
    have h23 : P.yRoot ≠ P.zRoot := by
      intro he
      have hh := congrArg Normal.y he
      dsimp [PureThreeBorderData.yRoot,PureThreeBorderData.zRoot] at hh
      have := P.v_pos
      have := P.v_lt
      omega
    simp [PureThreeBorderData.threeRoots,h12,h13,h23]
  · rw [ite_eq_right huv,pure_three_border_two_roots_exact P hS hd hanti (by omega)]
    have h12 : P.smallRoot ≠ P.zRoot := by
      intro he
      have hh := congrArg Normal.x he
      dsimp [PureThreeBorderData.smallRoot,PureThreeBorderData.zRoot] at hh
      have := P.r_pos
      have := P.r_lt
      omega
    simp [PureThreeBorderData.twoRoots,h12]

/--
@isnad1 id=iff.4h4v.s6.605131041089 from=translated src=- shape=601441a4 vocab=3ea54c59
-/
theorem pure_three_border_type_three_iff {S : Finset (Normal a b 0)}
    (P : PureThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b 0)
    (hl : IsLiveTie S) (hanti : IsRootAntichain S) :
    quotientType ℚ S hS hd hl = 3 ↔ P.u < P.v := by
  rw [pure_three_border_type_formula P hS hd hl hanti]
  split_ifs <;> omega
end
end P23.OneTie
