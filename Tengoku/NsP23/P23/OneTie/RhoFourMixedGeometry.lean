import Tengoku.NsP23.P23.OneTie.ThreeBorderGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact mixed three-border slices and socles. No trace hypothesis is hidden
in the geometry definitions. -/
namespace P23.OneTie
noncomputable section
open P23.Artin P23.Presentation
set_option maxHeartbeats 800000
variable {a b c : ℕ} [NeZero a]

def yzPoint (u v : ℕ) : Normal a b c := ⟨0,u,v,Nat.pos_of_ne_zero (NeZero.ne a)⟩

def noXThreeBorderRoots (B C u v : ℕ) : Finset (Normal a b c) :=
  {⟨a-1,B-1,v-1,by have := Nat.pos_of_ne_zero (NeZero.ne a); omega⟩,
   ⟨a-1,u-1,C-1,by have := Nat.pos_of_ne_zero (NeZero.ne a); omega⟩}

theorem no_x_three_border_standard (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (B C u v : ℕ)
    (he : borderFinset S = {yAxis B,zAxis C,yzPoint u v}) (p : Normal a b c) :
    p ∈ standardSet S ↔ p.y < B ∧ p.z < C ∧ (p.y < u ∨ p.z < v) := by
  rw [standard_iff_no_border_divisor S hS hd p, he]
  simp [Normal.exact_divides_iff, Normal.DividesCriterion, yAxis,zAxis,yzPoint] <;> omega

theorem no_x_three_border_roots_exact (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (ha : IsRootAntichain S)
    (B C u v : ℕ) (hu : 0 < u) (huB : u < B) (hv : 0 < v) (hvC : v < C)
    (he : borderFinset S = {yAxis B,zAxis C,yzPoint u v}) :
    S = noXThreeBorderRoots B C u v := by
  have hanti : IsRootAntichain (noXThreeBorderRoots (a := a) (b := b) (c := c) B C u v) := by
    intro s hs t ht hne hdiv
    simp only [noXThreeBorderRoots, Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact hne rfl
    · have hh := (Normal.exact_divides_iff _ _).mp hdiv
      simp only [Normal.DividesCriterion] at hh
      omega
    · have hh := (Normal.exact_divides_iff _ _).mp hdiv
      simp only [Normal.DividesCriterion] at hh
      omega
    · exact hne rfl
  apply roots_eq_of_standardSet_eq hd ha hanti
  ext p
  rw [no_x_three_border_standard S hS hd B C u v he]
  have hx := p.x_lt
  simp [standardSet,noXThreeBorderRoots,Normal.exact_divides_iff,Normal.DividesCriterion] <;> omega

theorem mixed_three_border_no_x_type_le_two (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c) (hl : IsLiveTie S)
    (ha : IsRootAntichain S) (B C u v : ℕ) (hu : 0 < u) (huB : u < B)
    (hv : 0 < v) (hvC : v < C)
    (he : borderFinset S = {yAxis B,zAxis C,yzPoint u v}) :
    quotientType ℚ S hS hd hl ≤ 2 := by
  rw [quotientType_eq_rootCard S hS hd hl ha,
    no_x_three_border_roots_exact S hS hd ha B C u v hu huB hv hvC he]
  simpa [noXThreeBorderRoots] using Finset.card_insert_le
    (⟨a-1,B-1,v-1,by have := Nat.pos_of_ne_zero (NeZero.ne a); omega⟩ : Normal a b c)
    {⟨a-1,u-1,C-1,by have := Nat.pos_of_ne_zero (NeZero.ne a); omega⟩}

structure MixedThreeBorderData (S : Finset (Normal a b c)) where
  B : ℕ
  C : ℕ
  r : ℕ
  v : ℕ
  b_pos : 0 < b
  c_pos : 0 < c
  B_pos : 0 < B
  r_pos : 0 < r
  r_lt : r < a
  v_pos : 0 < v
  v_lt : v < C
  border : borderFinset S = {yAxis B,zAxis C,(⟨r,0,v,r_lt⟩ : Normal a b c)}

namespace MixedThreeBorderData
variable {S : Finset (Normal a b c)} (M : MixedThreeBorderData S)
def highRoot : Normal a b c := ⟨a-1,M.B-1,M.v-1,by have := M.r_lt; omega⟩
def yCornerRoot : Normal a b c := ⟨M.r-1,b-1,M.C-1,by have := M.r_lt; omega⟩
def zCornerRoot : Normal a b c := ⟨M.r-1,M.B-1,c+M.v-1,by have := M.r_lt; omega⟩
def lowBoxRoot : Normal a b c := ⟨M.r-1,M.B-1,M.C-1,by have := M.r_lt; omega⟩
def threeRoots : Finset (Normal a b c) := {M.highRoot,M.yCornerRoot,M.zCornerRoot}
def twoRoots : Finset (Normal a b c) := {M.highRoot,M.lowBoxRoot}
end MixedThreeBorderData

theorem mixed_three_border_standard_slices {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (p : Normal a b c) : p ∈ standardSet S ↔ p.y < M.B ∧ p.z < M.C ∧
      ((p.x < M.r ∧ (p.y < b ∨ p.z < c+M.v)) ∨ (M.r ≤ p.x ∧ p.z < M.v)) := by
  rw [standard_iff_no_border_divisor S hS hd p, M.border]
  simp [Normal.exact_divides_iff,Normal.DividesCriterion,yAxis,zAxis]
  omega

theorem mixed_three_border_roots_exact {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hanti : IsRootAntichain S) (hbB : b < M.B) (hcvC : c+M.v < M.C) :
    S = M.threeRoots := by
  have hanti' : IsRootAntichain M.threeRoots := by
    intro s hs t ht hne hdiv
    simp only [MixedThreeBorderData.threeRoots,Finset.mem_insert,Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    all_goals try exact hne rfl
    all_goals have hh := (Normal.exact_divides_iff _ _).mp hdiv
    all_goals simp only [Normal.DividesCriterion,MixedThreeBorderData.highRoot,
      MixedThreeBorderData.yCornerRoot,MixedThreeBorderData.zCornerRoot] at hh
    all_goals
      have := M.r_pos
      have := M.r_lt
      have := M.b_pos
      have := M.c_pos
      have := M.B_pos
      have := M.v_pos
      omega
  apply roots_eq_of_standardSet_eq hd hanti hanti'
  ext p
  rw [mixed_three_border_standard_slices M hS hd]
  have := M.r_pos; have := M.r_lt; have := M.b_pos; have := M.c_pos
  have := M.B_pos; have := M.v_pos; have hx := p.x_lt
  simp [standardSet,MixedThreeBorderData.threeRoots,MixedThreeBorderData.highRoot,
    MixedThreeBorderData.yCornerRoot,MixedThreeBorderData.zCornerRoot,
    Normal.exact_divides_iff,Normal.DividesCriterion] <;> omega

theorem mixed_three_border_two_roots_of_degenerate {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hanti : IsRootAntichain S) (hdeg : M.B ≤ b ∨ M.C ≤ c+M.v) : S = M.twoRoots := by
  have hanti' : IsRootAntichain M.twoRoots := by
    intro s hs t ht hne hdiv
    simp only [MixedThreeBorderData.twoRoots,Finset.mem_insert,Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    all_goals try exact hne rfl
    all_goals have hh := (Normal.exact_divides_iff _ _).mp hdiv
    all_goals simp only [Normal.DividesCriterion,MixedThreeBorderData.highRoot,
      MixedThreeBorderData.lowBoxRoot] at hh
    all_goals
      have := M.r_pos
      have := M.r_lt
      have := M.b_pos
      have := M.c_pos
      have := M.B_pos
      have := M.v_pos
      have := M.v_lt
      omega
  apply roots_eq_of_standardSet_eq hd hanti hanti'
  ext p
  rw [mixed_three_border_standard_slices M hS hd]
  have := M.r_pos; have := M.r_lt; have := M.b_pos; have := M.c_pos
  have := M.B_pos; have := M.v_pos; have := M.v_lt; have hx := p.x_lt
  simp [standardSet,MixedThreeBorderData.twoRoots,MixedThreeBorderData.highRoot,
    MixedThreeBorderData.lowBoxRoot,Normal.exact_divides_iff,Normal.DividesCriterion] <;> omega

theorem mixed_three_border_type_three_iff {S : Finset (Normal a b c)}
    (M : MixedThreeBorderData S) (hS : S.Nonempty) (hd : IsLiveParameterDomain a b c)
    (hl : IsLiveTie S) (hanti : IsRootAntichain S) :
    quotientType ℚ S hS hd hl = 3 ↔ b < M.B ∧ c+M.v < M.C := by
  rw [quotientType_eq_rootCard S hS hd hl hanti]
  constructor
  · intro ht
    by_contra hn
    have hdeg : M.B ≤ b ∨ M.C ≤ c+M.v := by omega
    have he := mixed_three_border_two_roots_of_degenerate M hS hd hanti hdeg
    have hc : M.twoRoots.card ≤ 2 := by
      simpa [MixedThreeBorderData.twoRoots] using Finset.card_insert_le M.highRoot {M.lowBoxRoot}
    rw [he] at ht
    omega
  · rintro ⟨hb,hc⟩
    rw [mixed_three_border_roots_exact M hS hd hanti hb hc]
    have h12 : M.highRoot ≠ M.yCornerRoot := by
      intro he; have := congrArg Normal.x he; dsimp [MixedThreeBorderData.highRoot,
        MixedThreeBorderData.yCornerRoot] at this; have := M.r_pos; have := M.r_lt; omega
    have h13 : M.highRoot ≠ M.zCornerRoot := by
      intro he; have := congrArg Normal.x he; dsimp [MixedThreeBorderData.highRoot,
        MixedThreeBorderData.zCornerRoot] at this; have := M.r_pos; have := M.r_lt; omega
    have h23 : M.yCornerRoot ≠ M.zCornerRoot := by
      intro he; have := congrArg Normal.y he; dsimp [MixedThreeBorderData.yCornerRoot,
        MixedThreeBorderData.zCornerRoot] at this; have := M.b_pos; omega
    simp [MixedThreeBorderData.threeRoots,h12,h13,h23]
end
end P23.OneTie
