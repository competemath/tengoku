import Tengoku.NsP23.P23.Monomial.PlainGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section

def plainExp (x y z : ℕ) : PlainExp := Finsupp.single 0 x+Finsupp.single 1 y+Finsupp.single 2 z
@[simp] theorem plainExp_zero (x y z : ℕ) : plainExp x y z 0=x := by simp [plainExp]
@[simp] theorem plainExp_one (x y z : ℕ) : plainExp x y z 1=y := by simp [plainExp]
@[simp] theorem plainExp_two (x y z : ℕ) : plainExp x y z 2=z := by simp [plainExp]
theorem plainExp_coordinates (p : PlainExp) : plainExp (p 0) (p 1) (p 2)=p := by
  ext j; fin_cases j <;> simp
@[simp] theorem plainExp_eq (x y z x' y' z' : ℕ) :
    plainExp x y z=plainExp x' y' z' ↔ x=x' ∧ y=y' ∧ z=z' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun p : PlainExp=>p 0) h,
      by simpa using congrArg (fun p : PlainExp=>p 1) h,
      by simpa using congrArg (fun p : PlainExp=>p 2) h⟩
  · rintro ⟨rfl,rfl,rfl⟩; rfl
theorem plainExp_eq_coordinates (p : PlainExp) (x y z : ℕ) :
    p=plainExp x y z ↔ p 0=x ∧ p 1=y ∧ p 2=z := by
  constructor
  · intro h; simp [h]
  · rintro ⟨hx,hy,hz⟩; simpa [hx,hy,hz] using (plainExp_coordinates p).symm

def plainTriangleRoots (r u v : ℕ) : Finset PlainExp :=
  {plainExp r (u+1) (v+1),plainExp (r+1) u (v+1),plainExp (r+1) (u+1) v}
def plainTriangleBorder (r u v : ℕ) : Finset PlainExp :=
  {plainExp (r+2) 0 0,plainExp 0 (u+2) 0,plainExp 0 0 (v+2),plainExp (r+1) (u+1) (v+1)}

set_option maxHeartbeats 1000000 in
theorem plainTriangle_border_exact (r u v : ℕ) :
    plainBorderFinset (plainTriangleRoots r u v)=plainTriangleBorder r u v := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainStandardSet,plainTriangleRoots,Finset.mem_insert,Finset.mem_singleton,
    exists_eq_or_imp,exists_eq_left,plainDivides,Fin.forall_fin_succ,plainExp_zero,
    plainExp_one,plainExp_two,plainPredecessor_apply]
  simp [plainTriangleBorder,plainExp_eq_coordinates]
  omega

theorem plainTriangle_border_card (r u v : ℕ) :
    (plainBorderFinset (plainTriangleRoots r u v)).card=4 := by
  rw [plainTriangle_border_exact]
  simp [plainTriangleBorder,plainExp_eq]

def plainDominantAxisRoots (r u v : ℕ) : Finset PlainExp :=
  {plainExp r u v,plainExp (r+1) 0 0,plainExp 0 (u+1) 0}
def plainDominantAxisBorder (r u v : ℕ) : Finset PlainExp :=
  {plainExp (r+2) 0 0,plainExp 0 (u+2) 0,plainExp 0 0 (v+1),
    plainExp (r+1) 1 0,plainExp (r+1) 0 1,plainExp 1 (u+1) 0,plainExp 0 (u+1) 1}

theorem plainDominantAxis_standard (r u v : ℕ) (p : PlainExp) :
    p ∈ plainStandardSet (plainDominantAxisRoots r u v) ↔
      (p 0≤r ∧ p 1≤u ∧ p 2≤v) ∨
      (p 0≤r+1 ∧ p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1≤u+1 ∧ p 2=0) := by
  simp [plainStandardSet,plainDominantAxisRoots,plainDivides,Fin.forall_fin_succ]

set_option maxHeartbeats 1000000 in
theorem plainDominantAxis_border_exact (r u v : ℕ) (hr : 0<r) (hu : 0<u) (hv : 0<v) :
    plainBorderFinset (plainDominantAxisRoots r u v)=plainDominantAxisBorder r u v := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainDominantAxis_standard,Fin.forall_fin_succ,plainPredecessor_apply]
  by_cases hz : p 2=0 <;> by_cases hx : p 0=0 <;> by_cases hy : p 1=0
  all_goals simp [plainDominantAxisBorder,plainExp_eq_coordinates,hz,hx,hy]
  all_goals omega

theorem plainDominantAxis_border_card (r u v : ℕ) (hr : 0<r) (hu : 0<u) (hv : 0<v) :
    (plainBorderFinset (plainDominantAxisRoots r u v)).card=7 := by
  rw [plainDominantAxis_border_exact r u v hr hu hv]
  have hrn : r+1≠1 := by omega
  have hun : u+1≠1 := by omega
  simp [plainDominantAxisBorder,Finset.card_insert_eq_ite,plainExp_eq,hrn,hun,Ne.symm hrn,Ne.symm hun]
  omega

def plainPlaneAxisRoots (r u s v h : ℕ) : Finset PlainExp :=
  {plainExp r v 0,plainExp u s 0,plainExp 0 0 h}
def plainPlaneAxisBorder (r u s v h : ℕ) : Finset PlainExp :=
  {plainExp (u+1) 0 0,plainExp 0 (v+1) 0,plainExp (r+1) (s+1) 0,
    plainExp 0 0 (h+1),plainExp 1 0 1,plainExp 0 1 1}

theorem plainPlaneAxis_standard (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (p : PlainExp) :
    p ∈ plainStandardSet (plainPlaneAxisRoots r u s v h) ↔
      (p 2 = 0 ∧ p 0 ≤ u ∧ p 1 ≤ v ∧ (p 0 ≤ r ∨ p 1 ≤ s)) ∨
      (p 0 = 0 ∧ p 1 = 0 ∧ p 2 ≤ h) := by
  simp [plainStandardSet,plainPlaneAxisRoots,plainDivides,Fin.forall_fin_succ]
  omega

set_option maxHeartbeats 1000000 in
theorem plainPlaneAxis_border_exact (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (hh : 0<h) :
    plainBorderFinset (plainPlaneAxisRoots r u s v h)=plainPlaneAxisBorder r u s v h := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainPlaneAxis_standard r u s v h hru hsv,Fin.forall_fin_succ,plainPredecessor_apply]
  by_cases hz : p 2=0 <;> by_cases hx : p 0=0 <;> by_cases hy : p 1=0
  all_goals simp [plainPlaneAxisBorder,plainExp_eq_coordinates,hz,hx,hy]
  all_goals omega

theorem plainPlaneAxis_border_card (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (hh : 0<h) :
    (plainBorderFinset (plainPlaneAxisRoots r u s v h)).card=6 := by
  rw [plainPlaneAxis_border_exact r u s v h hru hsv hh]
  have hu : u+1≠1 := by omega
  have hv : v+1≠1 := by omega
  have hn : h+1≠1 := by omega
  simp [plainPlaneAxisBorder,Finset.card_insert_eq_ite,plainExp_eq,hu,hv,hn,Ne.symm hu,Ne.symm hv,Ne.symm hn]

end
end P23.Monomial
