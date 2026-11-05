import Tengoku.NsP23.P23.Monomial.PlainGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Monomial
noncomputable section

def plainExp (x y z : ℕ) : PlainExp := Finsupp.single 0 x+Finsupp.single 1 y+Finsupp.single 2 z
/--
@isnad1 id=eq.0h3v.s5.0fac2ec402c4 from=translated src=- shape=065a5397 vocab=396a2686
-/
@[simp] theorem plainExp_zero (x y z : ℕ) : plainExp x y z 0=x := by simp [plainExp]
/--
@isnad1 id=eq.0h3v.s5.72f85963009f from=translated src=- shape=1de9fdc0 vocab=396a2686
-/
@[simp] theorem plainExp_one (x y z : ℕ) : plainExp x y z 1=y := by simp [plainExp]
/--
@isnad1 id=eq.0h3v.s5.351ff4032d26 from=translated src=- shape=af1c0e71 vocab=396a2686
-/
@[simp] theorem plainExp_two (x y z : ℕ) : plainExp x y z 2=z := by simp [plainExp]
/--
@isnad1 id=eq.0h1v.s7.31532c465eaf from=translated src=- shape=57e75744 vocab=396a2686
-/
theorem plainExp_coordinates (p : PlainExp) : plainExp (p 0) (p 1) (p 2)=p := by
  ext j; fin_cases j <;> simp
/--
@isnad1 id=iff.0h6v.s5.5158feea3e34 from=translated src=- shape=323e0fd6 vocab=00294125
-/
@[simp] theorem plainExp_eq (x y z x' y' z' : ℕ) :
    plainExp x y z=plainExp x' y' z' ↔ x=x' ∧ y=y' ∧ z=z' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun p : PlainExp=>p 0) h,
      by simpa using congrArg (fun p : PlainExp=>p 1) h,
      by simpa using congrArg (fun p : PlainExp=>p 2) h⟩
  · rintro ⟨rfl,rfl,rfl⟩; rfl
/--
@isnad1 id=iff.0h4v.s7.ad8c4c17282d from=translated src=- shape=5f020e21 vocab=396a2686
-/
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
/--
@isnad1 id=eq.0h3v.s4.0dbccd2b1a12 from=translated src=- shape=8ab8efa9 vocab=ae1ba6a2
-/
theorem plainTriangle_border_exact (r u v : ℕ) :
    plainBorderFinset (plainTriangleRoots r u v)=plainTriangleBorder r u v := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainStandardSet,plainTriangleRoots,Finset.mem_insert,Finset.mem_singleton,
    exists_eq_or_imp,exists_eq_left,plainDivides,Fin.forall_fin_succ,plainExp_zero,
    plainExp_one,plainExp_two,plainPredecessor_apply]
  simp [plainTriangleBorder,plainExp_eq_coordinates]
  omega

/--
@isnad1 id=eq.0h3v.s4.3f17fb47a963 from=translated src=- shape=f35cce93 vocab=8fd11a89
-/
theorem plainTriangle_border_card (r u v : ℕ) :
    (plainBorderFinset (plainTriangleRoots r u v)).card=4 := by
  rw [plainTriangle_border_exact]
  simp [plainTriangleBorder,plainExp_eq]

def plainDominantAxisRoots (r u v : ℕ) : Finset PlainExp :=
  {plainExp r u v,plainExp (r+1) 0 0,plainExp 0 (u+1) 0}
def plainDominantAxisBorder (r u v : ℕ) : Finset PlainExp :=
  {plainExp (r+2) 0 0,plainExp 0 (u+2) 0,plainExp 0 0 (v+1),
    plainExp (r+1) 1 0,plainExp (r+1) 0 1,plainExp 1 (u+1) 0,plainExp 0 (u+1) 1}

/--
@isnad1 id=iff.0h4v.s8.b09ddaaf45a3 from=translated src=- shape=80b40084 vocab=23869a68
-/
theorem plainDominantAxis_standard (r u v : ℕ) (p : PlainExp) :
    p ∈ plainStandardSet (plainDominantAxisRoots r u v) ↔
      (p 0≤r ∧ p 1≤u ∧ p 2≤v) ∨
      (p 0≤r+1 ∧ p 1=0 ∧ p 2=0) ∨ (p 0=0 ∧ p 1≤u+1 ∧ p 2=0) := by
  simp [plainStandardSet,plainDominantAxisRoots,plainDivides,Fin.forall_fin_succ]

set_option maxHeartbeats 1000000 in
/--
@isnad1 id=eq.3h3v.s5.2fc465692798 from=translated src=- shape=f193c881 vocab=af6672c4
-/
theorem plainDominantAxis_border_exact (r u v : ℕ) (hr : 0<r) (hu : 0<u) (hv : 0<v) :
    plainBorderFinset (plainDominantAxisRoots r u v)=plainDominantAxisBorder r u v := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainDominantAxis_standard,Fin.forall_fin_succ,plainPredecessor_apply]
  by_cases hz : p 2=0 <;> by_cases hx : p 0=0 <;> by_cases hy : p 1=0
  all_goals simp [plainDominantAxisBorder,plainExp_eq_coordinates,hz,hx,hy]
  all_goals omega

/--
@isnad1 id=eq.3h3v.s5.6fd4911b6de5 from=translated src=- shape=e20f2239 vocab=b3ab0b4c
-/
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

/--
@isnad1 id=iff.2h6v.s8.a6b0709d811c from=translated src=- shape=c00e7652 vocab=d173b275
-/
theorem plainPlaneAxis_standard (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (p : PlainExp) :
    p ∈ plainStandardSet (plainPlaneAxisRoots r u s v h) ↔
      (p 2 = 0 ∧ p 0 ≤ u ∧ p 1 ≤ v ∧ (p 0 ≤ r ∨ p 1 ≤ s)) ∨
      (p 0 = 0 ∧ p 1 = 0 ∧ p 2 ≤ h) := by
  simp [plainStandardSet,plainPlaneAxisRoots,plainDivides,Fin.forall_fin_succ]
  omega

set_option maxHeartbeats 1000000 in
/--
@isnad1 id=eq.3h5v.s5.dc7df73e9362 from=translated src=- shape=2126fb4b vocab=0eac8673
-/
theorem plainPlaneAxis_border_exact (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (hh : 0<h) :
    plainBorderFinset (plainPlaneAxisRoots r u s v h)=plainPlaneAxisBorder r u s v h := by
  ext p
  rw [mem_plainBorderFinset_iff]
  simp only [plainPlaneAxis_standard r u s v h hru hsv,Fin.forall_fin_succ,plainPredecessor_apply]
  by_cases hz : p 2=0 <;> by_cases hx : p 0=0 <;> by_cases hy : p 1=0
  all_goals simp [plainPlaneAxisBorder,plainExp_eq_coordinates,hz,hx,hy]
  all_goals omega

/--
@isnad1 id=eq.3h5v.s5.fc7b55a93a25 from=translated src=- shape=9e821656 vocab=a4bb84e2
-/
theorem plainPlaneAxis_border_card (r u s v h : ℕ) (hru : r<u) (hsv : s<v) (hh : 0<h) :
    (plainBorderFinset (plainPlaneAxisRoots r u s v h)).card=6 := by
  rw [plainPlaneAxis_border_exact r u s v h hru hsv hh]
  have hu : u+1≠1 := by omega
  have hv : v+1≠1 := by omega
  have hn : h+1≠1 := by omega
  simp [plainPlaneAxisBorder,Finset.card_insert_eq_ite,plainExp_eq,hu,hv,hn,Ne.symm hu,Ne.symm hv,Ne.symm hn]

end
end P23.Monomial
