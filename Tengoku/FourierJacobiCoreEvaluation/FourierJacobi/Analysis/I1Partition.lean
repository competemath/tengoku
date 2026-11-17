import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.I1Complete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/abhisaha-git/fourier-jacobi-core-evaluation@fb2b788d6271, `FourierJacobi/Analysis/I1Partition.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Exact disjoint and exhaustive partition of the complete I1 lattice,
including every cancellation depth and both parity refinements. -/
namespace FourierJacobi.Analysis
set_option maxHeartbeats 2000000

def i1CellIndex (p : LatticeIndex) : Fin 17 :=
  let k := p.1; let j := p.2.1; let h := p.2.2.1; let c := p.2.2.2
  if 1 ≤ k then
    if -2*k ≤ j then
      if -k ≤ h then 0 else 1
    else if h < k+j then 7
    else if j ≤ 2*h then
      if j % 2 = 0 then 2 else 3
    else if 2*h = j-1 then
      if c = 0 then 4 else 5
    else 6
  else if 0 ≤ j then
    if h < 0 then 10
    else if k = 0 then 8 else 9
  else if h < j then 16
  else if j ≤ 2*h then
    if j % 2 = 0 then 11 else 12
  else if 2*h = j-1 then
    if c = 0 then 13 else 14
  else 15

abbrev I1Cell (i : Fin 17) := {p : LatticeIndex // i1CellIndex p = i}

/-- The library fiber equivalence proves both inverse laws.-/
def i1PartitionEquiv : (Σ i : Fin 17, I1Cell i) ≃ LatticeIndex :=
  Equiv.sigmaFiberEquiv i1CellIndex

/--
@isnad1 id=eq.0h1v.s7.f716a12e6a5d from=translated src=- shape=75609859 vocab=3f712798
-/
@[simp] theorem i1PartitionEquiv_val (p : Σ i : Fin 17, I1Cell i) :
    i1PartitionEquiv p = p.2.val := rfl

/--
@isnad1 id=iff.0h4v.s6.d4c1bee53ce2 from=translated src=- shape=3bd1f238 vocab=c1fc460c
-/
theorem i1r1_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 0 ↔ (1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r1DepthEquiv : (I1R1Row × ℕ) ≃ I1Cell 0 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r1_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r1_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r1_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.8edabe981d89 from=translated src=- shape=b5cb9ee5 vocab=c6a901e0
-/
@[simp] theorem i1r1DepthEquiv_val (p : I1R1Row × ℕ) :
    (i1r1DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.e324945cbe57 from=translated src=- shape=e894ec88 vocab=2e123906
-/
theorem i1r2_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 1 ↔ (1 ≤ k ∧ -2 * k ≤ j ∧ h < -k) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r2DepthEquiv : (I1R2Row × ℕ) ≃ I1Cell 1 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r2_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r2_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r2_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.f6cd99ba5051 from=translated src=- shape=d7094da6 vocab=7c99b0d8
-/
@[simp] theorem i1r2DepthEquiv_val (p : I1R2Row × ℕ) :
    (i1r2DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s7.824ce5c2edf4 from=translated src=- shape=5d3b7b99 vocab=25509652
-/
theorem i1r3ae_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 2 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r3aeDepthEquiv : (I1R3AERow × ℕ) ≃ I1Cell 2 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r3ae_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3ae_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3ae_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s9.dd2d23d99f44 from=translated src=- shape=f824c1b9 vocab=342f59b0
-/
@[simp] theorem i1r3aeDepthEquiv_val (p : I1R3AERow × ℕ) :
    (i1r3aeDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s7.4cfa5dc1ab02 from=translated src=- shape=5d3b7b99 vocab=25509652
-/
theorem i1r3ao_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 3 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r3aoDepthEquiv : (I1R3AORow × ℕ) ≃ I1Cell 3 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r3ao_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3ao_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3ao_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s9.6517244e12c1 from=translated src=- shape=f824c1b9 vocab=c2522c54
-/
@[simp] theorem i1r3aoDepthEquiv_val (p : I1R3AORow × ℕ) :
    (i1r3aoDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s7.387b4e7ff075 from=translated src=- shape=0d7c1a8f vocab=836d122c
-/
theorem i1r3b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 4 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1) ∧ c = 0 := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r3bDepthEquiv : (I1R3BRow) ≃ I1Cell 4 where
  toFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2,0), by
    apply (i1r3b_cell_iff _ _ _ _).mpr
    exact ⟨p.property, by omega⟩⟩
  invFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3b_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3b_cell_iff k j h c).mp hp
    change (k,j,h,0) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) hh.2.symm

/--
@isnad1 id=eq.0h1v.s9.ca523f258ca1 from=translated src=- shape=eb180bfa vocab=c002737e
-/
@[simp] theorem i1r3bDepthEquiv_val (p : I1R3BRow) :
    (i1r3bDepthEquiv p).val = (p.val.1,p.val.2.1,p.val.2.2,0) := rfl

/--
@isnad1 id=iff.0h4v.s7.078628168f01 from=translated src=- shape=ba40f7a5 vocab=836d122c
-/
theorem i1r3c_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 5 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1) ∧ 1 ≤ c := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r3cDepthEquiv : (I1R3CRow × ℕ) ≃ I1Cell 5 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1), by
    apply (i1r3c_cell_iff _ _ _ _).mpr
    exact ⟨p.1.property, by omega⟩⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3c_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩, p.val.2.2.2 - 1)
  left_inv p := by
    rcases p with ⟨p,c⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3c_cell_iff k j h c).mp hp
    change (k,j,h,c-1+1) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) (Nat.sub_add_cancel hh.2)

/--
@isnad1 id=eq.0h1v.s9.747a09d7cfa3 from=translated src=- shape=e259dd4b vocab=a74597cf
-/
@[simp] theorem i1r3cDepthEquiv_val (p : I1R3CRow × ℕ) :
    (i1r3cDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1) := rfl

/--
@isnad1 id=iff.0h4v.s6.df85b05a8178 from=translated src=- shape=0d7b8925 vocab=836d122c
-/
theorem i1r4_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 6 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r4DepthEquiv : (I1R4Row × ℕ) ≃ I1Cell 6 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r4_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r4_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r4_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s9.98704366b778 from=translated src=- shape=74591b0f vocab=0c0c71e6
-/
@[simp] theorem i1r4DepthEquiv_val (p : I1R4Row × ℕ) :
    (i1r4DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.4b8d8771e06a from=translated src=- shape=7a0f0a0c vocab=4b41de12
-/
theorem i1r5_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 7 ↔ (1 ≤ k ∧ j < -2*k ∧ h < k+j) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r5DepthEquiv : (I1R5Row × ℕ) ≃ I1Cell 7 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r5_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r5_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r5_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.2bcf427070bc from=translated src=- shape=f824534a vocab=1b9c1294
-/
@[simp] theorem i1r5DepthEquiv_val (p : I1R5Row × ℕ) :
    (i1r5DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.6657b4e407d0 from=translated src=- shape=2ab2201e vocab=1f15e154
-/
theorem i1r6a_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 8 ↔ (k = 0 ∧ 0 ≤ j ∧ 0 ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r6aDepthEquiv : (I1R6ARow × ℕ) ≃ I1Cell 8 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r6a_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r6a_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r6a_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.3f7c29a39c2d from=translated src=- shape=c95aec6b vocab=76d889e1
-/
@[simp] theorem i1r6aDepthEquiv_val (p : I1R6ARow × ℕ) :
    (i1r6aDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.a774bdf63084 from=translated src=- shape=4dd7578d vocab=70731415
-/
theorem i1r6b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 9 ↔ (k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r6bDepthEquiv : (I1R6BRow × ℕ) ≃ I1Cell 9 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r6b_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r6b_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r6b_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.d1d1beededb9 from=translated src=- shape=43345db6 vocab=0c73975b
-/
@[simp] theorem i1r6bDepthEquiv_val (p : I1R6BRow × ℕ) :
    (i1r6bDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.0cd291897c93 from=translated src=- shape=b8d3ccd9 vocab=53e1cd8d
-/
theorem i1r7_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 10 ↔ (k ≤ 0 ∧ 0 ≤ j ∧ h < 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r7DepthEquiv : (I1R7Row × ℕ) ≃ I1Cell 10 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r7_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r7_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r7_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.51cf92d4e20a from=translated src=- shape=9dcf1395 vocab=50e26a46
-/
@[simp] theorem i1r7DepthEquiv_val (p : I1R7Row × ℕ) :
    (i1r7DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.4addfe3d3922 from=translated src=- shape=ccd9b386 vocab=1b9dfa2c
-/
theorem i1r8ae_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 11 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r8aeDepthEquiv : (I1R8AERow × ℕ) ≃ I1Cell 11 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r8ae_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8ae_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8ae_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s9.9860b61ccbba from=translated src=- shape=2d441597 vocab=ca52f842
-/
@[simp] theorem i1r8aeDepthEquiv_val (p : I1R8AERow × ℕ) :
    (i1r8aeDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.e8731a5d73e1 from=translated src=- shape=ccd9b386 vocab=1b9dfa2c
-/
theorem i1r8ao_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 12 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r8aoDepthEquiv : (I1R8AORow × ℕ) ≃ I1Cell 12 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r8ao_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8ao_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8ao_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s9.fad90ad28e97 from=translated src=- shape=2d441597 vocab=6bd22aaa
-/
@[simp] theorem i1r8aoDepthEquiv_val (p : I1R8AORow × ℕ) :
    (i1r8aoDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.b6b066e78754 from=translated src=- shape=865c4cc8 vocab=9b3531a6
-/
theorem i1r8b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 13 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1) ∧ c = 0 := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r8bDepthEquiv : (I1R8BRow) ≃ I1Cell 13 where
  toFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2,0), by
    apply (i1r8b_cell_iff _ _ _ _).mpr
    exact ⟨p.property, by omega⟩⟩
  invFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8b_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8b_cell_iff k j h c).mp hp
    change (k,j,h,0) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) hh.2.symm

/--
@isnad1 id=eq.0h1v.s8.644947ff9a98 from=translated src=- shape=3f745ee7 vocab=e30155d2
-/
@[simp] theorem i1r8bDepthEquiv_val (p : I1R8BRow) :
    (i1r8bDepthEquiv p).val = (p.val.1,p.val.2.1,p.val.2.2,0) := rfl

/--
@isnad1 id=iff.0h4v.s6.e6ad2adb4aed from=translated src=- shape=d70a5af2 vocab=9b3531a6
-/
theorem i1r8c_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 14 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1) ∧ 1 ≤ c := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r8cDepthEquiv : (I1R8CRow × ℕ) ≃ I1Cell 14 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1), by
    apply (i1r8c_cell_iff _ _ _ _).mpr
    exact ⟨p.1.property, by omega⟩⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8c_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩, p.val.2.2.2 - 1)
  left_inv p := by
    rcases p with ⟨p,c⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8c_cell_iff k j h c).mp hp
    change (k,j,h,c-1+1) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) (Nat.sub_add_cancel hh.2)

/--
@isnad1 id=eq.0h1v.s8.df8fe1b6f6d8 from=translated src=- shape=629be65e vocab=135d2ae3
-/
@[simp] theorem i1r8cDepthEquiv_val (p : I1R8CRow × ℕ) :
    (i1r8cDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1) := rfl

/--
@isnad1 id=iff.0h4v.s6.65dc498d420f from=translated src=- shape=9a2bbef5 vocab=9b3531a6
-/
theorem i1r9_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 15 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r9DepthEquiv : (I1R9Row × ℕ) ≃ I1Cell 15 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r9_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r9_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r9_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.3da97eeda900 from=translated src=- shape=d1b4481b vocab=bd2a8e2e
-/
@[simp] theorem i1r9DepthEquiv_val (p : I1R9Row × ℕ) :
    (i1r9DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

/--
@isnad1 id=iff.0h4v.s6.9e8a8fe6af5b from=translated src=- shape=59a01a3a vocab=53e1cd8d
-/
theorem i1r10_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 16 ↔ (k ≤ 0 ∧ j < 0 ∧ h < j) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega

def i1r10DepthEquiv : (I1R10Row × ℕ) ≃ I1Cell 16 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r10_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r10_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r10_cell_iff k j h c).mp hp
    rfl

/--
@isnad1 id=eq.0h1v.s8.d5dae913fe58 from=translated src=- shape=c4c68b2d vocab=db4303a3
-/
@[simp] theorem i1r10DepthEquiv_val (p : I1R10Row × ℕ) :
    (i1r10DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl

end FourierJacobi.Analysis
