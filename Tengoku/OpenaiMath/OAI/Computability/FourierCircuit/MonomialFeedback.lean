import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.PivotJoin

namespace OAI

section
namespace ExactFourier.MatrixPrice
open scoped Matrix Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem source_shear (p : MatrixPrice) (U V : Matrix α α ℂ) (hU : IsUnit U) (hV : IsUnit V)
    (i j : α) (hij : i≠j) (c : ℂ) :
    p.value (V*(Matrix.transvection i j c*U)⁻¹)≤p.value (V*U⁻¹)+1 := by
  have hE := transvection_isUnit i j hij c
  rw [Matrix.mul_inv_rev,← Matrix.mul_assoc]
  have hh := p.mul_le (V*U⁻¹) (Matrix.transvection i j c)⁻¹
    (hV.mul (Matrix.isUnit_nonsing_inv_iff.mpr hU)) (Matrix.isUnit_nonsing_inv_iff.mpr hE)
  rw [p.inverse _ hE] at hh
  have hhE := p.transvection_le_one i j hij c
  linarith

end ExactFourier.MatrixPrice

end

section
namespace ExactFourier.DensePair
open scoped Matrix

end ExactFourier.DensePair

end

section
noncomputable section
namespace ExactFourier.DensePair
open scoped Matrix Kronecker

def rowY : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def rowX : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
def delta (l : ℂ) : Fin 4 → ℂ := ![-1,1,l,-l]
def signs : Fin 4 → ℂ := ![1,-1,1,-1]
def rankOne (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  1+(Matrix.of fun i j => delta l i*signs j/(1-l))
def scaled (l : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![l,1,1,1;1,l,1,1;1,1,l⁻¹,1;1,1,1,l⁻¹]
def scaled2 (u : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,u,u,1;u,1,u,1;u,u,u^2,1;1,1,1,1]
def B (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,1;1,u]

theorem rankOne_mul (l : ℂ) (hl1 : l≠1) :
    rankOne l*(Y6 l).submatrix rowY (Equiv.refl _)=
      (X l).submatrix rowX (Equiv.refl _) := by
  have h : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl1)
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rankOne,delta,signs,Y6,X,rowY,rowX,Fin.sum_univ_succ,
      Matrix.submatrix_apply,Matrix.one_apply] <;> field_simp <;> ring

def left1 (l : ℂ) : Fin 4 → ℂ := fun i => (1-l)/delta l i

theorem left1_ne (l : ℂ) (hl : l≠0) (hl1 : l≠1) : ∀ i,left1 l i≠0 := by
  intro i
  fin_cases i <;> simp [left1,delta,hl,sub_ne_zero.mpr (Ne.symm hl1)]

theorem signs_ne : ∀ i,signs i≠0 := by intro i; fin_cases i <;> norm_num [signs]

theorem scale1 (l : ℂ) (hl : l≠0) (hl1 : l≠1) :
    Matrix.diagonal (left1 l)*rankOne l*Matrix.diagonal signs=scaled l := by
  have h : 1-l≠0 := sub_ne_zero.mpr (Ne.symm hl1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,rankOne,left1,delta,signs,scaled
      ] <;> field_simp <;> ring

def left2 (l : ℂ) : Fin 4 → ℂ := ![l⁻¹,l⁻¹,l⁻¹,1]
def right2 (l : ℂ) : Fin 4 → ℂ := ![1,1,1,l]
theorem left2_ne (l : ℂ) (hl : l≠0) : ∀ i,left2 l i≠0 := by
  intro i; fin_cases i <;> simp [left2,hl]
theorem right2_ne (l : ℂ) (hl : l≠0) : ∀ i,right2 l i≠0 := by
  intro i; fin_cases i <;> simp [right2,hl]

theorem scale2 (l : ℂ) (hl : l≠0) :
    Matrix.diagonal (left2 l)*scaled l*Matrix.diagonal (right2 l)=scaled2 l⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul,Matrix.mul_diagonal,left2,right2,scaled,scaled2,hl,pow_two]

def bitsRow : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(1,0),(0,1),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 1) else (if p.2=0 then 0 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

def bitsCol : (Fin 4)≃(Fin 2×Fin 2) where
  toFun := ![(0,1),(1,0),(1,1),(0,0)]
  invFun := fun p => if p.1=0 then (if p.2=0 then 3 else 0) else (if p.2=0 then 1 else 2)
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; fin_cases a <;> fin_cases b <;> rfl

theorem tensor_scaled (u : ℂ) : (B u⊗ₖB u).submatrix bitsRow bitsCol=scaled2 u := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [B,bitsRow,bitsCol,scaled2,Matrix.submatrix_apply,pow_two]

theorem B_unit (u : ℂ) (hu : u≠1) : IsUnit (B u) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero]
  simpa [B,Matrix.det_fin_two] using sub_ne_zero.mpr hu

end ExactFourier.DensePair

end
end

section
namespace ExactFourier.DensePair
open scoped Matrix Kronecker

end ExactFourier.DensePair

end

section
noncomputable section
namespace ExactFourier.Embedded
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

abbrev complement (e : β ↪ α) := {a : α // a∉Set.range e}
instance (e : β ↪ α) : Fintype (complement e) := Fintype.ofFinite _
instance (e : β ↪ α) : DecidableEq (complement e) := Classical.decEq _

def coordinates (e : β ↪ α) : β⊕complement e ≃ α := by
  classical
  letI : DecidablePred (fun a => a∈Set.range e) := Classical.decPred _
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range e))

@[simp] theorem coordinates_inl
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) (i : β) : coordinates e (Sum.inl i)=e i := rfl
@[simp] theorem coordinates_inr
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : β ↪ α) (i : complement e) : coordinates e (Sum.inr i)=i.val := rfl

def matrix (e : β ↪ α) (A : Matrix β β ℂ) : Matrix α α ℂ :=
  Matrix.reindex (coordinates e) (coordinates e) (Matrix.fromBlocks A 0 0 (1 : Matrix (complement e) (complement e) ℂ))

theorem unit (e : β ↪ α) (A : Matrix β β ℂ) (hA : IsUnit A) : IsUnit (matrix e A) :=
  TensorTools.unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,isUnit_one⟩)

theorem price (p : MatrixPrice) (e : β ↪ α) (A : Matrix β β ℂ) (hA : IsUnit A) :
    p.value (matrix e A)=p.value A := by
  rw [matrix,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA,isUnit_one⟩),p.identity_pad _ hA]

def pair (i j : α) (hij : i≠j) : Fin 2 ↪ α where
  toFun := fun a => if a=0 then i else j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

@[simp] theorem pair_zero
    {α : Type} [Fintype α] [DecidableEq α] (i j : α) (hij : i≠j) : pair i j hij 0=i := rfl
@[simp] theorem pair_one
    {α : Type} [Fintype α] [DecidableEq α] (i j : α) (hij : i≠j) : pair i j hij 1=j := by change (if (1 : Fin 2)=0 then i else j)=j; simp

theorem complement_ne_pair (i j : α) (hij : i≠j) (a : complement (pair i j hij)) :
    a.val≠i ∧ a.val≠j := by
  constructor
  · intro h; exact a.property ⟨0,h.symm⟩
  · intro h; apply a.property; exact ⟨1,by simpa using h.symm⟩

theorem pair_matrix (i j : α) (hij : i≠j) (s t : ℂ) :
    matrix (pair i j hij) (!![1,s;t,1] : Matrix (Fin 2) (Fin 2) ℂ)=
      1+Matrix.single i j s+Matrix.single j i t := by
  ext a b
  obtain ⟨a,rfl⟩ := (coordinates (pair i j hij)).surjective a
  obtain ⟨b,rfl⟩ := (coordinates (pair i j hij)).surjective b
  have he (a b : Fin 2⊕complement (pair i j hij)) :
      matrix (pair i j hij) (!![1,s;t,1]) (coordinates (pair i j hij) a)
      (coordinates (pair i j hij) b)=
      Matrix.fromBlocks (!![1,s;t,1]) 0 0 (1 : Matrix (complement (pair i j hij)) (complement (pair i j hij)) ℂ) a b := by
    simp [matrix,Matrix.reindex_apply]
  rw [he]
  rcases a with a|a <;> rcases b with b|b
  · fin_cases a <;> fin_cases b <;> simp [Matrix.single,hij,Ne.symm hij]
  · have ha := complement_ne_pair i j hij b
    fin_cases a <;> simp [Matrix.single,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    fin_cases b <;> simp [Matrix.single,ha.1,ha.2,Ne.symm ha.1,Ne.symm ha.2]
  · have ha := complement_ne_pair i j hij a
    have hb := complement_ne_pair i j hij b
    simp [Matrix.single,Matrix.one_apply,Ne.symm ha.1,Ne.symm ha.2,Ne.symm hb.1,Ne.symm hb.2,Subtype.ext_iff]

end ExactFourier.Embedded

end
end

end OAI
