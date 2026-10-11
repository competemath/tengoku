import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.DiagonalBlocks

namespace OAI

section
/-! Entrywise regular rational matrices and a common scalar denominator.
Regularity is absence of a pole: the reduced polynomial denominator is nonzero
at the point. Evaluation is only claimed on this domain. -/
namespace ExactFourier.RationalMatrix
open Polynomial
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def eval (X : Matrix α α (RatFunc ℂ)) (s : ℂ) : Matrix α α ℂ :=
  X.map (RatFunc.eval (RingHom.id ℂ) s)

def RegularAt (X : Matrix α α (RatFunc ℂ)) (s : ℂ) : Prop :=
  ∀ i j, (X i j).denom.eval s≠0

noncomputable def denominator (X : Matrix α α (RatFunc ℂ)) : Polynomial ℂ :=
  ∏ v : α×α, (X v.1 v.2).denom

noncomputable def numerator (X : Matrix α α (RatFunc ℂ)) : Matrix α α (Polynomial ℂ) :=
  fun i j => (X i j).num * ∏ v ∈ (Finset.univ : Finset (α×α)).erase (i,j), (X v.1 v.2).denom

theorem denominator_factor (X : Matrix α α (RatFunc ℂ)) (i j : α) :
    denominator X=(X i j).denom *
      ∏ v ∈ (Finset.univ : Finset (α×α)).erase (i,j),(X v.1 v.2).denom :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ (i,j))).symm

theorem denominator_eval_ne_zero
    {α : Type} [Fintype α] [DecidableEq α] (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : RegularAt X s) : (denominator X).eval s≠0 := by
  rw [denominator,Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => hX v.1 v.2)

theorem regular_of_denominator (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : (denominator X).eval s≠0) : RegularAt X s := by
  intro i j
  rw [denominator_factor X i j,Polynomial.eval_mul] at hX
  exact (mul_ne_zero_iff.mp hX).1

theorem eval_clearing (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : RegularAt X s) :
    (numerator X).map (Polynomial.eval s)=(denominator X).eval s • eval X s := by
  ext i j
  simp only [numerator,Matrix.map_apply,Polynomial.eval_mul,Matrix.smul_apply,smul_eq_mul,
    eval,RatFunc.eval,Polynomial.eval₂_id]
  rw [denominator_factor X i j,Polynomial.eval_mul]
  field_simp [hX i j]

end ExactFourier.RationalMatrix

end

section
namespace ExactFourier.MatrixPrice
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.MatrixPrice

end

section
noncomputable section
namespace ExactFourier.MatrixPrice
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.MatrixPrice

end
end

section
noncomputable section
namespace ExactFourier.CayleyLimit
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

def active (a : α → ℂ) : Finset α := Finset.univ.filter (fun i=>a i≠0)
def denominator (a : α → ℂ) : Polynomial ℂ := ∏ i∈active a,(X-Polynomial.C (a i))
def except (a : α → ℂ) (i : α) : Polynomial ℂ := ∏ j∈(active a).erase i,(X-Polynomial.C (a j))
def numerator (a : α → ℂ) (i : α) : Polynomial ℂ :=
  if a i=0 then denominator a else (X+Polynomial.C (a i))*except a i
def sign (a : α → ℂ) (i : α) : ℂ := if a i=0 then 1 else -1

theorem denominator_factor (a : α → ℂ) (i : α) (hi : a i≠0) :
    denominator a=(X-Polynomial.C (a i))*except a i := by
  exact (Finset.mul_prod_erase _ _ (by simp [active,hi])).symm

theorem denominator_zero
    {α : Type} [Fintype α] [DecidableEq α] (a : α → ℂ) : (denominator a).eval 0≠0 := by
  rw [denominator,Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have h : a i≠0 := (Finset.mem_filter.mp hi).2
  simpa using neg_ne_zero.mpr h

theorem numerator_zero (a : α → ℂ) (i : α) :
    (numerator a i).eval 0=(denominator a).eval 0*sign a i := by
  by_cases hi : a i=0
  · simp [numerator,sign,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp [sign,hi]

theorem numerator_identity (a : α → ℂ) (i : α) (s : ℂ) (hs : s≠0) :
    (numerator a i).eval s*(1-s⁻¹*a i)=(denominator a).eval s*(1+s⁻¹*a i) := by
  by_cases hi : a i=0
  · simp [numerator,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp only [eval_mul,eval_add,eval_sub,eval_X,eval_C]
    field_simp

def polynomial (U : Matrix α α ℂ) (a : α → ℂ) : Matrix α α (Polynomial ℂ) :=
  U.map Polynomial.C*Matrix.diagonal (numerator a)*(U⁻¹).map Polynomial.C

theorem eval_polynomial (U : Matrix α α ℂ) (a : α → ℂ) (s : ℂ) :
    (polynomial U a).map (evalRingHom s)=Similarity.conj U (Matrix.diagonal (fun i=>(numerator a i).eval s)) := by
  have hc (V : Matrix α α ℂ) : (V.map Polynomial.C).map (evalRingHom s)=V := by ext i j; simp
  rw [polynomial,Matrix.map_mul,Matrix.map_mul,hc,hc]
  have hd : (Matrix.diagonal (numerator a)).map (evalRingHom s)=Matrix.diagonal (fun i=>(numerator a i).eval s) := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [hd]; rfl

theorem eval_zero (U : Matrix α α ℂ) (a : α → ℂ) :
    (polynomial U a).map (evalRingHom 0)=(denominator a).eval 0•Similarity.conj U (Matrix.diagonal (sign a)) := by
  rw [eval_polynomial]
  simp_rw [numerator_zero]
  rw [← Similarity.smul]
  congr 1
  ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]

theorem eval_as_cayley (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s≠0)
    (hm : IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a))) :
    (polynomial U a).map (evalRingHom s)=(denominator a).eval s•
      MatrixPrice.cayley (Similarity.conj U (Matrix.diagonal a)) s⁻¹ := by
  apply hm.mul_right_cancel
  rw [eval_polynomial,Similarity.diagonal_linear_sub U hU,Similarity.mul U _ _ hU]
  rw [MatrixPrice.cayley,Matrix.smul_mul,← Similarity.diagonal_linear_sub U hU,Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hm),
    Similarity.diagonal_linear U hU,← Similarity.smul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simpa using numerator_identity a i s hs
  · simp [Matrix.diagonal,h]

def bad (a : α → ℂ) : Finset ℂ := insert 0 (Finset.univ.image a∪Finset.univ.image (fun i=>-a i))

theorem generic_units (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s∉bad a) : s≠0 ∧ (denominator a).eval s≠0 ∧
    IsUnit (1+s⁻¹•Similarity.conj U (Matrix.diagonal a)) ∧
    IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a)) := by
  classical
  have hs0 : s≠0 := by intro h; exact hs (by simp [bad,h])
  have hspos (i : α) : s≠a i := by intro h; exact hs (by simp [bad,h])
  have hsneg (i : α) : s≠-a i := by intro h; exact hs (by simp [bad,h])
  have hq : (denominator a).eval s≠0 := by
    rw [denominator,Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa using sub_ne_zero.mpr (hspos i))
  have hp (i : α) : 1+s⁻¹*a i≠0 := by
    intro hh
    have he : s+a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hsneg i (eq_neg_of_add_eq_zero_left he)
  have hm (i : α) : 1-s⁻¹*a i≠0 := by
    intro hh
    have he : s-a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hspos i (sub_eq_zero.mp he)
  refine ⟨hs0,hq,?_,?_⟩
  · rw [Similarity.diagonal_linear U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hp i))))
  · rw [Similarity.diagonal_linear_sub U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hm i))))

end ExactFourier.CayleyLimit

end
end

section
noncomputable section
namespace ExactFourier.CayleyLimit
variable {α : Type} [Fintype α] [DecidableEq α]

def reciprocal (a : α → ℂ) (i : α) : ℂ := if a i=0 then 0 else 2/(a i)

theorem sign_square (a : α → ℂ) : Matrix.diagonal (sign a)*Matrix.diagonal (sign a)=(1 : Matrix α α ℂ) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simp [sign]; split_ifs <;> norm_num
  · simp [Matrix.diagonal,h]

theorem reflection_square (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal (sign a))*Similarity.conj U (Matrix.diagonal (sign a))=1 := by
  rw [Similarity.mul U _ _ hU,sign_square,Similarity.one U hU]

theorem killed_sum (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal a)*(1+Similarity.conj U (Matrix.diagonal (sign a)))=0 := by
  rw [← Similarity.one U hU,← Similarity.add,Similarity.mul U _ _ hU]
  rw [mul_add,mul_one,Matrix.diagonal_mul_diagonal]
  have hh : Matrix.diagonal a+Matrix.diagonal (fun i=>a i*sign a i)=0 := by
    ext i j
    by_cases h : i=j
    · subst j; simp [sign]; split_ifs <;> simp_all
    · simp [Matrix.diagonal,h]
  rw [hh,Similarity.zero]

theorem difference_factor (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    1-Similarity.conj U (Matrix.diagonal (sign a))=
      Similarity.conj U (Matrix.diagonal a)*Similarity.conj U (Matrix.diagonal (reciprocal a)) := by
  rw [Similarity.mul U _ _ hU,← Similarity.one U hU,← Similarity.sub]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j
    by_cases hi : a i=0 <;> simp [sign,reciprocal,hi]
    field_simp
    ring
  · simp [Matrix.diagonal,h]

theorem reflection_symm (U : Matrix α α ℂ) (hi : U⁻¹=U.transpose) (a : α → ℂ) :
    (Similarity.conj U (Matrix.diagonal (sign a))).IsSymm := by
  change (Similarity.conj U (Matrix.diagonal (sign a))).transpose=_
  simp [Similarity.conj,hi,Matrix.transpose_mul,mul_assoc]

end ExactFourier.CayleyLimit

end
end

end OAI
