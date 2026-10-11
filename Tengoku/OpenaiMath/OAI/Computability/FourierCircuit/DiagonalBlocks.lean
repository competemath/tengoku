import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.SymmetricLaplacian

namespace OAI

section
namespace ExactFourier
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def diagonalBlocks {t : ℕ} (A : Fin t → Matrix α α ℂ) :
    Matrix (Fin t × α) (Fin t × α) ℂ :=
  fun i j => if i.1=j.1 then A i.1 i.2 j.2 else 0

namespace MatrixPrice

theorem diagonal_blocks (p : MatrixPrice) (t : ℕ) (A : Fin t → Matrix α α ℂ)
    (hA : ∀ i, IsUnit (A i)) :
    IsUnit (diagonalBlocks A) ∧ p.value (diagonalBlocks A)=∑ i, p.value (A i) := by
  have hu := (p.blocks_lower t (diagonalBlocks A) A hA
    (by intros; simp [diagonalBlocks])
    (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
  refine ⟨hu,?_⟩
  induction t with
  | zero =>
    have he : diagonalBlocks A=1 := by ext i j; exact Fin.elim0 i.1
    rw [he,p.one]; simp
  | succ t ih =>
    have hD : IsUnit (diagonalBlocks (fun i : Fin t => A i.succ)) :=
      (p.blocks_lower t _ _ (fun i => hA i.succ)
        (by intros; simp [diagonalBlocks])
        (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
    have he : Matrix.reindex (timeSplit t α) (timeSplit t α) (diagonalBlocks A)=
        Matrix.fromBlocks (A 0) 0 0 (diagonalBlocks (fun i : Fin t => A i.succ)) := by
      ext i j
      rcases i with a|⟨i,a⟩ <;> rcases j with b|⟨j,b⟩ <;>
        simp [Matrix.reindex_apply,Matrix.submatrix_apply,timeSplit,diagonalBlocks,
          Ne.symm (Fin.succ_ne_zero _)]
    rw [← p.reindex (timeSplit t α) _ hu,he,p.directSum _ _ (hA 0) hD,
      ih _ (fun i => hA i.succ) hD,Fin.sum_univ_succ]

end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped BigOperators Kronecker
noncomputable def fourier (t : ℕ) (ω : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => ω^(i.val*j.val)

@[simp] theorem fourier_mulVec (t : ℕ) (ω : ℂ) (x : Fin t → ℂ) :
    (fourier t ω).mulVec x=RadixTwo.eval t ω x := rfl

theorem fourier_unit (t : ℕ) (ht : 0<t) (ω : ℂ) (hω : IsPrimitiveRoot ω t) :
    IsUnit (fourier t ω) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  rw [fourier_mulVec,fourier_mulVec] at h
  have hh := congrArg (RadixTwo.eval t ω⁻¹) h
  rw [RadixTwo.eval_inverse ht ω hω,RadixTwo.eval_inverse ht ω hω] at hh
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt ht : (t:ℂ)≠0) (congrFun hh i)

noncomputable def matrix (t : ℕ) (ω a : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun i j => (a*ω^i.val)^j.val

theorem matrix_eq (t : ℕ) (ω a : ℂ) :
    matrix t ω a=fourier t ω*Matrix.diagonal (fun j : Fin t => a^j.val) := by
  ext i j
  simp [matrix,fourier,Matrix.mul_diagonal,mul_pow,pow_mul,mul_comm]

theorem matrix_unit (t : ℕ) (ht : 0<t) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω t) (ha : a≠0) : IsUnit (matrix t ω a) := by
  rw [matrix_eq]
  exact (fourier_unit t ht ω hω).mul
    (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun j => isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha))))

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped Kronecker BigOperators

theorem eval_remainder (ℓ f : Polynomial ℂ) (s : ℂ) (hs : ℓ.eval s=0) :
    (f%ₘℓ).eval s=f.eval s := by
  rw [modByMonic_eq_sub_mul_div,eval_sub,eval_mul,hs,zero_mul,sub_zero]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem root_modulus (t : ℕ) (ht : 0<t) (ω a : ℂ) (hω : IsPrimitiveRoot ω t)
    (i : Fin t) : (X^t-C (a^t) : Polynomial ℂ).eval (a*ω^i.val)=0 := by
  obtain ⟨size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp only [eval_sub,eval_pow,eval_X,eval_C,mul_pow,← pow_mul]
  rw [Nat.mul_comm i.val size.succ,pow_mul,hω.pow_eq_one,one_pow,mul_one,sub_self]

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial TensorAxis
open scoped Kronecker BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation

theorem exists_dilation (t : ℕ) (ω : ℂ) (hω : ω≠0) (E : Finset ℂ) :
    ∃ a : ℂ, a≠0 ∧ ∀ i : Fin t, a*ω^i.val ∉ E := by
  classical
  let F : Finset ℂ := insert 0 (Finset.univ.biUnion (fun i : Fin t => E.image (fun s => s/ω^i.val)))
  obtain ⟨a,ha⟩ := F.exists_notMem
  refine ⟨a,?_,?_⟩
  · intro he
    apply ha
    simp [F,he]
  · intro i hi
    apply ha
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨a*ω^i.val,hi,?_⟩⟩
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ hω)

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier
open Filter Topology

theorem exists_dyadic_between (b : ℕ) (hb : 0<b) : ∃ j : ℕ, b≤2^j ∧ 2^j≤2*b := by
  refine ⟨Nat.log 2 b+1,(Nat.lt_pow_succ_log_self (by decide : 1<2) b).le,?_⟩
  have hh := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
  rw [pow_succ]
  omega

theorem fixed_price_of_dyadic_boundary (x y C : ℝ) (hC : 0≤C)
    (h : ∀ k j : ℕ, 0<k →
      (2^j:ℝ)*k*(x-y) ≤ C*((2^j:ℝ)*Real.log (2*2^j)+(k+1:ℝ)^6)) : x≤y := by
  have he (m : ℕ) : x-y ≤ (2*C)*boundaryError m := by
    let b : ℕ := (m+2)^8
    have hb : 0<b := by dsimp [b]; positivity
    obtain ⟨j,hlo,hhi⟩ := exists_dyadic_between b hb
    let T : ℕ := 2^j
    have hTr : 0<(T:ℝ) := by exact_mod_cast (pow_pos (by decide : 0<2) j)
    have hbr : (b:ℝ)=((m:ℝ)+2)^8 := by dsimp [b]; push_cast; rfl
    have hk : 0<(m:ℝ)+1 := by positivity
    have hb1 : (1:ℝ)≤b := by exact_mod_cast (hb : 1≤b)
    have hloR : (b:ℝ)≤T := by exact_mod_cast hlo
    have hhiR : (T:ℝ)≤2*b := by exact_mod_cast hhi
    have hln : Real.log (2*(T:ℝ)) ≤ 2*Real.log (2*b) := by
      have harg : 2*(T:ℝ)≤(2*(b:ℝ))^2 := by nlinarith
      have hh := Real.log_le_log (by positivity : (0:ℝ)<2*T) harg
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    have hln0 : 0≤Real.log (2*(b:ℝ)) := Real.log_nonneg (by linarith)
    have hr : ((m:ℝ)+2)^6 / ((T:ℝ)*((m:ℝ)+1)) ≤
        ((m:ℝ)+2)^6 / ((b:ℝ)*((m:ℝ)+1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hloR hk.le
    have hlog : Real.log (2*(T:ℝ))/((m:ℝ)+1) ≤
        2*Real.log (2*(b:ℝ))/((m:ℝ)+1) := by exact div_le_div_of_nonneg_right hln hk.le
    have herr : Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1)) ≤2*boundaryError m := by
      have hfrac : 0≤((m:ℝ)+2)^6/((b:ℝ)*((m:ℝ)+1)) := by positivity
      dsimp only [boundaryError]
      rw [← hbr]
      rw [mul_div_assoc] at hlog
      nlinarith only [hr,hlog,hfrac]
    have hh := h (m+1) j (by omega)
    have hTR : (2^j:ℝ)=(T:ℝ) := by dsimp [T]; norm_cast
    rw [hTR] at hh
    push_cast at hh
    have hnorm : x-y ≤ C*(Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1))) := by
      have hn : x-y ≤ (C*((T:ℝ)*Real.log (2*T)+((m:ℝ)+2)^6))/((T:ℝ)*((m:ℝ)+1)) :=
        (le_div_iff₀ (mul_pos hTr hk)).mpr (by nlinarith only [hh])
      convert hn using 1 ; field_simp
    calc
      x-y ≤ _ := hnorm
      _ ≤ C*(2*boundaryError m) := mul_le_mul_of_nonneg_left herr hC
      _ = (2*C)*boundaryError m := by ring
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul (2*C)) (Filter.Eventually.of_forall he)
  have : x-y≤0 := by simpa using hh
  linarith

end ExactFourier

end

section
namespace ExactFourier.MatrixPrice
open TensorAxis Polynomial CoefficientTime
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.MatrixPrice

end

end OAI
