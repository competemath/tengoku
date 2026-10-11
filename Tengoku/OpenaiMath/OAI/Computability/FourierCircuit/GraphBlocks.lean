import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.SparseSpectral

namespace OAI

section
noncomputable section
namespace ExactFourier.GraphReflection
variable {α : Type} [Fintype α] [DecidableEq α]

theorem block_relations (B E F G H : Matrix α α ℂ) (hB : IsUnit B)
    (hp : graph B*(1+Matrix.fromBlocks E F G H)=1+Matrix.fromBlocks E F G H)
    (hm : (graph B).transpose*(1-Matrix.fromBlocks E F G H)=-(1-Matrix.fromBlocks E F G H)) :
    B*G=1+E ∧ B*(1+H)=F ∧ B.transpose*F=1-H ∧ B.transpose*(1-E)=G := by
  obtain ⟨unit, rfl⟩ := hB
  have h1 := congrArg Matrix.toBlocks₁₁ hp
  have h2 := congrArg Matrix.toBlocks₁₂ hp
  have h3 := congrArg Matrix.toBlocks₂₂ hm
  have h4 := congrArg Matrix.toBlocks₂₁ hm
  simp only [graph,← Matrix.fromBlocks_one,sub_eq_add_neg,Matrix.fromBlocks_add,
    Matrix.fromBlocks_transpose,Matrix.fromBlocks_neg,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁,Matrix.toBlocks_fromBlocks₁₂,Matrix.toBlocks_fromBlocks₂₁,Matrix.toBlocks_fromBlocks₂₂,
    Matrix.transpose_zero,zero_mul,zero_add,add_zero,zero_add,mul_neg,neg_neg,neg_zero] at h1 h2 h3 h4
  exact ⟨h1,h2,by simpa [sub_eq_add_neg] using neg_inj.mp h3,by simpa [sub_eq_add_neg] using h4⟩

theorem offdiagonal_unit (B E F G H : Matrix α α ℂ) (hB : IsUnit B)
    (hreal : ∀ i j,star (B i j)=B i j)
    (hs : (Matrix.fromBlocks E F G H).IsSymm)
    (hp : graph B*(1+Matrix.fromBlocks E F G H)=1+Matrix.fromBlocks E F G H)
    (hm : (graph B).transpose*(1-Matrix.fromBlocks E F G H)=-(1-Matrix.fromBlocks E F G H)) :
    IsUnit F ∧ IsUnit G := by
  obtain ⟨h1,h2,h3,h4⟩ := block_relations B E F G H hB hp hm
  have hq := gram_unit B hreal
  have he : (1+B.transpose*B)*(1+H)=(2:ℂ)•1 := by
    calc
      _ = 1+H+B.transpose*(B*(1+H)) := by noncomm_ring
      _ = 1+H+(1-H) := by rw [h2,h3]
      _ = _ := by rw [two_smul]; abel
  have hhu : IsUnit (1+H) := by
    have hh : 1+H=(1+B.transpose*B)⁻¹*((2:ℂ)•1) := by
      apply hq.mul_left_cancel
      rw [← mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hq),one_mul,he]
    rw [hh]
    exact (Matrix.isUnit_nonsing_inv_iff.mpr hq).mul (MatrixPrice.scalar_unit _ isUnit_one 2 (by norm_num))
  have hf : IsUnit F := h2 ▸ hB.mul hhu
  refine ⟨hf,?_⟩
  have hgf : G=F.transpose := by
    have hh := congrArg Matrix.toBlocks₁₂ hs
    simpa [Matrix.fromBlocks_transpose] using congrArg Matrix.transpose hh
  rw [hgf]; exact (Matrix.isUnit_transpose _).mpr hf

end ExactFourier.GraphReflection

end
end

section
noncomputable section
namespace ExactFourier.GraphReflection
variable {α : Type} [Fintype α] [DecidableEq α]

theorem diagonalization (B E F G H : Matrix α α ℂ) (hB : IsUnit B) (hG : IsUnit G)
    (h1 : B*G=1+E) (h2 : B*(1+H)=F) (h3 : B.transpose*F=1-H) (h4 : B.transpose*(1-E)=G) :
    hadamard*(swap*Pivot.matrix F E H G)*hadamard⁻¹=
      Matrix.fromBlocks B 0 0 (-B.transpose⁻¹) := by
  let W : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 1 0 H G
  let Z : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks 0 1 F E
  let D : Matrix (α⊕α) (α⊕α) ℂ := Matrix.fromBlocks B 0 0 (-B.transpose⁻¹)
  have hBt : IsUnit B.transpose := (Matrix.isUnit_transpose _).mpr hB
  have hi := Matrix.nonsing_inv_mul B.transpose ((Matrix.isUnit_iff_isUnit_det _).mp hBt)
  have h3' : B.transpose⁻¹*(1-H)=F := by rw [← h3,← mul_assoc,hi,one_mul]
  have h4' : B.transpose⁻¹*G=1-E := by rw [← h4,← mul_assoc,hi,one_mul]
  have hW : IsUnit W := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,hG⟩
  have hv : (swap*Pivot.matrix F E H G)*W=Z := by
    rw [mul_assoc,Pivot.solve F E H G hG]
    simp [swap,Z,Matrix.fromBlocks_multiply]
  have hz : hadamard*Z=D*hadamard*W := by
    dsimp only [hadamard,Z,D,W]
    simp only [Matrix.fromBlocks_multiply,mul_zero,one_mul,mul_one,
      zero_add,add_zero,neg_mul,mul_neg,neg_neg,neg_zero]
    have hh2 : B+B*H=F := by simpa [mul_add] using h2
    have hh3 : -B.transpose⁻¹+B.transpose⁻¹*H= -F := by rw [← h3',mul_sub,mul_one]; abel
    have hh4 : B.transpose⁻¹*G=1-E := h4'
    rw [h1,hh2,hh3,hh4]
    simp [sub_eq_add_neg,add_comm]
  have he : hadamard*(swap*Pivot.matrix F E H G)=D*hadamard := by
    apply hW.mul_right_cancel
    rw [mul_assoc,hv,hz]
  rw [he,mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hadamard_unit),mul_one]

end ExactFourier.GraphReflection

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

def weight : (m : ℕ) → Bits m → ℕ
  | 0, _ => 0
  | m+1, .inl i => weight m i
  | m+1, .inr i => weight m i+1

theorem D_weight (m : ℕ) (i j : Bits m) (h : D m i j≠0) :
    weight m i=weight m j+1 := by
  induction m with
  | zero => exact False.elim (h rfl)
  | succ m ih =>
    rcases i with i|i <;> rcases j with j|j
    · exact ih i j h
    · exact False.elim (h rfl)
    · have hij : i=j := by simpa [D,Matrix.one_apply] using h
      subst j; rfl
    · change weight m i+1=weight m j+1+1
      change -(D m i j)≠0 at h
      rw [ih i j (neg_ne_zero.mp h)]

def V : Matrix (Fin 2) (Fin 2) ℂ := !![0,-1;1,0]
def Vi : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]
def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

theorem ViV : Vi*V=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [Vi,V,Matrix.mul_apply,Fin.sum_univ_two]
theorem XX : X*X=1 := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [X,Matrix.mul_apply,Fin.sum_univ_two]
theorem V_monomial : MonomialMatrix V := by
  refine ⟨Equiv.swap 0 1,![1,-1],?_,?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [V]
theorem Vi_monomial : MonomialMatrix Vi := by
  refine ⟨Equiv.swap 0 1,![-1,1],?_,?_⟩
  · intro j; fin_cases j <;> norm_num
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [Vi]
theorem X_monomial : MonomialMatrix X := by
  refine ⟨Equiv.swap 0 1,fun _ => 1,by simp,?_⟩
  intro i j; fin_cases i <;> fin_cases j <;> norm_num [X]

def gauge (m : ℕ) : Matrix (Fin 2×Bits m) (Fin 2×Bits m) ℂ :=
  Matrix.blockDiagonal (fun i => Vi^(weight m i))
def Q (m : ℕ) : Matrix (Fin 2×Bits m) (Fin 2×Bits m) ℂ := 1+V⊗ₖD m

theorem gauge_monomial (m : ℕ) : MonomialMatrix (gauge m) :=
  MonomialMatrix.blockDiagonal _ (fun _ => Vi_monomial.pow _)

theorem blockDiagonal_mul_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : β → Matrix α α ℂ) (B : Matrix (α×β) (α×β) ℂ) (a b : α) (i j : β) :
    (Matrix.blockDiagonal A*B) (a,i) (b,j)=∑ c,A i a c*B (c,i) (b,j) := by
  classical
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]

theorem mul_blockDiagonal_apply {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (A : Matrix (α×β) (α×β) ℂ) (B : β → Matrix α α ℂ) (a b : α) (i j : β) :
    (A*Matrix.blockDiagonal B) (a,i) (b,j)=∑ c,A (a,i) (c,j)*B j c b := by
  classical
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]

theorem gauge_intertwine (m : ℕ) :
    gauge m*Q m=((1 : Matrix (Fin 2) (Fin 2) ℂ)⊗ₖT m)*gauge m := by
  rw [Q,T,Matrix.kronecker_add,Matrix.one_kronecker_one,mul_add,add_mul,mul_one,one_mul]
  congr 1
  ext ⟨a,i⟩ ⟨b,j⟩
  rw [gauge,blockDiagonal_mul_apply,mul_blockDiagonal_apply]
  simp only [Matrix.kronecker_apply,Matrix.one_apply]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,← mul_assoc]
  rw [← Finset.sum_mul]
  change (Vi^weight m i*V) a b*D m i j=D m i j*(Vi^weight m j) a b
  by_cases h : D m i j=0
  · simp [h]
  · rw [D_weight m i j h,pow_succ,mul_assoc,ViV,mul_one,mul_comm]

theorem Q_unit (m : ℕ) : IsUnit (Q m) := by
  have hs : (V⊗ₖD m)*(V⊗ₖD m)=0 := by
    rw [← Matrix.mul_kronecker_mul,D_square,Matrix.kronecker_zero]
  rw [Q,isUnit_iff_exists_inv']
  refine ⟨1-V⊗ₖD m,?_⟩
  rw [sub_mul,mul_add,mul_add,one_mul,one_mul,mul_one,hs]
  abel

theorem Q_price (p : MatrixPrice) (m : ℕ) : p.value (Q m)=2*p.value (T m) := by
  have h := p.monomial (Q m) (gauge m) 1 (Q_unit m) (gauge_monomial m) MonomialMatrix.one
  rw [mul_one,gauge_intertwine] at h
  have ht := TensorTools.unit_tensor (1 : Matrix (Fin 2) (Fin 2) ℂ) (T m) isUnit_one (T_unit m)
  rw [← one_mul ((1 : Matrix (Fin 2) (Fin 2) ℂ)⊗ₖT m),
    p.monomial _ 1 (gauge m) ht MonomialMatrix.one (gauge_monomial m),
    p.tensor _ _ isUnit_one (T_unit m),p.one,mul_zero,zero_add] at h
  norm_num at h
  exact h.symm

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier.SignedBits
open scoped Matrix Kronecker

theorem Gamma_Q (m : ℕ) : Gamma m=Matrix.reindex (twoProdEquiv (Bits m)) (twoProdEquiv (Bits m))
    ((X⊗ₖ(1 : Matrix (Bits m) (Bits m) ℂ))*Q m) := by
  rw [Q,mul_add,mul_one,← Matrix.mul_kronecker_mul,one_mul]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [Gamma,Matrix.reindex_apply,twoProdEquiv,X,V
      ]

end ExactFourier.SignedBits

end
end

section
noncomputable section
namespace ExactFourier
open SignedBits
open scoped Kronecker

end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
end ExactFourier

end
end

section
noncomputable section
namespace ExactFourier
/-- Exact-width mixed rounds. Monomial rounds are counted, not silently free
scalar multiplications. Disjoint parallel blocks share a round. -/
inductive Layered : {α : Type} → [Fintype α] → [DecidableEq α] → Matrix α α ℂ → ℕ → Prop
 | identity {α : Type} [Fintype α] [DecidableEq α] : Layered (1 : Matrix α α ℂ) 0
 | mono {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ)
   (hM : MonomialMatrix M) : Layered M 1
 | pair (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : IsUnit M) : Layered M 1
 | mul {α : Type} [Fintype α] [DecidableEq α] {M N : Matrix α α ℂ} {d e : ℕ}
   (hM : Layered M d) (hN : Layered N e) : Layered (M*N) (d+e)
 | reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   (f : α≃β) {M : Matrix α α ℂ} {d : ℕ} (hM : Layered M d) :
   Layered (Matrix.reindex f f M) d
 | sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
   {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d : ℕ}
   (hM : Layered M d) (hN : Layered N d) : Layered (Matrix.fromBlocks M 0 0 N) d
 | weaken {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ} {d e : ℕ}
   (h : Layered M d) (hde : d≤e) : Layered M e

namespace Layered
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
theorem unit {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) : IsUnit M := by
 induction h with
 | identity => exact isUnit_one
 | mono M hM => exact hM.unit M
 | pair M hM => exact hM
 | mul hM hN ihM ihN => exact ihM.mul ihN
 | reindex f hM ih => exact TensorTools.unit_reindex _ _ ih
 | sum hM hN ihM ihN => exact Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨ihM,ihN⟩
 | weaken h hde ih => exact ih

theorem parallel {M : Matrix α α ℂ} {N : Matrix β β ℂ} {d e : ℕ}
 (hM : Layered M d) (hN : Layered N e) :
 Layered (Matrix.fromBlocks M 0 0 N) (max d e) :=
 (hM.weaken (le_max_left _ _)).sum (hN.weaken (le_max_right _ _))

 theorem embed (e : α↪β) {M : Matrix α α ℂ} {d : ℕ} (h : Layered M d) :
 Layered (Embedded.matrix e M) d :=
 (h.sum (Layered.identity.weaken (Nat.zero_le d))).reindex (Embedded.coordinates e)
end Layered
end ExactFourier

end
end

end OAI
