import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.Berger

namespace OAI

noncomputable section

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter

namespace HarmonicCounterexample.Control

lemma derivative_mem_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    {f : ℝ → E} {v : E} {t : ℝ} (hf : HasDerivAt f v t) (hm : ∀ x,f x ∈ S) : v ∈ S := by
  apply hS.mem_of_tendsto hf.tendsto_slope
  exact Filter.Eventually.of_forall fun x => S.smul_mem _ (S.sub_mem (hm x) (hm t))

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

end HarmonicCounterexample.Control

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix NormedSpace
open scoped Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma exp_neg_mul_self (A : Matrix ι ι ℝ) : exp (-A)*exp A = 1 := by
  rw [← Matrix.exp_add_of_commute (-A) A (Commute.refl A).neg_left,neg_add_cancel,exp_zero]

lemma exp_mul_neg_self (A : Matrix ι ι ℝ) : exp A*exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute A (-A) (Commute.refl A).neg_right,add_neg_cancel,exp_zero]

lemma exp_skew_transpose (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    (exp A)ᵀ = exp (-A) := by rw [← Matrix.exp_transpose,hA]

/-- An actual smooth orbit of orthogonal complex structures under any skew
infinitesimal rotation; both orientation classes remain available. -/
def rotate (J : ComplexStructure ι) (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) (t : ℝ) :
    ComplexStructure ι where
  matrix := exp (t • R)*J.matrix*exp (-(t • R))
  square := by
    have hi := exp_neg_mul_self (t • R)
    calc
      (exp (t • R)*J.matrix*exp (-(t • R)))*
        (exp (t • R)*J.matrix*exp (-(t • R))) =
        exp (t • R)*(J.matrix*J.matrix)*exp (-(t • R)) := by
          simp only [mul_assoc,← mul_assoc (exp (-(t • R))) (exp (t • R)),hi,one_mul]
      _ = -1 := by rw [J.square,mul_neg,mul_one,neg_mul,exp_mul_neg_self]
  orthogonal := by
    have hs : (t • R)ᵀ = -(t • R) := by simp only [transpose_smul,hR,smul_neg]
    have hns : (-(t • R))ᵀ = -(-(t • R)) := by rw [transpose_neg,hs]
    rw [transpose_mul,transpose_mul,exp_skew_transpose _ hs,exp_skew_transpose _ hns,neg_neg]
    calc
      (exp (t • R)*(J.matrixᵀ*exp (-(t • R))))*
        (exp (t • R)*J.matrix*exp (-(t • R))) =
        exp (t • R)*(J.matrixᵀ*J.matrix)*exp (-(t • R)) := by
          simp only [mul_assoc,← mul_assoc (exp (-(t • R))) (exp (t • R)),
            exp_neg_mul_self,one_mul]
      _ = 1 := by rw [J.orthogonal,mul_one,exp_mul_neg_self]

lemma rotate_zero (J : ComplexStructure ι) (R : Matrix ι ι ℝ) (hR : Rᵀ = -R) :
    (J.rotate R hR 0).matrix = J.matrix := by
  simp [rotate]

end HarmonicCounterexample.Berger.ComplexStructure

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix

namespace HarmonicCounterexample.Control
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

def traceFree : Matrix ι ι 𝕜 →ₗ[𝕜] Matrix ι ι 𝕜 where
  toFun M := M - (M.trace / (Fintype.card ι : 𝕜)) • 1
  map_add' M N := by simp only [trace_add,add_div,add_smul]; abel
  map_smul' c M := by
    simp only [trace_smul,smul_eq_mul,mul_div_assoc,smul_sub,smul_smul,RingHom.id_apply]

lemma four_square_polarization {A : Type*} [Ring A] (H X Y : A) :
    H*H-(H-2*X)*(H-2*X)-(H-2*Y)*(H-2*Y)+
      (H-2*X-2*Y)*(H-2*X-2*Y)=4*(X*Y+Y*X) := by noncomm_ring

/-- Four sign choices already extract each mixed plane product: no exponential
Walsh sum needs to be computed inside the kernel. Trace subtraction is exact. -/
lemma mixed_product_mem [CharZero 𝕜] (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    (H X Y : Matrix ι ι 𝕜) (hXY : Commute X Y)
    (h0 : traceFree (H*H) ∈ L)
    (hi : traceFree ((H-2*X)*(H-2*X)) ∈ L)
    (hj : traceFree ((H-2*Y)*(H-2*Y)) ∈ L)
    (hij : traceFree ((H-2*X-2*Y)*(H-2*X-2*Y)) ∈ L) :
    traceFree (X*Y) ∈ L := by
  have h := L.add_mem (L.sub_mem (L.sub_mem h0 hi) hj) hij
  rw [← map_sub,← map_sub,← map_add,four_square_polarization] at h
  have he : (4 : Matrix ι ι 𝕜)*(X*Y+Y*X) = (8:𝕜) • (X*Y) := by
    rw [← hXY.eq]
    ext i j
    simp only [Matrix.smul_apply,mul_apply,ofNat_apply]
    simp
    simp only [Matrix.mul_apply]
    ring
  rw [he,map_smul] at h
  have h' := L.smul_mem (8:𝕜)⁻¹ h
  simpa only [smul_smul,inv_mul_cancel₀ (by norm_num : (8:𝕜) ≠ 0),one_smul] using h'

end HarmonicCounterexample.Control

end

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix

namespace HarmonicCounterexample.Control

section
open Matrix HarmonicCounterexample.Berger
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma traceFree_commutator (A B : Matrix κ κ ℝ) :
    traceFree (A*B-B*A) = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,trace_sub]
  rw [trace_mul_comm A B,sub_self,zero_div,zero_smul,sub_zero]

lemma commutator_traceFree (A B : Matrix κ κ ℝ) :
    A*traceFree B-traceFree B*A = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,
    mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  abel

/-- Normalizer membership on generators propagates through the genuine Lie
span by Jacobi. This is the closure step needed for torus weight filtering. -/
lemma normalizer_lieSpan {𝕜 A : Type*} [Field 𝕜] [LieRing A] [LieAlgebra 𝕜 A]
    (s : Set A) (z : A)
    (hz : ∀ x ∈ s,⁅z,x⁆ ∈ LieSubalgebra.lieSpan 𝕜 A s) :
    ∀ x ∈ LieSubalgebra.lieSpan 𝕜 A s,⁅z,x⁆ ∈ LieSubalgebra.lieSpan 𝕜 A s := by
  intro x hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact hz x hx
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [lie_add] using (LieSubalgebra.lieSpan 𝕜 A s).add_mem ihx ihy
  | smul a x hx ih =>
    simpa only [lie_smul] using (LieSubalgebra.lieSpan 𝕜 A s).smul_mem a ih
  | lie x y hx hy ihx ihy =>
    rw [leibniz_lie]
    exact (LieSubalgebra.lieSpan 𝕜 A s).add_mem
      ((LieSubalgebra.lieSpan 𝕜 A s).lie_mem ihx hy)
      ((LieSubalgebra.lieSpan 𝕜 A s).lie_mem hx ihy)

end

open Matrix HarmonicCounterexample.Berger
open scoped Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
lemma traceFree_commutator_complex (A B : Matrix κ κ ℂ) :
    traceFree (A*B-B*A) = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,trace_sub]
  rw [trace_mul_comm A B,sub_self,zero_div,zero_smul,sub_zero]

lemma commutator_traceFree_complex (A B : Matrix κ κ ℂ) :
    A*traceFree B-traceFree B*A = A*B-B*A := by
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,
    mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  abel

end HarmonicCounterexample.Control

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix
variable {s : ℕ}

/-- The manuscript's explicit three-plane complex structure: the disjoint
coordinate swaps turn the standard pairs into (X_i,X_j), (Y_i,X_k), (Y_j,Y_k).
It is an ACTUAL orthogonal complex structure, with no matrix equations assumed. -/
def triple (i j k : Fin s) : ComplexStructure (Fin s ⊕ Fin s) :=
  (block s).reindex ((Equiv.swap (Sum.inr i) (Sum.inl j)).trans
    (Equiv.swap (Sum.inr j) (Sum.inl k)))

def coordinateSign : Fin s ⊕ Fin s → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
def coordinatePlane : Fin s ⊕ Fin s → Fin s := Sum.elim id id

def signedIndex (i : Fin s) (ε : Bool) : Fin s ⊕ Fin s := if ε then .inl i else .inr i

/-- Pullback matrix in the independent complex coordinates x_i ± i y_i.
This is the exact substitution x=(z+zbar)/2, y=(z-zbar)/(2i), not a spectral
model replacing the real vector field. -/
def splitMatrix (J : ComplexStructure (Fin s ⊕ Fin s)) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ := fun a b =>
  (1/2:ℂ)*((J.matrix (.inl (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    -coordinateSign b*Complex.I*(J.matrix (.inl (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ)
    +coordinateSign a*Complex.I*(J.matrix (.inr (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    +coordinateSign a*coordinateSign b*(J.matrix (.inr (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ))

lemma triple_split_ij (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε β : Bool) : splitMatrix (triple i j k) (signedIndex i ε) (signedIndex j β) = -1/2 := by
  cases ε <;> cases β <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm]

lemma triple_split_ik (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε γ : Bool) : splitMatrix (triple i j k) (signedIndex i ε) (signedIndex k γ) =
      -Complex.I*coordinateSign (signedIndex i ε)/2 := by
  cases ε <;> cases γ <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm] <;> ring

lemma triple_split_ji (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε β : Bool) : splitMatrix (triple i j k) (signedIndex j β) (signedIndex i ε) = 1/2 := by
  cases ε <;> cases β <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm]

lemma triple_split_ki (i j k : Fin s) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ε γ : Bool) : splitMatrix (triple i j k) (signedIndex k γ) (signedIndex i ε) =
      -Complex.I*coordinateSign (signedIndex i ε)/2 := by
  cases ε <;> cases γ <;>
    norm_num [splitMatrix,triple,reindex,block,signedIndex,coordinatePlane,coordinateSign,
      Equiv.swap_apply_def,Matrix.submatrix,Matrix.one_apply,
      Sum.inl_ne_inr,Sum.inr_ne_inl,Sum.inl.injEq,Sum.inr.injEq,
      hij,hik,hjk,hij.symm,hik.symm,hjk.symm] <;> ring

/-- Complexification of the actual real coordinate matrix. -/
def complexMatrix (J : ComplexStructure (Fin s ⊕ Fin s)) :
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ := J.matrix.map Complex.ofReal

def splitChange (s : ℕ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1)

def unsplitChange (s : ℕ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ :=
  (1/2:ℂ) • fromBlocks 1 1 (-Complex.I • 1) (Complex.I • 1)

lemma split_unsplit (s : ℕ) : splitChange s*unsplitChange s = 1 := by
  simp only [splitChange,unsplitChange,mul_smul_comm,fromBlocks_multiply,
    mul_one,mul_smul_comm,smul_smul]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> norm_num [Matrix.ofNat_apply,Matrix.one_apply,hab, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma unsplit_split (s : ℕ) : unsplitChange s*splitChange s = 1 := by
  simp only [splitChange,unsplitChange,smul_mul_assoc,fromBlocks_multiply,
    mul_one,smul_mul_assoc,mul_smul_comm,smul_smul]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> norm_num [Matrix.ofNat_apply,Matrix.one_apply,hab, Sum.inl_ne_inr, Sum.inr_ne_inl]

lemma splitMatrix_eq (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitMatrix J = splitChange s*complexMatrix J*unsplitChange s := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals
    simp [splitMatrix,splitChange,unsplitChange,complexMatrix,coordinatePlane,coordinateSign,
      Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

lemma splitMatrix_square (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitMatrix J*splitMatrix J = -1 := by
  have hj : complexMatrix J*complexMatrix J = -1 := by
    have h := congrArg (Complex.ofRealHom.mapMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →+* Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ) J.square
    rw [map_mul,map_neg,map_one] at h
    change complexMatrix J*complexMatrix J = -1 at h
    exact h
  rw [splitMatrix_eq]
  calc
    (splitChange s*complexMatrix J*unsplitChange s)*
        (splitChange s*complexMatrix J*unsplitChange s) =
        splitChange s*(complexMatrix J*complexMatrix J)*unsplitChange s := by
      simp only [mul_assoc,← mul_assoc (unsplitChange s) (splitChange s),unsplit_split,one_mul]
    _ = -1 := by rw [hj,mul_neg,mul_one,neg_mul,split_unsplit]

def torusMatrix (r : Fin s → ℝ) : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ :=
  fromBlocks 0 (-(diagonal r)) (diagonal r) 0

lemma torusMatrix_skew (r : Fin s → ℝ) : (torusMatrix r)ᵀ = -torusMatrix r := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    by_cases hab : a = b <;> simp [torusMatrix,Matrix.transpose_apply,hab,eq_comm]

lemma torusMatrix_square (r : Fin s → ℝ) (hr : ∀ i,r i*r i = 1) :
    torusMatrix r*torusMatrix r = -1 := by
  have hd : diagonal r*diagonal r = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hr,diagonal_one]
  simp only [torusMatrix,fromBlocks_multiply,zero_mul,mul_zero,zero_add,add_zero,
    neg_mul,mul_neg,hd]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply]

def signedStructure (r : Fin s → ℝ) (hr : ∀ i,r i*r i = 1) :
    ComplexStructure (Fin s ⊕ Fin s) where
  matrix := torusMatrix r
  square := torusMatrix_square r hr
  orthogonal := by rw [torusMatrix_skew,neg_mul,torusMatrix_square r hr,neg_neg]

/-- Real-linear transformation of any actual coordinate field into the source's
independent complex z/bar-z coordinates. -/
def splitFieldMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →ₗ[ℝ]
    Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ where
  toFun M := splitChange s*M.map Complex.ofReal*unsplitChange s
  map_add' M N := by
    simp only [Matrix.map_add _ Complex.ofReal_add,mul_add,add_mul]
  map_smul' r M := by
    have he : (r • M).map Complex.ofReal = r • M.map Complex.ofReal := by ext i j; simp
    rw [he,mul_smul_comm,smul_mul_assoc]
    rfl

lemma splitFieldMatrix_complex (J : ComplexStructure (Fin s ⊕ Fin s)) :
    splitFieldMatrix J.matrix = splitMatrix J := (splitMatrix_eq J).symm

lemma splitFieldMatrix_mul (M N : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :
    splitFieldMatrix (M*N) = splitFieldMatrix M*splitFieldMatrix N := by
  have hf : (M*N).map Complex.ofReal = M.map Complex.ofReal*N.map Complex.ofReal := by
    exact (Complex.ofRealHom.mapMatrix : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ →+*
      Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℂ).map_mul M N
  change splitChange s*(M*N).map Complex.ofReal*unsplitChange s =
    (splitChange s*M.map Complex.ofReal*unsplitChange s)*
    (splitChange s*N.map Complex.ofReal*unsplitChange s)
  rw [hf]
  simp only [mul_assoc,← mul_assoc (unsplitChange s) (splitChange s),unsplit_split,one_mul]

lemma splitFieldMatrix_torus (r : Fin s → ℝ) :
    splitFieldMatrix (torusMatrix r) =
      diagonal (fun a => Complex.I*coordinateSign a*(r (coordinatePlane a):ℂ)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  all_goals
    change (splitChange s*(torusMatrix r).map Complex.ofReal*unsplitChange s) _ _ = _
    simp [splitChange,unsplitChange,torusMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
      Matrix.one_apply,diagonal_apply,coordinateSign,coordinatePlane]
  all_goals by_cases hab : a = b <;> simp [hab]
  all_goals ring_nf

end HarmonicCounterexample.Berger.ComplexStructure

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control
variable {𝕜 ι : Type*} [CommRing 𝕜] [Fintype ι] [DecidableEq ι]

/-- The actual infinitesimal linear coordinate motion, specified on generators. -/
def linearField (M : Matrix ι ι 𝕜) : Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜) :=
  MvPolynomial.mkDerivation 𝕜 (fun i => ∑ j : ι,M i j • X j)

omit [DecidableEq ι] in
lemma linearField_X (M : Matrix ι ι 𝕜) (i : ι) :
    linearField M (X i) = ∑ j : ι,M i j • X j := mkDerivation_X _ _ _

omit [DecidableEq ι] in
lemma linearField_add (M N : Matrix ι ι 𝕜) : linearField (M+N) = linearField M+linearField N := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [linearField_X,add_smul,Finset.sum_add_distrib]

omit [DecidableEq ι] in
lemma linearField_smul (c : 𝕜) (M : Matrix ι ι 𝕜) : linearField (c • M) = c • linearField M := by
  apply MvPolynomial.derivation_ext
  intro i
  simp [linearField_X,smul_smul,Finset.smul_sum]

omit [DecidableEq ι] in
/-- Exact anti-representation identity for coordinate vector fields.
The sign is important: fields act on functions by pullback. -/
lemma linearField_bracket (M N : Matrix ι ι 𝕜) :
    ⁅linearField M,linearField N⁆ = linearField (N*M-M*N) := by
  apply MvPolynomial.derivation_ext
  intro i
  simp only [Derivation.commutator_apply,linearField_X,map_sum,Derivation.map_smul,
    Matrix.sub_apply,Matrix.mul_apply,Finset.sum_sub_distrib,sub_smul,Finset.smul_sum,
    Finset.sum_smul,smul_smul]
  congr 1 <;> exact Finset.sum_comm

omit [Fintype ι] [DecidableEq ι] in
lemma derivation_sum_apply {κ : Type*} (s : Finset κ)
    (f : κ → Derivation 𝕜 (MvPolynomial ι 𝕜) (MvPolynomial ι 𝕜)) (P : MvPolynomial ι 𝕜) :
    (∑ i ∈ s,f i) P = ∑ i ∈ s,f i P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Derivation.add_apply,ih]

lemma linearField_apply (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    linearField M P = ∑ i : ι,∑ j : ι,M i j • (X j*pderiv i P) := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

def linearFieldMap : Matrix ι ι 𝕜 →ₗ[𝕜] Module.End 𝕜 (MvPolynomial ι 𝕜) where
  toFun M := (linearField M).toLinearMap
  map_add' M N := by rw [linearField_add]; rfl
  map_smul' c M := by rw [linearField_smul]; rfl

end HarmonicCounterexample.Control

end

section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control

section
open scoped BigOperators
open Matrix MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

abbrev MonomialIndex (ι : Type*) (l : ℕ) := {d : ι →₀ ℕ // d.degree = l}

instance monomialIndexFintype (l : ℕ) : Fintype (MonomialIndex ι l) := by
  let e : MonomialIndex ι l ≃ ↥((Finset.univ : Finset ι).finsuppAntidiag l) :=
    { toFun := fun d => ⟨d.1, by
        have h : d.1.degree = ∑ i : ι,d.1 i := Finsupp.sum_fintype d.1 (fun _ a => a) (fun _ => rfl)
        exact Finset.mem_finsuppAntidiag.2 ⟨h.symm.trans d.2,Finset.subset_univ _⟩⟩
      invFun := fun d => ⟨d.1,by
        have h : d.1.degree = ∑ i : ι,d.1 i := Finsupp.sum_fintype d.1 (fun _ a => a) (fun _ => rfl)
        exact h.trans (Finset.mem_finsuppAntidiag.1 d.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.ofEquiv _ e.symm

/-- Actual coefficient coordinates on homogeneous polynomials. -/
def homogeneousCoords (l : ℕ) :
    homogeneousSubmodule ι 𝕜 l ≃ₗ[𝕜] MonomialIndex ι l →₀ 𝕜 :=
  (LinearEquiv.ofEq _ _ (homogeneousSubmodule_eq_finsupp_supported ι 𝕜 l)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp (R := 𝕜) (S := 𝕜) {d : ι →₀ ℕ | d.degree = l})

def homogeneousBasis (l : ℕ) : Module.Basis (MonomialIndex ι l) 𝕜 (homogeneousSubmodule ι 𝕜 l) :=
  Finsupp.basisSingleOne.map (homogeneousCoords l).symm

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneousCoords_apply (l : ℕ) (P : homogeneousSubmodule ι 𝕜 l) (d : MonomialIndex ι l) :
    homogeneousCoords l P d = P.1.coeff d.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma homogeneousBasis_repr (l : ℕ) (P : homogeneousSubmodule ι 𝕜 l) (d : MonomialIndex ι l) :
    (homogeneousBasis l).repr P d = P.1.coeff d.1 := rfl

omit [Fintype ι] in
lemma homogeneousBasis_val (l : ℕ) (d : MonomialIndex ι l) :
    ((homogeneousBasis (𝕜 := 𝕜) l) d).1 = monomial d.1 1 := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e.degree = l
  · have h := (homogeneousBasis (𝕜 := 𝕜) l).repr_self d
    have h' := DFunLike.congr_fun h ⟨e,he⟩
    change ((homogeneousBasis (𝕜 := 𝕜) l) d).1.coeff e = (Finsupp.single d (1:𝕜)) ⟨e,he⟩ at h'
    simpa only [Finsupp.single_apply,Subtype.ext_iff,coeff_monomial] using h'
  · have hP := ((homogeneousBasis (𝕜 := 𝕜) l) d).property
    have hzero := hP.coeff_eq_zero he
    have hne : d.1 ≠ e := fun hd => he (hd ▸ d.2)
    simp [hzero,coeff_monomial,hne]

lemma linearField_homogeneous {P : MvPolynomial ι 𝕜} {l : ℕ}
    (hP : P.IsHomogeneous l) (M : Matrix ι ι 𝕜) : (linearField M P).IsHomogeneous l := by
  rw [linearField_apply]
  by_cases hl : l = 0
  · have hc : P = C (P.coeff 0) :=
      totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous ι).2 (hl ▸ hP))
    rw [hc]
    simp only [pderiv_C,mul_zero,smul_zero,Finset.sum_const_zero]
    exact isHomogeneous_zero ι 𝕜 l
  · apply IsHomogeneous.sum
    intro i _
    apply IsHomogeneous.sum
    intro j _
    apply (homogeneousSubmodule ι 𝕜 l).smul_mem
    have h := (isHomogeneous_X 𝕜 j).mul (hP.pderiv (i := i))
    have he : 1+(l-1) = l := by omega
    change (X j*pderiv i P).IsHomogeneous l
    simpa only [he] using h

end

open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
variable {s : ℕ}

def monomialWeight (ν : Fin s ⊕ Fin s →₀ ℕ) (i : Fin s) : ℂ :=
  (ν (.inl i):ℂ)-ν (.inr i)

end HarmonicCounterexample.Control

end

open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
variable {s : ℕ}

end HarmonicCounterexample.Control

end

end OAI
