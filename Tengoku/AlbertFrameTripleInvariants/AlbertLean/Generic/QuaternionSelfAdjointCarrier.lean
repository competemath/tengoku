import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Module
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GroupedSymplecticBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms hat_unhat_of_skew` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms grouped_extract` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_grouped` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms grouped_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixJordan_mem` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier

open AlbertLean.Generic.QuaternionRow.ScalarFibre
open AlbertLean.Generic.QuaternionRow.GroupedBridge

universe u
variable {K : Type u} [Field K] [CharZero K]

def IsSelfAdjoint (P : Mat6 K) : Prop :=
  P.transpose * symplecticJ = symplecticJ * P

def carrierSubmodule : Submodule K (Mat6 K) where
  carrier := {P | IsSelfAdjoint P}
  zero_mem' := by
    change IsSelfAdjoint (0 : Mat6 K)
    simp [IsSelfAdjoint]
  add_mem' := by
    intro A B hA hB
    change IsSelfAdjoint A at hA
    change IsSelfAdjoint B at hB
    change IsSelfAdjoint (A + B)
    simp only [IsSelfAdjoint, Matrix.transpose_add, Matrix.add_mul,
      Matrix.mul_add] at hA hB ⊢
    rw [hA, hB]
  smul_mem' := by
    intro t A hA
    change IsSelfAdjoint A at hA
    change IsSelfAdjoint (t • A)
    simp only [IsSelfAdjoint, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul] at hA ⊢
    rw [hA]

abbrev Carrier (K : Type u) [Field K] [CharZero K] := carrierSubmodule (K := K)

/--
@isnad1 id=isselfad.0h2v.s8.b57b217b98ab from=translated src=- shape=f9fccb43 vocab=778afb2b
-/
theorem carrier_property (P : Carrier K) : IsSelfAdjoint (P : Mat6 K) := by
  change IsSelfAdjoint (P : Mat6 K)
  exact P.property

def topLeft (P : Mat6 K) : Mat3 K := fun i j => P (Sum.inl i) (Sum.inl j)
def topRight (P : Mat6 K) : Mat3 K := fun i j => P (Sum.inl i) (Sum.inr j)
def bottomLeft (P : Mat6 K) : Mat3 K := fun i j => P (Sum.inr i) (Sum.inl j)
def bottomRight (P : Mat6 K) : Mat3 K := fun i j => P (Sum.inr i) (Sum.inr j)

def unhat (B : Mat3 K) : Vec3 K := ![-B 1 2, B 0 2, -B 0 1]

/--
@isnad1 id=eq.0h2v.s4.6f36f426a079 from=translated src=- shape=e17ccb0b vocab=8464dc98
-/
@[simp] theorem unhat_hat (u : Vec3 K) : unhat (hat u) = u := by
  funext i
  fin_cases i <;> simp [unhat, hat]

/--
@isnad1 id=eq.1h2v.s6.38c73eedcbd9 from=translated src=- shape=6820a77e vocab=5c2b590d
-/
theorem topRight_skew {P : Mat6 K} (hP : IsSelfAdjoint P) :
    (topRight P).transpose = -topRight P := by
  ext i j
  have h := congrFun (congrFun hP (Sum.inr i)) (Sum.inr j)
  fin_cases i <;> fin_cases j <;>
    simp [topRight, symplecticJ, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.transpose_apply] at h ⊢ <;>
    linear_combination h

/--
@isnad1 id=eq.1h2v.s6.0f5371730397 from=translated src=- shape=6820a77e vocab=20674b28
-/
theorem bottomLeft_skew {P : Mat6 K} (hP : IsSelfAdjoint P) :
    (bottomLeft P).transpose = -bottomLeft P := by
  ext i j
  have h := congrFun (congrFun hP (Sum.inl i)) (Sum.inl j)
  fin_cases i <;> fin_cases j <;>
    simp [bottomLeft, symplecticJ, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.one_apply, Fin.sum_univ_succ, Matrix.transpose_apply] at h ⊢ <;>
    linear_combination -h

/--
@isnad1 id=eq.1h2v.s5.e13b03baf410 from=translated src=- shape=39c2abb5 vocab=7e49c291
-/
theorem bottomRight_eq_transpose_topLeft {P : Mat6 K}
    (hP : IsSelfAdjoint P) : bottomRight P = (topLeft P).transpose := by
  ext i j
  have h := congrFun (congrFun hP (Sum.inl i)) (Sum.inr j)
  fin_cases i <;> fin_cases j <;>
    simp [bottomRight, topLeft, symplecticJ, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, Fin.sum_univ_succ,
      Matrix.transpose_apply] at h ⊢ <;> exact h.symm

/-- Every skew 3-by-3 matrix is the chosen `hat` of its three displayed
upper-triangular coordinates.  Characteristic zero is used on the diagonal.
@isnad1 id=eq.1h2v.s6.bddf3cd50980 from=translated src=- shape=16cb8430 vocab=14d74ecd
-/
theorem hat_unhat_of_skew (B : Mat3 K) (hB : B.transpose = -B) :
    hat (unhat B) = B := by
  ext i j
  have hij := congrFun (congrFun hB i) j
  fin_cases i <;> fin_cases j
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (-1 / 2 : K) * hij
  · simp [unhat, hat]
  · simp [unhat, hat]
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (norm := module) -hij
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (-1 / 2 : K) * hij
  · simp [unhat, hat]
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (norm := module) -hij
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (norm := module) -hij
  · simp [unhat, hat, Matrix.transpose_apply] at hij ⊢
    linear_combination (-1 / 2 : K) * hij

/-- Converse to `grouped_symplectic_selfadjoint`: every actual
symplectic-selfadjoint matrix has unique displayed grouped coordinates.
@isnad1 id=eq.1h2v.s5.76f82efefe81 from=translated src=- shape=b61bb942 vocab=099bbf52
-/
theorem grouped_extract (P : Mat6 K) (hP : IsSelfAdjoint P) :
    grouped (topLeft P) (unhat (topRight P)) (unhat (bottomLeft P)) = P := by
  have hB := hat_unhat_of_skew (topRight P) (topRight_skew hP)
  have hC := hat_unhat_of_skew (bottomLeft P) (bottomLeft_skew hP)
  have hD := bottomRight_eq_transpose_topLeft hP
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · exact congrFun (congrFun hB i) j
  · exact congrFun (congrFun hC i) j
  · exact (congrFun (congrFun hD i) j).symm

/--
@isnad1 id=ex.0h2v.s8.de76f5b954ac from=translated src=- shape=0c13d6b3 vocab=d49c2fd8
-/
theorem exists_grouped (P : Carrier K) :
    ∃ a u v, (P : Mat6 K) = grouped a u v := by
  have hP : IsSelfAdjoint (P : Mat6 K) := carrier_property P
  exact ⟨topLeft P, unhat (topRight P), unhat (bottomLeft P),
    (grouped_extract (K := K) (P : Mat6 K) hP).symm⟩

/-- The grouped coordinates are unique, so this carrier has exactly the
`9+3+3` scalar coordinates displayed by `(a,u,v)`.
@isnad1 id=and.1h7v.s6.9abd99d1d194 from=translated src=- shape=91ffdc72 vocab=e32440f8
-/
theorem grouped_injective
    {a a' : Mat3 K} {u v u' v' : Vec3 K}
    (h : grouped a u v = grouped a' u' v') :
    a = a' ∧ u = u' ∧ v = v' := by
  have ha : a = a' := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  have huHat : hat u = hat u' := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  have hvHat : hat v = hat v' := by
    ext i j
    exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  exact ⟨ha, by simpa using congrArg unhat huHat,
    by simpa using congrArg unhat hvHat⟩

/-- The symmetric Jordan product of two actual carrier elements remains in
the actual carrier.
@isnad1 id=isselfad.2h3v.s5.3f979b85234b from=translated src=- shape=d8d8ccef vocab=d5cdb6a9
-/
theorem matrixJordan_mem {A B : Mat6 K}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (matrixJordan A B) := by
  simp only [IsSelfAdjoint, matrixJordan, Matrix.transpose_smul,
    Matrix.transpose_add, Matrix.transpose_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add] at hA hB ⊢
  rw [Matrix.mul_assoc B.transpose A.transpose symplecticJ,
    Matrix.mul_assoc A.transpose B.transpose symplecticJ, hA, hB]
  rw [← Matrix.mul_assoc B.transpose symplecticJ A,
    ← Matrix.mul_assoc A.transpose symplecticJ B, hB, hA]
  simp [Matrix.mul_assoc, add_comm]

def jordan (A B : Carrier K) : Carrier K :=
  ⟨matrixJordan A B, matrixJordan_mem (carrier_property A) (carrier_property B)⟩

def one : Carrier K := by
  refine ⟨1, ?_⟩
  change IsSelfAdjoint (1 : Mat6 K)
  simp [IsSelfAdjoint]

/--
@isnad1 id=eq.0h3v.s9.b560dd6ff635 from=translated src=- shape=afa1e9a4 vocab=e4748f2f
-/
@[simp] theorem coe_jordan (A B : Carrier K) :
    ((jordan A B : Carrier K) : Mat6 K) = matrixJordan A B := rfl

/--
@isnad1 id=eq.0h1v.s8.ce609b8ca695 from=translated src=- shape=cc700884 vocab=57eddf84
-/
@[simp] theorem coe_one : ((one : Carrier K) : Mat6 K) = 1 := rfl

end AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier
