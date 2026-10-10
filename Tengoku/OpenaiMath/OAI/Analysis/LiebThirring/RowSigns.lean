import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.Continuation

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.ContinuationGap
open Matrix Set

abbrev LowerSpace (N : ℕ) :=
  {C : Matrix (Fin N) (Fin N) ℝ // ∀ i j, i < j → C i j = 0}

def rowSign {N : ℕ} (s : Fin N → ℝ) (C : LowerSpace N) : LowerSpace N :=
  ⟨fun i j ↦ s i * C.val i j, by
    intro i j hij
    change s i * C.val i j = 0
    rw [C.prop i j hij, mul_zero]⟩

def signConjugate {N : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j ↦ s i * Z i j * s j

def NonzeroRows {N : ℕ} (C : LowerSpace N) : Prop := ∀ i, ∃ j, C.val i j ≠ 0

end SharpLiebThirring.ContinuationGap
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

abbrev LowerIndex (N : ℕ) := {a : Fin N × Fin N // a.2 ≤ a.1}
abbrev lowerDim (N : ℕ) := Fintype.card (LowerIndex N)
noncomputable def indexEquiv (N : ℕ) : LowerIndex N ≃ Fin (lowerDim N) := Fintype.equivFin _

def diagonalIndex {N : ℕ} (i : Fin N) : Fin (lowerDim N) := indexEquiv N ⟨(i,i),le_refl _⟩
def rowIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.1
def colIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.2

@[simp] lemma rowIndex_diagonal {N : ℕ} (i : Fin N) : rowIndex (diagonalIndex i) = i := by
  simp [rowIndex,diagonalIndex]
@[simp] lemma colIndex_diagonal {N : ℕ} (i : Fin N) : colIndex (diagonalIndex i) = i := by
  simp [colIndex,diagonalIndex]
lemma colIndex_le_rowIndex {N : ℕ} (a : Fin (lowerDim N)) : colIndex a ≤ rowIndex a :=
  ((indexEquiv N).symm a).prop

/-- Exact linear coordinates on the entire lower-triangular coefficient space;
no nonvanishing or invertibility restriction is imposed. -/
def lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) : LowerSpace N :=
  ⟨fun i j ↦ if h : j ≤ i then x (indexEquiv N ⟨(i,j),h⟩) else 0,
    by intro i j hij; simp only [not_le.mpr hij,↓reduceDIte]⟩
def lowerCoords {N : ℕ} (C : LowerSpace N) : Fin (lowerDim N) → ℝ :=
  fun a ↦ C.val (rowIndex a) (colIndex a)

@[simp] lemma lowerCoords_lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) :
    lowerCoords (lowerOfCoords x) = x := by
  funext a
  have he : (⟨(rowIndex a,colIndex a),colIndex_le_rowIndex a⟩ : LowerIndex N) = (indexEquiv N).symm a := rfl
  simp only [lowerCoords,lowerOfCoords,colIndex_le_rowIndex,↓reduceDIte,he,Equiv.apply_symm_apply]

@[simp] lemma lowerOfCoords_lowerCoords {N : ℕ} (C : LowerSpace N) :
    lowerOfCoords (lowerCoords C) = C := by
  apply Subtype.ext
  funext i j
  dsimp [lowerOfCoords]
  split_ifs with h
  · simp [lowerCoords,rowIndex,colIndex]
  · exact (C.prop i j (lt_of_not_ge h)).symm

lemma continuous_lowerCoords {N : ℕ} : Continuous (lowerCoords (N := N)) := by
  apply continuous_pi
  intro a
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
lemma continuous_lowerOfCoords {N : ℕ} : Continuous (lowerOfCoords (N := N)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : j ≤ i
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_apply (indexEquiv N ⟨(i,j),h⟩))
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_const : Continuous (fun _ : Fin (lowerDim N) → ℝ ↦ (0 : ℝ)))

def lowerHomeomorph (N : ℕ) : (Fin (lowerDim N) → ℝ) ≃ₜ LowerSpace N where
  toFun := lowerOfCoords
  invFun := lowerCoords
  left_inv := lowerCoords_lowerOfCoords
  right_inv := lowerOfCoords_lowerCoords
  continuous_toFun := continuous_lowerOfCoords
  continuous_invFun := continuous_lowerCoords

/-- Coordinate reflections that flip whole rows and fix the homotopy time. -/
def rowSubgroup (N : ℕ) : Subgroup (Signs (lowerDim N + 1)) where
  carrier := {s | s.val (Fin.last (lowerDim N)) = false ∧
    ∀ a : Fin (lowerDim N), s.val a.castSucc = s.val (diagonalIndex (rowIndex a)).castSucc}
  one_mem' := ⟨rfl,fun _ ↦ rfl⟩
  mul_mem' hs ht := ⟨by simp only [Signs.mul_val,hs.1,ht.1,Bool.false_xor],
    fun a ↦ by simp only [Signs.mul_val,hs.2 a,ht.2 a]⟩
  inv_mem' hs := hs

def rowBool {N : ℕ} (s : rowSubgroup N) (i : Fin N) : Bool :=
  s.val.val (diagonalIndex i).castSucc

@[simp] lemma rowBool_one {N : ℕ} (i : Fin N) : rowBool (1 : rowSubgroup N) i = false := rfl
@[simp] lemma rowBool_mul {N : ℕ} (s t : rowSubgroup N) (i : Fin N) :
    rowBool (s*t) i = xor (rowBool s i) (rowBool t i) := rfl

def rowElement {N : ℕ} (s : Fin N → Bool) : rowSubgroup N :=
  ⟨⟨Fin.snoc (fun a ↦ s (rowIndex a)) false⟩,by
    constructor
    · simp only [Fin.snoc_last]
    · intro a
      simp only [Fin.snoc_castSucc,rowIndex_diagonal]⟩
@[simp] lemma rowBool_rowElement {N : ℕ} (s : Fin N → Bool) : rowBool (rowElement s) = s := by
  funext i
  simp only [rowBool,rowElement,Fin.snoc_castSucc,rowIndex_diagonal]

def signValue (b : Bool) : ℝ := if b then -1 else 1
@[simp] lemma signValue_false : signValue false = 1 := rfl
@[simp] lemma signValue_true : signValue true = -1 := rfl
lemma signValue_cases (b : Bool) : signValue b = 1 ∨ signValue b = -1 := by cases b <;> simp [signValue]
lemma signValue_xor (b c : Bool) : signValue (xor b c) = signValue b * signValue c := by
  cases b <;> cases c <;> norm_num [signValue]
lemma signValue_smul (b : Bool) (x : ℝ) : (if b then -x else x) = signValue b * x := by
  cases b <;> simp [signValue]

def conjugateSigns {N : ℕ} (s : rowSubgroup N) : Signs (lowerDim N) :=
  ⟨fun a ↦ xor (rowBool s (rowIndex a)) (rowBool s (colIndex a))⟩

def conjugateRepresentation (N : ℕ) : rowSubgroup N →* ((Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ)) where
  toFun s := (conjugateSigns s).linearIsometry.toLinearEquiv
  map_one' := by
    ext x a
    simp only [conjugateSigns,Signs.linearIsometry,rowBool_one,Bool.false_xor,Bool.false_eq_true,↓reduceIte]
    rfl
  map_mul' s t := by
    ext x a
    change (if xor (rowBool (s*t) (rowIndex a)) (rowBool (s*t) (colIndex a)) then -x a else x a) =
      if xor (rowBool s (rowIndex a)) (rowBool s (colIndex a)) then
        -(if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a) else
        if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a
    simp only [rowBool_mul]
    rcases Bool.eq_false_or_eq_true (rowBool s (rowIndex a)) with h₁ | h₁ <;>
      rcases Bool.eq_false_or_eq_true (rowBool s (colIndex a)) with h₂ | h₂ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (rowIndex a)) with h₃ | h₃ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (colIndex a)) with h₄ | h₄ <;> simp [h₁,h₂,h₃,h₄]

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

/-- Lower-coordinate restriction is faithful on symmetric matrices. -/
def matrixCoords {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Fin (lowerDim N) → ℝ :=
  fun a ↦ A (rowIndex a) (colIndex a)

def diagonalLower {N : ℕ} (c : Fin N → ℝ) : LowerSpace N :=
  ⟨diagonal c,fun _i _j hij ↦ diagonal_apply_ne c (ne_of_lt hij)⟩
def diagonalPoint {N : ℕ} (c : Fin N → ℝ) : Fin (lowerDim N) → ℝ := lowerCoords (diagonalLower c)
@[simp] lemma lowerOfCoords_diagonalPoint {N : ℕ} (c : Fin N → ℝ) :
    lowerOfCoords (diagonalPoint c) = diagonalLower c := lowerOfCoords_lowerCoords _

def lowerEntry {N : ℕ} (i j : Fin N) : (Fin (lowerDim N) → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj (indexEquiv N ⟨(i,j),h⟩) else 0

def initialMap {N : ℕ} (β : ℝ) (k : Fin N → ℝ) (x : Fin (lowerDim N) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (2 • diagonal k - β • ((lowerOfCoords x).val * (lowerOfCoords x).val.transpose))

def jacobianWeight {N : ℕ} (β : ℝ) (c : Fin N → ℝ) (a : Fin (lowerDim N)) : ℝ :=
  -β * (c (colIndex a) + if rowIndex a = colIndex a then c (rowIndex a) else 0)
lemma jacobianWeight_ne_zero {N : ℕ} {β : ℝ} (hβ : β ≠ 0) (c : Fin N → ℝ)
    (hc : ∀ i, 0 < c i) (a : Fin (lowerDim N)) : jacobianWeight β c a ≠ 0 := by
  unfold jacobianWeight
  apply mul_ne_zero (neg_ne_zero.mpr hβ)
  apply ne_of_gt
  split_ifs
  · exact add_pos (hc _) (hc _)
  · simpa using hc (colIndex a)

def initialLinearEquiv {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ) :=
  LinearEquiv.piCongrRight (fun a ↦ LinearEquiv.smulOfNeZero ℝ ℝ (jacobianWeight β c a) (jacobianWeight_ne_zero hβ c hc a))

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

def spaceTimeHomeomorph (N : ℕ) : (Fin (lowerDim N + 1) → ℝ) ≃ₜ (LowerSpace N × ℝ) where
  toFun x := (lowerOfCoords (spatial x),x (Fin.last (lowerDim N)))
  invFun z := Fin.snoc (lowerCoords z.1) z.2
  left_inv x := by
    simp only [lowerCoords_lowerOfCoords]
    exact Fin.snoc_init_self x
  right_inv z := by
    change (lowerOfCoords (Fin.init (Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2)),
      Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2 (Fin.last (lowerDim N))) = z
    simp only [Fin.init_snoc,Fin.snoc_last,lowerOfCoords_lowerCoords]
  continuous_toFun := (continuous_lowerOfCoords.comp spatial.continuous_of_finiteDimensional).prodMk (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simpa only [Fin.snoc_last] using (continuous_snd : Continuous (fun z : LowerSpace N × ℝ ↦ z.2))
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using ((continuous_apply b).comp (continuous_lowerCoords.comp continuous_fst))

def clampTime (t : ℝ) : ℝ := max 0 (min t 1)
lemma clampTime_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clampTime t = t := by
  rw [clampTime,min_eq_left ht.2,max_eq_right ht.1]
@[simp] lemma clampTime_zero : clampTime 0 = 0 := clampTime_eq ⟨le_refl _,zero_le_one⟩
@[simp] lemma clampTime_one : clampTime 1 = 1 := clampTime_eq ⟨zero_le_one,le_refl _⟩

def homotopyCoords {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (x : Fin (lowerDim N + 1) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (Φ (clampTime (x (Fin.last (lowerDim N)))) (lowerOfCoords (spatial x)))

lemma homotopyCoords_initial {N : ℕ} (ε : ℝ) (k : Fin N → ℝ)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (u : Fin (lowerDim N) → ℝ) :
    homotopyCoords Φ (embedSpatial u) = initialMap ε⁻¹ k u := by
  unfold homotopyCoords
  have ht : embedSpatial u (Fin.last (lowerDim N)) = 0 := by
    change Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) u 0 (Fin.last (lowerDim N)) = 0
    exact Fin.snoc_last _ _
  rw [ht,clampTime_zero,spatial_embed,h0]
  rfl

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma initial_matrix_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) :
    2 • diagonal k - ε⁻¹ • ((diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val *
      (diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val.transpose) = 0 := by
  change 2 • diagonal k - ε⁻¹ • (diagonal (fun i ↦ Real.sqrt (2*ε*k i)) *
    (diagonal (fun i ↦ Real.sqrt (2*ε*k i))).transpose) = 0
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul,Matrix.zero_apply]
    rw [← sq,Real.sq_sqrt (le_of_lt (mul_pos (mul_pos (by norm_num) hε) (hk i)))]
    field_simp [ne_of_gt hε]
    ring
  · simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero,sub_self,Matrix.zero_apply]

lemma gram_of_initial_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (C : LowerSpace N)
    (h : 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose) = 0) :
    C.val * C.val.transpose = diagonal (fun i ↦ 2*ε*k i) := by
  have he : ε • (2 • diagonal k) = C.val * C.val.transpose := by
    have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ ε • A) (sub_eq_zero.mp h)
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hε),one_smul] using he
  rw [← he]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul]
    ring
  · simp only [Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero]

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

end SharpLiebThirring.PathTopology

end
end
end

end OAI
