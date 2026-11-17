import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Defs/Basic.lean
  Tube type, Hadamard product for vectors, embedding ℝ ↪ ℂ.
-/

namespace TubalTensor

open Complex Matrix

/-! ## Hadamard (entrywise) product on vectors -/

/-- Entrywise (Hadamard) product on `Fin n → ℂ`.-/
noncomputable def vecHadamard {n : ℕ} (a b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => a i * b i

scoped infixl:70 " ∘ₕ " => vecHadamard

@[simp]
theorem vecHadamard_apply {n : ℕ} (a b : Fin n → ℂ) (i : Fin n) :
    (a ∘ₕ b) i = a i * b i := rfl

theorem vecHadamard_comm {n : ℕ} (a b : Fin n → ℂ) : a ∘ₕ b = b ∘ₕ a := by
  ext i; simp [mul_comm]

theorem vecHadamard_assoc {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ b ∘ₕ c = a ∘ₕ(b ∘ₕ c) := by
  ext i; exact mul_assoc _ _ _

theorem vecHadamard_left_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ(b + c) = a ∘ₕ b + a ∘ₕ c := by
  ext i; simp [mul_add]

theorem vecHadamard_right_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    (a + b) ∘ₕ c = a ∘ₕ c + b ∘ₕ c := by
  ext i; simp [add_mul]

/-- The all-ones vector in `Fin n → ℂ`.-/
def allOnes (n : ℕ) : Fin n → ℂ := fun _ => 1

@[simp]
theorem allOnes_apply (n : ℕ) (i : Fin n) : allOnes n i = 1 := rfl

theorem vecHadamard_allOnes_left {n : ℕ} (a : Fin n → ℂ) :
    allOnes n ∘ₕ a = a := by
  ext i; simp

theorem vecHadamard_allOnes_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ allOnes n = a := by
  ext i; simp

theorem vecHadamard_zero_left {n : ℕ} (a : Fin n → ℂ) :
    (0 : Fin n → ℂ) ∘ₕ a = 0 := by
  ext i; simp

theorem vecHadamard_zero_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ(0 : Fin n → ℂ) = 0 := by
  ext i; simp

theorem vecHadamard_neg_left {n : ℕ} (a b : Fin n → ℂ) :
    (-a) ∘ₕ b = -(a ∘ₕ b) := by
  ext i; simp [neg_mul]

theorem vecHadamard_smul_left {n : ℕ} (r : ℂ) (a b : Fin n → ℂ) :
    (r • a) ∘ₕ b = r • (a ∘ₕ b) := by
  ext i; simp [vecHadamard, mul_assoc]

theorem vecHadamard_conj {n : ℕ} (a b : Fin n → ℂ) :
    starRingEnd ℂ ∘ (a ∘ₕ b) = (starRingEnd ℂ ∘ a) ∘ₕ(starRingEnd ℂ ∘ b) := by
  ext i; simp [vecHadamard, map_mul]

/-! ## Embedding ℝⁿ ↪ ℂⁿ -/

/-- Componentwise embedding of real vectors into complex vectors.-/
def toComplex {n : ℕ} (a : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (a i : ℂ)

@[simp]
theorem toComplex_apply {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    toComplex a i = (a i : ℂ) := rfl

theorem toComplex_injective {n : ℕ} : Function.Injective (toComplex (n := n)) := by
  intro a b h
  ext i
  have hi := congr_fun h i
  simp only [toComplex_apply] at hi
  exact_mod_cast hi

theorem toComplex_add {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a + b) = toComplex a + toComplex b := by
  ext i; simp

theorem toComplex_neg {n : ℕ} (a : Fin n → ℝ) :
    toComplex (-a) = -toComplex a := by
  ext i; simp

theorem toComplex_smul {n : ℕ} (r : ℝ) (a : Fin n → ℝ) :
    toComplex (r • a) = (r : ℂ) • toComplex a := by
  ext i; simp [Complex.ofReal_mul]

theorem toComplex_zero {n : ℕ} : toComplex (0 : Fin n → ℝ) = 0 := by
  ext i; simp

theorem toComplex_sub {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a - b) = toComplex a - toComplex b := by
  ext i; simp

/-! ## Extracting real part of a complex vector -/

/-- Componentwise real part of a complex vector.-/
def vecRe {n : ℕ} (a : Fin n → ℂ) : Fin n → ℝ :=
  fun i => (a i).re

@[simp]
theorem vecRe_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecRe a i = (a i).re := rfl

theorem vecRe_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecRe (toComplex a) = a := by
  ext i; simp

theorem toComplex_vecRe {n : ℕ} (a : Fin n → ℂ) (h : ∀ i, (a i).im = 0) :
    toComplex (vecRe a) = a := by
  ext i; simp [Complex.ext_iff, h i]

/-- A complex vector is real iff every component has zero imaginary part.-/
def IsRealVec {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i : Fin n, (a i).im = 0

theorem isRealVec_iff_eq_toComplex {n : ℕ} (a : Fin n → ℂ) :
    IsRealVec a ↔ a = toComplex (vecRe a) := by
  constructor
  · intro h; ext i; simp [Complex.ext_iff, h i]
  · intro h i; rw [h]; simp

theorem isRealVec_toComplex {n : ℕ} (a : Fin n → ℝ) : IsRealVec (toComplex a) := by
  intro i; simp

theorem isRealVec_add {n : ℕ} {a b : Fin n → ℂ} (ha : IsRealVec a) (hb : IsRealVec b) :
    IsRealVec (a + b) := by
  intro i; simp [ha i, hb i]

theorem isRealVec_neg {n : ℕ} {a : Fin n → ℂ} (ha : IsRealVec a) :
    IsRealVec (-a) := by
  intro i; simp [ha i]

theorem vecRe_add {n : ℕ} (a b : Fin n → ℂ) :
    vecRe (a + b) = vecRe a + vecRe b := by
  ext i; simp

theorem vecRe_neg {n : ℕ} (a : Fin n → ℂ) :
    vecRe (-a) = -vecRe a := by
  ext i; simp

/-! ## Conjugation on vectors -/

/-- Componentwise complex conjugation of a vector.-/
def vecConj {n : ℕ} (a : Fin n → ℂ) : Fin n → ℂ :=
  fun i => starRingEnd ℂ (a i)

@[simp]
theorem vecConj_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecConj a i = starRingEnd ℂ (a i) := rfl

theorem vecConj_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecConj (toComplex a) = toComplex a := by
  ext i; simp [vecConj, Complex.conj_ofReal]

end TubalTensor
