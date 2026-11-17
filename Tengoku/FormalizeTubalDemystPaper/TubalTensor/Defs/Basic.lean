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

/--
@isnad1 id=eq.0h4v.s5.c2d44180e4ae from=translated src=- shape=d4eaebb1 vocab=c3706598
-/
@[simp]
theorem vecHadamard_apply {n : ℕ} (a b : Fin n → ℂ) (i : Fin n) :
    (a ∘ₕ b) i = a i * b i := rfl

/--
@isnad1 id=eq.0h3v.s4.3876c569a1cc from=translated src=- shape=9922580f vocab=30be4bae
-/
theorem vecHadamard_comm {n : ℕ} (a b : Fin n → ℂ) : a ∘ₕ b = b ∘ₕ a := by
  ext i; simp [mul_comm]

/--
@isnad1 id=eq.0h4v.s5.8f3dcce7fa1d from=translated src=- shape=9965e11c vocab=30be4bae
-/
theorem vecHadamard_assoc {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ b ∘ₕ c = a ∘ₕ(b ∘ₕ c) := by
  ext i; exact mul_assoc _ _ _

/--
@isnad1 id=eq.0h4v.s6.63ec0c96962f from=translated src=- shape=511b4fcd vocab=10c82dc0
-/
theorem vecHadamard_left_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ(b + c) = a ∘ₕ b + a ∘ₕ c := by
  ext i; simp [mul_add]

/--
@isnad1 id=eq.0h4v.s6.1bf2a92cd8e1 from=translated src=- shape=288a6b81 vocab=10c82dc0
-/
theorem vecHadamard_right_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    (a + b) ∘ₕ c = a ∘ₕ c + b ∘ₕ c := by
  ext i; simp [add_mul]

/-- The all-ones vector in `Fin n → ℂ`.-/
def allOnes (n : ℕ) : Fin n → ℂ := fun _ => 1

/--
@isnad1 id=eq.0h2v.s4.13509205786a from=translated src=- shape=64d491c2 vocab=ba0333dd
-/
@[simp]
theorem allOnes_apply (n : ℕ) (i : Fin n) : allOnes n i = 1 := rfl

/--
@isnad1 id=eq.0h2v.s4.febfeeb6817f from=translated src=- shape=5620189d vocab=2890bd07
-/
theorem vecHadamard_allOnes_left {n : ℕ} (a : Fin n → ℂ) :
    allOnes n ∘ₕ a = a := by
  ext i; simp

/--
@isnad1 id=eq.0h2v.s4.a5344d720378 from=translated src=- shape=972d8a0a vocab=2890bd07
-/
theorem vecHadamard_allOnes_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ allOnes n = a := by
  ext i; simp

/--
@isnad1 id=eq.0h2v.s5.2659ee83acec from=translated src=- shape=f00ff7ff vocab=30be4bae
-/
theorem vecHadamard_zero_left {n : ℕ} (a : Fin n → ℂ) :
    (0 : Fin n → ℂ) ∘ₕ a = 0 := by
  ext i; simp

/--
@isnad1 id=eq.0h2v.s5.e062310792a6 from=translated src=- shape=0e5080b7 vocab=30be4bae
-/
theorem vecHadamard_zero_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ(0 : Fin n → ℂ) = 0 := by
  ext i; simp

/--
@isnad1 id=eq.0h3v.s5.13e31f9532a1 from=translated src=- shape=53200377 vocab=57a305b9
-/
theorem vecHadamard_neg_left {n : ℕ} (a b : Fin n → ℂ) :
    (-a) ∘ₕ b = -(a ∘ₕ b) := by
  ext i; simp [neg_mul]

/--
@isnad1 id=eq.0h4v.s6.10c1ec18b054 from=translated src=- shape=b1f483ac vocab=f5f2677e
-/
theorem vecHadamard_smul_left {n : ℕ} (r : ℂ) (a b : Fin n → ℂ) :
    (r • a) ∘ₕ b = r • (a ∘ₕ b) := by
  ext i; simp [vecHadamard, mul_assoc]

/--
@isnad1 id=eq.0h3v.s7.95d874ec8fba from=translated src=- shape=3f27071b vocab=27352fd7
-/
theorem vecHadamard_conj {n : ℕ} (a b : Fin n → ℂ) :
    starRingEnd ℂ ∘ (a ∘ₕ b) = (starRingEnd ℂ ∘ a) ∘ₕ(starRingEnd ℂ ∘ b) := by
  ext i; simp [vecHadamard, map_mul]

/-! ## Embedding ℝⁿ ↪ ℂⁿ -/

/-- Componentwise embedding of real vectors into complex vectors.-/
def toComplex {n : ℕ} (a : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (a i : ℂ)

/--
@isnad1 id=eq.0h3v.s4.f8f0055b38ff from=translated src=- shape=e4b9eb44 vocab=5dee9a8e
-/
@[simp]
theorem toComplex_apply {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    toComplex a i = (a i : ℂ) := rfl

/--
@isnad1 id=injectiv.0h1v.s3.bee5f1d2141e from=translated src=- shape=a63464cb vocab=bf1b1d5c
-/
theorem toComplex_injective {n : ℕ} : Function.Injective (toComplex (n := n)) := by
  intro a b h
  ext i
  have hi := congr_fun h i
  simp only [toComplex_apply] at hi
  exact_mod_cast hi

/--
@isnad1 id=eq.0h3v.s6.dd989a07ef0e from=translated src=- shape=6c7d02ab vocab=b1a11daf
-/
theorem toComplex_add {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a + b) = toComplex a + toComplex b := by
  ext i; simp

/--
@isnad1 id=eq.0h2v.s5.a881be70cc89 from=translated src=- shape=169fcc1f vocab=8e290239
-/
theorem toComplex_neg {n : ℕ} (a : Fin n → ℝ) :
    toComplex (-a) = -toComplex a := by
  ext i; simp

/--
@isnad1 id=eq.0h3v.s6.5c8001ac5305 from=translated src=- shape=4806d497 vocab=8472a5af
-/
theorem toComplex_smul {n : ℕ} (r : ℝ) (a : Fin n → ℝ) :
    toComplex (r • a) = (r : ℂ) • toComplex a := by
  ext i; simp [Complex.ofReal_mul]

/--
@isnad1 id=eq.0h1v.s5.f0f7bf180391 from=translated src=- shape=713ddbf1 vocab=5a5068a7
-/
theorem toComplex_zero {n : ℕ} : toComplex (0 : Fin n → ℝ) = 0 := by
  ext i; simp

/--
@isnad1 id=eq.0h3v.s6.0d7a535ba91f from=translated src=- shape=6c7d02ab vocab=5935dec0
-/
theorem toComplex_sub {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a - b) = toComplex a - toComplex b := by
  ext i; simp

/-! ## Extracting real part of a complex vector -/

/-- Componentwise real part of a complex vector.-/
def vecRe {n : ℕ} (a : Fin n → ℂ) : Fin n → ℝ :=
  fun i => (a i).re

/--
@isnad1 id=eq.0h3v.s4.bf2ee1d97f67 from=translated src=- shape=e4b9eb44 vocab=6ce37b23
-/
@[simp]
theorem vecRe_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecRe a i = (a i).re := rfl

/--
@isnad1 id=eq.0h2v.s4.f6478854b657 from=translated src=- shape=fdec4105 vocab=68890ef5
-/
theorem vecRe_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecRe (toComplex a) = a := by
  ext i; simp

/--
@isnad1 id=eq.1h2v.s5.ff44bd2e2d04 from=translated src=- shape=8a0af346 vocab=274868de
-/
theorem toComplex_vecRe {n : ℕ} (a : Fin n → ℂ) (h : ∀ i, (a i).im = 0) :
    toComplex (vecRe a) = a := by
  ext i; simp [Complex.ext_iff, h i]

/-- A complex vector is real iff every component has zero imaginary part.-/
def IsRealVec {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i : Fin n, (a i).im = 0

/--
@isnad1 id=iff.0h2v.s4.862a1901dfe4 from=translated src=- shape=552a033c vocab=4e803f2b
-/
theorem isRealVec_iff_eq_toComplex {n : ℕ} (a : Fin n → ℂ) :
    IsRealVec a ↔ a = toComplex (vecRe a) := by
  constructor
  · intro h; ext i; simp [Complex.ext_iff, h i]
  · intro h i; rw [h]; simp

/--
@isnad1 id=isrealve.0h2v.s3.203ecda5e035 from=translated src=- shape=b2f3482b vocab=9014a61e
-/
theorem isRealVec_toComplex {n : ℕ} (a : Fin n → ℝ) : IsRealVec (toComplex a) := by
  intro i; simp

/--
@isnad1 id=isrealve.2h3v.s5.1c0180027c00 from=translated src=- shape=1ee68c7f vocab=d2ed29c8
-/
theorem isRealVec_add {n : ℕ} {a b : Fin n → ℂ} (ha : IsRealVec a) (hb : IsRealVec b) :
    IsRealVec (a + b) := by
  intro i; simp [ha i, hb i]

/--
@isnad1 id=isrealve.1h2v.s4.1d4357ef7338 from=translated src=- shape=9755319e vocab=adea332f
-/
theorem isRealVec_neg {n : ℕ} {a : Fin n → ℂ} (ha : IsRealVec a) :
    IsRealVec (-a) := by
  intro i; simp [ha i]

/--
@isnad1 id=eq.0h3v.s6.d4f17546d105 from=translated src=- shape=6c7d02ab vocab=84a91d3d
-/
theorem vecRe_add {n : ℕ} (a b : Fin n → ℂ) :
    vecRe (a + b) = vecRe a + vecRe b := by
  ext i; simp

/--
@isnad1 id=eq.0h2v.s5.257d096e4f37 from=translated src=- shape=169fcc1f vocab=1f884e7a
-/
theorem vecRe_neg {n : ℕ} (a : Fin n → ℂ) :
    vecRe (-a) = -vecRe a := by
  ext i; simp

/-! ## Conjugation on vectors -/

/-- Componentwise complex conjugation of a vector.-/
def vecConj {n : ℕ} (a : Fin n → ℂ) : Fin n → ℂ :=
  fun i => starRingEnd ℂ (a i)

/--
@isnad1 id=eq.0h3v.s5.6ff40f87e028 from=translated src=- shape=ae9d5d41 vocab=0c15a44b
-/
@[simp]
theorem vecConj_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecConj a i = starRingEnd ℂ (a i) := rfl

/--
@isnad1 id=eq.0h2v.s4.a05de43a93b8 from=translated src=- shape=b8d432e7 vocab=edc25ac4
-/
theorem vecConj_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecConj (toComplex a) = toComplex a := by
  ext i; simp [vecConj, Complex.conj_ofReal]

end TubalTensor
