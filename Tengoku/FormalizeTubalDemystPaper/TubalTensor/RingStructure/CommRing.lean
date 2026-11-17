import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.Realness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/RingStructure/CommRing.lean
  Theorem 3: K_M is a commutative unital ring.

  We define the type KM n td as a wrapper around Fin n → ℝ equipped
  with the ⋆_M product, and prove it forms a commutative ring.
-/

namespace TubalTensor

open Complex Matrix

variable {n : ℕ}

/-! ## The type KM: tubes with the ⋆_M ring structure -/

/-- The type of n-tubes with the ⋆_M ring structure.
    As a set this is ℝⁿ, but it carries a different multiplication.-/
def KM (n : ℕ) (_td : TubalData n) := Fin n → ℝ

namespace KM

variable {td : TubalData n}

noncomputable instance : DecidableEq (KM n td) := inferInstanceAs (DecidableEq (Fin n → ℝ))

/-- Coerce from KM to the underlying function type.-/
def toFun (a : KM n td) : Fin n → ℝ := a

/-- Construct a KM element from a function.-/
def ofFun (a : Fin n → ℝ) : KM n td := a

@[ext]
theorem ext {a b : KM n td} (h : ∀ i, toFun a i = toFun b i) : a = b :=
  funext h

@[simp] theorem ofFun_toFun (a : KM n td) : ofFun (toFun a) = a := rfl
@[simp] theorem toFun_ofFun (a : Fin n → ℝ) : toFun (ofFun a : KM n td) = a := rfl

/-! ## Additive structure (inherited from Fin n → ℝ) -/

noncomputable instance : Zero (KM n td) := ⟨ofFun 0⟩
noncomputable instance : Add (KM n td) := ⟨fun a b => ofFun (toFun a + toFun b)⟩
noncomputable instance : Neg (KM n td) := ⟨fun a => ofFun (-toFun a)⟩
noncomputable instance : Sub (KM n td) := ⟨fun a b => ofFun (toFun a - toFun b)⟩

noncomputable instance : SMul ℤ (KM n td) :=
  ⟨fun z a => ofFun (z • toFun a)⟩

noncomputable instance : SMul ℕ (KM n td) :=
  ⟨fun n a => ofFun (n • toFun a)⟩

@[simp] theorem toFun_zero : toFun (0 : KM n td) = 0 := rfl
@[simp] theorem toFun_add (a b : KM n td) : toFun (a + b) = toFun a + toFun b := rfl
@[simp] theorem toFun_neg (a : KM n td) : toFun (-a) = -toFun a := rfl
@[simp] theorem toFun_sub (a b : KM n td) : toFun (a - b) = toFun a - toFun b := rfl
@[simp] theorem toFun_nsmul (k : ℕ) (a : KM n td) : toFun (k • a) = k • toFun a := rfl
@[simp] theorem toFun_zsmul (k : ℤ) (a : KM n td) : toFun (k • a) = k • toFun a := rfl

noncomputable instance : AddCommGroup (KM n td) where
  add_assoc a b c := show ofFun _ = ofFun _ from congr_arg ofFun (add_assoc _ _ _)
  zero_add a := show ofFun _ = _ from congr_arg ofFun (zero_add _)
  add_zero a := show ofFun _ = _ from congr_arg ofFun (add_zero _)
  add_comm a b := show ofFun _ = ofFun _ from congr_arg ofFun (add_comm _ _)
  neg_add_cancel a := show ofFun _ = ofFun _ from congr_arg ofFun (neg_add_cancel _)
  nsmul := (· • ·)
  zsmul := (· • ·)

/-! ## Multiplicative structure via ⋆_M -/

/-- The ⋆_M multiplication on KM.-/
noncomputable instance : Mul (KM n td) :=
  ⟨fun a b => ofFun (starM td (toFun a) (toFun b))⟩

@[simp] theorem toFun_mul (a b : KM n td) :
    toFun (a * b) = starM td (toFun a) (toFun b) := rfl

/-- The unit element of KM: eM = M⁻¹ * 1-/
noncomputable instance : One (KM n td) := ⟨ofFun (unitTube td)⟩

@[simp] theorem toFun_one : toFun (1 : KM n td) = unitTube td := rfl

/-! ## Core proof: ⋆_M associativity via complex lift -/

/-- Helper: the starMC complex product is associative.-/
private theorem starMC_assoc (td : TubalData n) (a b c : Fin n → ℂ) :
    starMC td (starMC td a b) c = starMC td a (starMC td b c) := by
  unfold starMC
  congr 1
  rw [td.applyM_applyMinv, td.applyM_applyMinv]
  exact vecHadamard_assoc _ _ _

/-- Helper: the starMC complex product is commutative.-/
private theorem starMC_comm (td : TubalData n) (a b : Fin n → ℂ) :
    starMC td a b = starMC td b a := by
  unfold starMC
  congr 1
  exact vecHadamard_comm _ _

/-- Helper: starMC distributes over addition on the left.-/
private theorem starMC_add_left (td : TubalData n) (a b c : Fin n → ℂ) :
    starMC td (a + b) c = starMC td a c + starMC td b c := by
  show td.applyMinv _ = td.applyMinv _ + td.applyMinv _
  rw [← td.applyMinv_add]
  congr 1
  show td.applyM (a + b) ∘ₕ td.applyM c =
    td.applyM a ∘ₕ td.applyM c + td.applyM b ∘ₕ td.applyM c
  rw [td.applyM_add, vecHadamard_right_distrib]

/-- Helper: the unit element is indeed a left identity for starMC.-/
private theorem starMC_one_left (td : TubalData n) (a : Fin n → ℂ) :
    starMC td (td.applyMinv (allOnes n)) a = a := by
  unfold starMC
  rw [td.applyM_applyMinv, vecHadamard_allOnes_left]
  exact td.applyMinv_applyM a

/-- Helper: zero is absorbing for starMC.-/
private theorem starMC_zero_left (td : TubalData n) (a : Fin n → ℂ) :
    starMC td 0 a = 0 := by
  show td.applyMinv (td.applyM (0 : Fin n → ℂ) ∘ₕ td.applyM a) = 0
  have h1 : td.applyM (0 : Fin n → ℂ) = 0 := Matrix.mulVec_zero _
  rw [h1, vecHadamard_zero_left]
  show td.M_inv *ᵥ (0 : Fin n → ℂ) = 0
  exact Matrix.mulVec_zero _

/-- Helper: negation in starMC.-/
private theorem starMC_neg_left (td : TubalData n) (a b : Fin n → ℂ) :
    starMC td (-a) b = -starMC td a b := by
  show td.applyMinv (td.applyM (-a) ∘ₕ td.applyM b) =
    -td.applyMinv (td.applyM a ∘ₕ td.applyM b)
  rw [show td.applyM (-a) = -td.applyM a from Matrix.mulVec_neg _ _]
  rw [vecHadamard_neg_left]
  show td.M_inv *ᵥ -(td.applyM a ∘ₕ td.applyM b) =
    -(td.M_inv *ᵥ (td.applyM a ∘ₕ td.applyM b))
  exact Matrix.mulVec_neg _ td.M_inv

/-! ## Lift to real operations via toComplex embedding -/

theorem starM_assoc (td : TubalData n) (a b c : Fin n → ℝ) :
    starM td (starM td a b) c = starM td a (starM td b c) := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC, starM_eq_starMC, starM_eq_starMC]
  exact starMC_assoc td _ _ _

theorem starM_comm (td : TubalData n) (a b : Fin n → ℝ) :
    starM td a b = starM td b a := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC]
  exact starMC_comm td _ _

theorem starM_add_left (td : TubalData n) (a b c : Fin n → ℝ) :
    starM td (a + b) c = starM td a c + starM td b c := by
  apply toComplex_injective
  rw [toComplex_add, starM_eq_starMC, starM_eq_starMC, starM_eq_starMC, toComplex_add]
  exact starMC_add_left td _ _ _

theorem starM_unitTube_left (td : TubalData n) (a : Fin n → ℝ) :
    starM td (unitTube td) a = a := by
  apply toComplex_injective
  rw [starM_eq_starMC, toComplex_unitTube]
  exact starMC_one_left td _

theorem starM_zero_left (td : TubalData n) (a : Fin n → ℝ) :
    starM td 0 a = 0 := by
  apply toComplex_injective
  rw [toComplex_zero, starM_eq_starMC]
  show starMC td 0 (toComplex a) = 0
  exact starMC_zero_left td _

theorem starM_neg_left (td : TubalData n) (a b : Fin n → ℝ) :
    starM td (-a) b = -(starM td a b) := by
  apply toComplex_injective
  rw [starM_eq_starMC, toComplex_neg, toComplex_neg, starM_eq_starMC]
  exact starMC_neg_left td _ _

/-! ## Assembling the CommRing instance (Theorem 3) -/

/-- **Theorem 3**: (KM n td, +, ⋆_M) is a commutative unital ring.-/
noncomputable instance instCommRing : CommRing (KM n td) where
  mul_assoc a b c := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_assoc td _ _ _)
  one_mul a := by
    show ofFun _ = _; exact congr_arg ofFun (starM_unitTube_left td _)
  mul_one a := by
    show ofFun _ = _
    have : starM td (toFun a) (unitTube td) = toFun a := by
      rw [starM_comm]; exact starM_unitTube_left td _
    exact congr_arg ofFun this
  mul_comm a b := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_comm td _ _)
  left_distrib a b c := by
    show ofFun _ = ofFun _
    have : starM td (toFun a) (toFun b + toFun c) =
           starM td (toFun a) (toFun b) + starM td (toFun a) (toFun c) := by
      rw [starM_comm td _ (toFun b + toFun c), starM_add_left,
          starM_comm td (toFun b), starM_comm td (toFun c)]
    exact congr_arg ofFun this
  right_distrib a b c := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_add_left td _ _ _)
  zero_mul a := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_zero_left td _)
  mul_zero a := by
    show ofFun _ = ofFun _
    have : starM td (toFun a) 0 = 0 := by
      rw [starM_comm]; exact starM_zero_left td _
    exact congr_arg ofFun this

/-- KM is also an ℝ-module via the usual scalar-vector multiplication.-/
noncomputable instance instModule : Module ℝ (KM n td) :=
  inferInstanceAs (Module ℝ (Fin n → ℝ))

/-! ## Algebra and finite-dimensionality -/

/-- Scalar multiplication commutes with ⋆_M: (r • a) ⋆_M b = r • (a ⋆_M b).-/
private theorem smul_starM (td : TubalData n) (r : ℝ) (a b : Fin n → ℝ) :
    starM td (r • a) b = r • starM td a b := by
  apply toComplex_injective
  rw [toComplex_smul, starM_eq_starMC, starM_eq_starMC, toComplex_smul]
  show td.applyMinv (td.applyM ((r : ℂ) • toComplex a) ∘ₕ td.applyM (toComplex b)) =
    (r : ℂ) • td.applyMinv (td.applyM (toComplex a) ∘ₕ td.applyM (toComplex b))
  unfold TubalData.applyM TubalData.applyMinv
  rw [Matrix.mulVec_smul, vecHadamard_smul_left, ← Matrix.mulVec_smul]

/-- **Proposition 5 prerequisite**: KM is an ℝ-algebra.-/
@[reducible] private noncomputable def mkAlgebra : Algebra ℝ (KM n td) :=
  Algebra.ofModule
    (fun r (x y : KM n td) => by
      change ofFun (starM td (r • toFun x) (toFun y)) = ofFun (r • starM td (toFun x) (toFun y))
      exact congr_arg ofFun (smul_starM td r (toFun x) (toFun y)))
    (fun r (x y : KM n td) => by
      change ofFun (starM td (toFun x) (r • toFun y)) = ofFun (r • starM td (toFun x) (toFun y))
      rw [starM_comm td (toFun x) (r • toFun y), starM_comm td (toFun x) (toFun y)]
      exact congr_arg ofFun (smul_starM td r (toFun y) (toFun x)))

-- Note: `Algebra.ofModule` is an `abbrev`, and writing `instance := Algebra.ofModule ...`
-- directly causes Lean to not register the instance in the typeclass system.
-- The workaround is to define the body as a `def` and assign it to the instance.
/-- **Proposition 5**: KM is an ℝ-algebra (scalar multiplication commutes with ⋆_M).-/
noncomputable instance instAlgebra : Algebra ℝ (KM n td) := mkAlgebra

/-- KM is finite-dimensional over ℝ (dimension n).-/
noncomputable instance instFiniteDimensional : FiniteDimensional ℝ (KM n td) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin n → ℝ))

theorem finrank_eq : Module.finrank ℝ (KM n td) = n :=
  Module.finrank_fin_fun (R := ℝ)

end KM

end TubalTensor
