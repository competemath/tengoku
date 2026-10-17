import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Triangular

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure CylinderOperation (I : Finset ℕ) where
  scaleIndex : ℕ
  center : OperationGrid I scaleIndex
  isG : Bool

namespace CylinderOperation
variable {I : Finset ℕ}
def scale (r : CylinderOperation I) : ℝ := dyadic r.scaleIndex
def point (r : CylinderOperation I) : Cube I := operationGridPoint I r.scaleIndex r.center
def act (r : CylinderOperation I) : (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  localOp r.isG r.point r.scale

/--
@isnad1 id=lt.0h2v.s4.69854fc87345 from=translated src=- shape=9ec563f8 vocab=ab1cfddf
-/
theorem scale_pos (r : CylinderOperation I) : 0 < r.scale := dyadic_pos r.scaleIndex

/--
@isnad1 id=lipschit.1h4v.s8.2060574faeed from=translated src=- shape=e302805c vocab=d49b0b29
-/
theorem act_lipschitz (r : CylinderOperation I) {K : ℝ≥0} {u : Cube I → ℝ}
    (hu : LipschitzWith K u) : LipschitzWith (4*K) (r.act u) := by
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact (localR_lipschitz r.point r.scale_pos u hu).weaken (by nlinarith)
  · exact localG_lipschitz r.point r.scale_pos u hu

/--
@isnad1 id=le.2h5v.s7.a162e7ab65da from=translated src=- shape=155fba24 vocab=a1e19c4e
-/
theorem act_sup (r : CylinderOperation I) {A : ℝ} (hA : 0 ≤ A)
    {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) : ∀ x, |r.act u x| ≤ 2*A := by
  intro x
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact localR_sup r.point r.scale u A hu x
  · exact (localG_sup r.point r.scale u A hu x).trans (by linarith)

end CylinderOperation

def applyOperations {I : Finset ℕ} (ops : List (CylinderOperation I)) :
    (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  match ops with
  | [] => LinearMap.id
  | r :: rs => (applyOperations rs).comp r.act

/--
@isnad1 id=eq.0h2v.s7.fc72c87cd9fb from=translated src=- shape=05c3806e vocab=72f53191
-/
@[simp] theorem applyOperations_nil {I : Finset ℕ} (u : Cube I → ℝ) : applyOperations [] u = u := rfl
/--
@isnad1 id=eq.0h4v.s8.3e91c790f72e from=translated src=- shape=e64b3acf vocab=cd298eed
-/
@[simp] theorem applyOperations_cons {I : Finset ℕ} (r : CylinderOperation I)
    (rs : List (CylinderOperation I)) (u : Cube I → ℝ) :
    applyOperations (r::rs) u = applyOperations rs (r.act u) := rfl

/--
@isnad1 id=eq.0h4v.s8.c1a42f8d626e from=translated src=- shape=b42802ad vocab=fff0c3f3
-/
theorem applyOperations_append {I : Finset ℕ} (rs ss : List (CylinderOperation I))
    (u : Cube I → ℝ) : applyOperations (rs++ss) u = applyOperations ss (applyOperations rs u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih => simpa using ih (r.act u)

/--
@isnad1 id=lipschit.1h4v.s8.956676f23d07 from=translated src=- shape=31763045 vocab=c9bb1f2c
-/
theorem applyOperations_lipschitz {I : Finset ℕ} (ops : List (CylinderOperation I))
    {K : ℝ≥0} {u : Cube I → ℝ} (hu : LipschitzWith K u) :
    LipschitzWith (4^ops.length*K) (applyOperations ops u) := by
  induction ops generalizing K u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (r.act_lipschitz hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

/--
@isnad1 id=le.2h5v.s7.bcfe64495bb8 from=translated src=- shape=ceb4b24b vocab=8150039e
-/
theorem applyOperations_sup {I : Finset ℕ} (ops : List (CylinderOperation I))
    {A : ℝ} (hA : 0 ≤ A) {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) :
    ∀ x, |applyOperations ops u x| ≤ 2^ops.length*A := by
  induction ops generalizing A u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (by positivity : 0 ≤ 2*A) (r.act_sup hA hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh

/--
@isnad1 id=le.3h6v.s9.f6538733388b from=translated src=- shape=cb287c42 vocab=8fe8a335
-/
theorem applyOperations_support_bound {I : Finset ℕ} (ops : List (CylinderOperation I))
    (u : Cube I → ℝ) {φ : Cube I → ℝ} (hφ : LipschitzWith 1 φ) {b : ℝ}
    (hu : ∀ x ∈ tsupport u, φ x ≤ b) :
    ∀ x ∈ tsupport (applyOperations ops u), φ x ≤ b+(ops.map CylinderOperation.scale).sum := by
  induction ops generalizing u b with
  | nil => simpa using hu
  | cons r rs ih =>
    have hnew : ∀ x ∈ tsupport (r.act u), φ x ≤ b+r.scale := by
      simpa only [CylinderOperation.act, NNReal.coe_one, mul_one] using localOp_support_bound r.isG r.point r.scale_pos u φ hφ b hu
    have hh := ih (r.act u) hnew
    simpa only [List.map_cons, List.sum_cons, applyOperations_cons, add_assoc] using hh

structure CylinderBases (Γ : Type*) where
  coordinates : Γ → Finset ℕ
  coordinates_nonempty : ∀ γ, (coordinates γ).Nonempty
  band : Γ → ℕ
  ell : ℕ → ℝ
  ell_pos : ∀ j, 0 < ell j
  base : (γ : Γ) → Cube (coordinates γ) → ℝ
  A : ℝ≥0
  L0 : ℝ≥0
  base_sup : ∀ γ x, |base γ x| ≤ A
  base_lipschitz : ∀ γ, LipschitzWith L0 (base γ)

structure GeneratedRepresentation {Γ : Type*} (B : CylinderBases Γ) (γ : Γ) where
  operations : List (CylinderOperation (B.coordinates γ))
  ordered : operations.Pairwise (fun p q => q.scale ≤ p.scale)
  budget : (operations.map CylinderOperation.scale).sum < B.ell (B.band γ)/2

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

def cubeValue (r : GeneratedRepresentation B γ) : Cube (B.coordinates γ) → ℝ :=
  applyOperations r.operations (B.base γ)

def value (r : GeneratedRepresentation B γ) : C0Ball → ℝ :=
  r.cubeValue ∘ cubeRestrict (B.coordinates γ)

def baseRepresentation (B : CylinderBases Γ) (γ : Γ) : GeneratedRepresentation B γ :=
  ⟨[], by simp, by simpa using half_pos (B.ell_pos (B.band γ))⟩

/--
@isnad1 id=lipschit.0h4v.s7.ffe72779c29f from=translated src=- shape=a618c716 vocab=17553f05
-/
theorem cubeValue_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.cubeValue :=
  applyOperations_lipschitz _ (B.base_lipschitz γ)

/--
@isnad1 id=lipschit.0h4v.s6.02e311dca7a7 from=translated src=- shape=e91b29d9 vocab=4019becb
-/
theorem value_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.value := by
  simpa only [value, mul_one] using r.cubeValue_lipschitz.comp (cubeRestrict_lipschitz (B.coordinates γ))

/--
@isnad1 id=le.0h5v.s6.48b92ef43b87 from=translated src=- shape=a949a97a vocab=0046039d
-/
theorem cubeValue_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.cubeValue x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  applyOperations_sup _ B.A.coe_nonneg (B.base_sup γ)

/--
@isnad1 id=le.0h5v.s6.c0e1b7ea1882 from=translated src=- shape=4aa7ca62 vocab=a7517bde
-/
theorem value_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.value x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  fun point => r.cubeValue_sup (cubeRestrict (B.coordinates γ) point)

end GeneratedRepresentation

def TClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, r.operations.length ≤ h ∧ f = r.value}

structure TailOperation where
  scaleIndex : ℕ
  tailIndex : ℕ
  isBasic : Bool

namespace TailOperation

def factor (t : TailOperation) (s : C0Ball) : ℝ :=
  if t.isBasic then tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  else tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1

/--
@isnad1 id=le.0h2v.s4.ed1a754b5dfd from=translated src=- shape=9239d307 vocab=841c4781
-/
theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith

/--
@isnad1 id=lipschit.0h1v.s6.3846d40b4c45 from=translated src=- shape=9f5e9bfb vocab=d5a5527c
-/
theorem factor_lipschitz (t : TailOperation) : LipschitzWith (2^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s u
  have hh := (tailFactor_lipschitz (dyadic_pos t.scaleIndex) (t.tailIndex+1)).dist_le_mul s.val u.val
  change dist (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val)
      (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) u.val) ≤
      (dyadic t.scaleIndex)⁻¹ * dist s u at hh
  simp only [dyadic, inv_inv] at hh
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  cases ht : t.isBasic
  · simpa only [factor, dyadic, ht, Bool.false_eq_true, ↓reduceIte, dist_sub_right] using hh
  · simpa only [factor, dyadic, ht, ↓reduceIte] using hh

end TailOperation

def tailProduct (ts : List TailOperation) (s : C0Ball) : ℝ := (ts.map (fun t => t.factor s)).prod

/--
@isnad1 id=eq.0h1v.s4.f8a8eb4e54fd from=translated src=- shape=5ee2ef00 vocab=f5432ba1
-/
@[simp] theorem tailProduct_nil (s : C0Ball) : tailProduct [] s = 1 := rfl
/--
@isnad1 id=eq.0h3v.s4.54c3138c94a1 from=translated src=- shape=5d3f6e03 vocab=bcfc4edc
-/
@[simp] theorem tailProduct_cons (t : TailOperation) (ts : List TailOperation) (s : C0Ball) :
    tailProduct (t::ts) s = t.factor s * tailProduct ts s := rfl

/--
@isnad1 id=le.0h2v.s4.9807e61764f9 from=translated src=- shape=e9eefb27 vocab=38051422
-/
theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)

/--
@isnad1 id=lipschit.4h7v.s7.ebe83e8c3cb4 from=translated src=- shape=24ca5cf7 vocab=6664a272
-/
theorem bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y = f x*(g x-g y)+g y*(f x-f y) := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|g y| * |f x-f y| := by rw [abs_mul, abs_mul]
    _ ≤ A*(L*dist x y)+B*(K*dist x y) := add_le_add
      (mul_le_mul (hfB x) (hg.dist_le_mul x y) (abs_nonneg _) A.coe_nonneg)
      (mul_le_mul (hgB y) (hf.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg)
    _ = _ := by push_cast; ring

/--
@isnad1 id=lipschit.0h1v.s6.89410fdd7c14 from=translated src=- shape=6368cb9f vocab=771212cd
-/
theorem tailProduct_lipschitz (ts : List TailOperation) :
    LipschitzWith ((ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum) (tailProduct ts) := by
  induction ts with
  | nil =>
    change LipschitzWith 0 (fun _ : C0Ball => (1 : ℝ))
    exact LipschitzWith.const 1
  | cons t ts ih =>
    have hh := bounded_product_lipschitz (A := 1) (B := 1) t.factor_lipschitz ih t.factor_abs_le (tailProduct_abs_le ts)
    convert hh using 1 <;> first | rfl | simp only [List.map_cons, List.sum_cons, one_mul, add_comm]

/--
@isnad1 id=lipschit.2h2v.s6.9b6c0c11ae90 from=translated src=- shape=6c7b40ae vocab=65f73415
-/
theorem tailProduct_lipschitz_bound (ts : List TailOperation) (h : ℕ)
    (hlen : ts.length ≤ h) (hscale : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((h : ℝ≥0)*2^h) (tailProduct ts) := by
  apply (tailProduct_lipschitz ts).weaken
  calc
    (ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum ≤
        (ts.map (fun _ => (2 : ℝ≥0)^h)).sum := List.sum_le_sum
          (fun t ht => pow_le_pow_right₀ (by norm_num) (hscale t ht))
    _ = (ts.length : ℝ≥0)*2^h := by simp
    _ ≤ (h : ℝ≥0)*2^h := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)

def VClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, ∃ ts : List TailOperation,
    r.operations.length ≤ h ∧ B.band γ ≤ h ∧ ts.length ≤ h ∧
      (∀ t ∈ ts, t.scaleIndex ≤ h) ∧ f = fun s => r.value s*tailProduct ts s}

/--
@isnad1 id=lipschit.1h4v.s6.d7bf9ea40324 from=translated src=- shape=010fa2e9 vocab=8cebcc4c
-/
theorem TClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : LipschitzWith (4^h*B.L0) f := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  apply r.value_lipschitz.weaken
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) B.L0.coe_nonneg

/--
@isnad1 id=le.1h5v.s6.8fa165d6a4ba from=translated src=- shape=88e9a489 vocab=2c0620ec
-/
theorem TClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  intro s
  exact (r.value_sup s).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hlen) B.A.coe_nonneg)

/--
@isnad1 id=lipschit.1h4v.s7.cdd42087ebe4 from=translated src=- shape=7fedc957 vocab=193cfb5b
-/
theorem VClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  have hu : LipschitzWith (4^h*B.L0) r.value := TClass_lipschitz B h ⟨γ,r,hren,rfl⟩
  have hb := tailProduct_lipschitz_bound ts h hlen hscale
  have hsup : ∀ s, |r.value s| ≤ ((2 : ℝ≥0)^h*B.A : ℝ≥0) := by
    intro s
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using TClass_sup B h ⟨γ,r,hren,rfl⟩ s
  have hh := bounded_product_lipschitz (B := 1) hu hb hsup (tailProduct_abs_le ts)
  convert hh using 1 ; try rfl
  rw [one_mul]
  have hp : (4 : ℝ≥0)^h = 2^h*2^h := by rw [← mul_pow]; norm_num
  rw [hp]
  ring

/--
@isnad1 id=le.1h5v.s6.3151f26dc612 from=translated src=- shape=88e9a489 vocab=edd46785
-/
theorem VClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  intro s
  rw [abs_mul]
  exact (mul_le_mul (TClass_sup B h ⟨γ,r,hren,rfl⟩ s) (tailProduct_abs_le ts s)
    (abs_nonneg _) (by positivity)).trans_eq (mul_one _)

def sourceClasses {Γ : Type*} (B : CylinderBases Γ) (n : ℕ) : Set (C0Ball → ℝ) :=
  if n % 2 = 0 then TClass B (n/2+1) else VClass B (n/2+1)

/--
@isnad1 id=eq.0h3v.s5.01bde4e8dc7c from=translated src=- shape=2a8138dc vocab=e711a0e6
-/
@[simp] theorem sourceClasses_even {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h) = TClass B (h+1) := by simp [sourceClasses]

/--
@isnad1 id=eq.0h3v.s5.08febdd0fc41 from=translated src=- shape=4d94c832 vocab=f1438579
-/
@[simp] theorem sourceClasses_odd {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h+1) = VClass B (h+1) := by
  have hh : (2*h+1)/2 = h := by omega
  simp [sourceClasses, hh]

/--
@isnad1 id=le.1h4v.s5.376c338ada98 from=translated src=- shape=7e01151c vocab=05655ab6
-/
theorem tsupport_comp_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) {π : X → Y} (hπ : Continuous π) :
    tsupport (f ∘ π) ⊆ π ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx; exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage hπ

/--
@isnad1 id=le.0h3v.s5.19b51a3ee924 from=translated src=- shape=f85e3df4 vocab=53542010
-/
theorem tsupport_product_subset_left {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  exact subset_tsupport f (left_ne_zero_of_mul (show f x*g x ≠ 0 from hx))

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

/--
@isnad1 id=le.3h7v.s8.f06a52eda07f from=translated src=- shape=c025e575 vocab=5e8b8c62
-/
theorem support_bound (r : GeneratedRepresentation B γ) {φ : Cube (B.coordinates γ) → ℝ}
    (hφ : LipschitzWith 1 φ) {b : ℝ} (hu : ∀ x ∈ tsupport (B.base γ), φ x ≤ b) :
    ∀ s ∈ tsupport r.value,
      φ (cubeRestrict (B.coordinates γ) s) ≤ b+(r.operations.map CylinderOperation.scale).sum := by
  intro s hs
  have hm := tsupport_comp_subset r.cubeValue (cubeRestrict_lipschitz (B.coordinates γ)).continuous hs
  exact applyOperations_support_bound r.operations (B.base γ) hφ hu _ hm

def append (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    GeneratedRepresentation B γ where
  operations := r.operations++[op]
  ordered := List.pairwise_append.mpr ⟨r.ordered, by simp, by
    intro p hp q hq; have hq' : q=op := by simpa using hq
    subst q; exact hord p hp⟩
  budget := by simpa using hbudget

/--
@isnad1 id=eq.2h5v.s8.6ea5b876f8d8 from=translated src=- shape=0408e6f3 vocab=d40672c3
-/
@[simp] theorem append_cubeValue (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    (r.append op hord hbudget).cubeValue = op.act r.cubeValue := by
  exact applyOperations_append r.operations [op] (B.base γ)

/--
@isnad1 id=eventual.0h4v.s6.5edf96953087 from=translated src=- shape=02b1ea1c vocab=188d8170
-/
theorem eventually_append_allowed (r : GeneratedRepresentation B γ) :
    ∀ᶠ a in atTop, (∀ p ∈ r.operations, dyadic a ≤ p.scale) ∧
      (r.operations.map CylinderOperation.scale).sum+dyadic a < B.ell (B.band γ)/2 := by
  have h1 : ∀ᶠ a in atTop, ∀ p ∈ r.operations, dyadic a ≤ p.scale := by
    apply r.operations.finite_toSet.eventually_all.mpr
    intro p hp
    exact dyadic_tendsto.eventually (eventually_le_nhds p.scale_pos)
  have h2 : ∀ᶠ a in atTop, dyadic a < B.ell (B.band γ)/2-(r.operations.map CylinderOperation.scale).sum :=
    dyadic_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr r.budget))
  filter_upwards [h1,h2] with a ha hb
  exact ⟨ha, by linarith⟩

end GeneratedRepresentation

end
end C0Absorption

end OAI
