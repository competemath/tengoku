import Tengoku.FormalizeTubalDemystPaper.TubalTensor.TransformDomain.FacewiseProduct
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Modules.TensorMatrix
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.Realness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/TransformDomain/Transform.lean
  Transformed tensor Â := A ×₃ M, inverse transform, and Fact 25.

  Given a tubal matrix A ∈ K_M^{m×p}, the transformed tensor
  Â ∈ ℂ^{m×p×n} (viewed as n frontal slices in ℂ^{m×p}) is defined by
  applying M to each tube along the third dimension:
    Â_k[i,j] = (M · tube(A_{ij}))_k

  Fact 25: C = A ⋆_M B  ⟺  Ĉ = Â △ B̂
-/

namespace TubalTensor

open BigOperators Matrix

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## Transform and inverse transform (Section 6) -/

/-- The transformed tensor Â := A ×₃ M.
    The k-th frontal slice has entry (i,j) = (M · tube(A_{ij}))_k.-/
noncomputable def transform (A : TubalMatrix m p n td) :
    Fin n → Matrix (Fin m) (Fin p) ℂ :=
  fun k i j => td.applyM (toComplex (KM.toFun (A i j))) k

/-- The inverse transform: reconstruct a TubalMatrix from frontal slices.
    For each (i,j), extract the tube across slices, apply M⁻¹, take real part.-/
noncomputable def invTransform (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ) :
    TubalMatrix m p n td :=
  fun i j => KM.ofFun (vecRe (td.applyMinv (fun k => Ahat k i j)))

/--
@isnad1 id=eq.0h8v.s5.830946fc9af4 from=translated src=- shape=f877b802 vocab=0e631dfe
-/
@[simp]
theorem transform_apply (A : TubalMatrix m p n td) (k : Fin n) (i : Fin m) (j : Fin p) :
    transform A k i j = td.applyM (toComplex (KM.toFun (A i j))) k := rfl

/-! ## Transform / inverse transform are mutual inverses -/

/-- Round-trip: invTransform ∘ transform = id.
@isnad1 id=eq.0h5v.s5.e64941dc9063 from=translated src=- shape=e6462a5d vocab=91e7a331
-/
theorem invTransform_transform (A : TubalMatrix m p n td) :
    invTransform (transform A) = A := by
  funext i j
  show KM.ofFun (vecRe (td.applyMinv (td.applyM (toComplex (KM.toFun (A i j)))))) = A i j
  rw [td.applyMinv_applyM, vecRe_toComplex, KM.ofFun_toFun]

/-- Round-trip: transform ∘ invTransform = id, provided the input arises
    from a real tubal matrix (each tube through M⁻¹ gives a real vector).
@isnad1 id=eq.1h5v.s5.bb1bad0c4de3 from=translated src=- shape=b52793fc vocab=41b99a0c
-/
theorem transform_invTransform
    (Ahat : Fin n → Matrix (Fin m) (Fin p) ℂ)
    (hreal : ∀ i j, IsRealVec (td.applyMinv (fun k => Ahat k i j))) :
    transform (invTransform Ahat : TubalMatrix m p n td) = Ahat := by
  funext k i j
  simp only [transform_apply, invTransform, KM.toFun_ofFun]
  rw [toComplex_vecRe _ (hreal i j), td.applyM_applyMinv]

/-! ## Helper lemmas for Fact 25 -/

/-- toComplex distributes over finite sums.-/
private theorem toComplex_sum {ι : Type*} (S : Finset ι) (f : ι → Fin n → ℝ) :
    toComplex (∑ s ∈ S, f s) = ∑ s ∈ S, toComplex (f s) := by
  induction S using Finset.cons_induction with
  | empty => ext i; simp [toComplex_apply]
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [toComplex_add, ih]

/-- applyM distributes over finite sums.-/
private theorem applyM_sum {ι : Type*} (S : Finset ι)
    (f : ι → Fin n → ℂ) :
    td.applyM (∑ s ∈ S, f s) = ∑ s ∈ S, td.applyM (f s) := by
  induction S using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.mulVec_zero _
  | cons a S ha ih =>
    simp only [Finset.sum_cons]
    rw [td.applyM_add, ih]

/-- Key tube-level lemma: M(a ⋆_M b) = Ma ∘ₕ Mb.-/
private theorem applyM_toComplex_mul (a b : KM n td) :
    td.applyM (toComplex (KM.toFun (a * b))) =
    td.applyM (toComplex (KM.toFun a)) ∘ₕ td.applyM (toComplex (KM.toFun b)) := by
  have h1 : toComplex (KM.toFun (a * b)) =
      starMC td (toComplex (KM.toFun a)) (toComplex (KM.toFun b)) := by
    change toComplex (starM td (KM.toFun a) (KM.toFun b)) = _
    exact starM_eq_starMC td (KM.toFun a) (KM.toFun b)
  rw [h1]
  show td.applyM (td.applyMinv (td.applyM _ ∘ₕ td.applyM _)) = _
  rw [td.applyM_applyMinv]

/-! ## Fact 25: C = A ⋆_M B ⟺ Ĉ = Â △ B̂ -/

/-- The transform of a ⋆_M-product equals the facewise product
    of the transforms: `transform (A * B) = transform A △ transform B`.-/
private theorem transform_mul (A : TubalMatrix m p n td) (B : TubalMatrix p l n td) :
    transform (A * B) = transform A △ transform B := by
  funext k i j
  simp only [transform_apply, facewise_apply, Matrix.mul_apply]
  -- KM.toFun distributes over sum (definitional for the type alias)
  change (td.applyM (toComplex (∑ s : Fin p, KM.toFun (A i s * B s j)))) k = _
  rw [toComplex_sum, applyM_sum]
  -- Pull the evaluation at k inside the sum
  rw [Finset.sum_apply]
  -- Apply the tube-level lemma to each summand
  refine Finset.sum_congr rfl fun s _ => ?_
  have := congr_fun (applyM_toComplex_mul (A i s) (B s j)) k
  simpa [vecHadamard_apply] using this

/-- The transform is injective: if two tubal matrices have the same transform,
    they are equal.-/
private theorem transform_injective :
    Function.Injective (transform : TubalMatrix m p n td → _) :=
  Function.LeftInverse.injective invTransform_transform

/-- A tube is zero iff all its transform-domain components are zero.
@isnad1 id=iff.0h7v.s5.92cf2f700170 from=translated src=- shape=95fc6291 vocab=8bfaa4f7
-/
theorem tube_eq_zero_iff_transform {A : TubalMatrix m p n td}
    (i : Fin m) (j : Fin p) :
    A i j = 0 ↔ ∀ k, transform A k i j = 0 := by
  constructor
  · intro h k
    simp only [transform_apply, h, KM.toFun_zero, toComplex_zero]
    exact congr_fun (Matrix.mulVec_zero td.M) k
  · intro h
    have hall : td.applyM (toComplex (KM.toFun (A i j))) = 0 := funext h
    have hzero := congr_arg td.applyMinv hall
    simp only [td.applyMinv_applyM] at hzero
    rw [show td.applyMinv 0 = 0 from Matrix.mulVec_zero _] at hzero
    have hfun : KM.toFun (A i j) = 0 := by
      ext l; have := congr_fun hzero l
      simp only [toComplex, Pi.zero_apply] at this
      exact_mod_cast this
    change KM.ofFun (KM.toFun (A i j)) = 0
    rw [hfun]; rfl

/-- **Fact 25**
    C = A ⋆_M B ⟺ Ĉ = Â △ B̂.
@isnad1 id=iff.0h8v.s6.3c8c6aad5d65 from=translated src=- shape=769d3e09 vocab=9ee79824
-/
theorem transform_eq_facewise_iff
    (A : TubalMatrix m p n td) (B : TubalMatrix p l n td) (C : TubalMatrix m l n td) :
    C = A * B ↔ transform C = transform A △ transform B :=
  ⟨fun h => h ▸ transform_mul A B,
   fun h => transform_injective (h.trans (transform_mul A B).symm)⟩

end TubalTensor
