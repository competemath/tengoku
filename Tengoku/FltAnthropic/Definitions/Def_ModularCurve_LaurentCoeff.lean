import Tengoku.Seed.RingTheory.LaurentSeries
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField

namespace ModularCurve

section CoeffMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := by
    ext k
    simp
  map_one' := by
    ext k
    simp [HahnSeries.coeff_one, apply_ite f]
  map_add' x y := by
    ext k
    simp
  map_mul' x y := by
    have h := HahnSeries.map_mul (f := (f : R →ₙ+* S)) (x := x) (y := y)
    have hx : ∀ z : LaurentSeries R, z.map (f : R →ₙ+* S) = z.map f := fun z =>
      HahnSeries.ext rfl
    rwa [hx, hx, hx] at h

/--
@isnad1 id=eq.0h5v.s8.e49ab4250a62 from=translated src=- shape=91225d07 vocab=1c9a0e72
-/
@[simp]
theorem coeffMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (coeffMap f x).coeff k = f (x.coeff k) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.58354d5d482b from=translated src=- shape=d658a659 vocab=2366d17e
-/
@[simp]
theorem coeffMap_single (f : R →+* S) (k : ℤ) (r : R) :
    coeffMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext m
  rcases eq_or_ne m k with rfl | hm
  · simp [HahnSeries.coeff_single_same]
  · simp [HahnSeries.coeff_single_of_ne hm]

/--
@isnad1 id=eq.0h6v.s9.2d84eb452693 from=translated src=- shape=940bacdb vocab=e043539c
-/
theorem coeffMap_coeffMap (g : S →+* T) (f : R →+* S) (x : LaurentSeries R) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k
  simp

/--
@isnad1 id=eq.0h2v.s7.963f4b2d34e8 from=translated src=- shape=2bcc4d08 vocab=d69e8bd2
-/
@[simp]
theorem coeffMap_id (x : LaurentSeries R) : coeffMap (RingHom.id R) x = x := by
  ext k
  simp

/--
@isnad1 id=eq.1h5v.s8.291ea12731f2 from=translated src=- shape=b48b5da2 vocab=89902c22
-/
theorem coeffMap_congr {f g : R →+* S} (h : f = g) (x : LaurentSeries R) :
    coeffMap f x = coeffMap g x := by
  subst h; rfl

end CoeffMap

section Constants

variable (L : Type*) [Field L]

/--
@isnad1 id=eq.0h2v.s8.cc8f87e4f19d from=translated src=- shape=0782e67a vocab=bc2c5aef
-/
theorem algebraMap_laurentSeries_eq_single (c : L) :
    algebraMap L (LaurentSeries L) c = HahnSeries.single 0 c := by
  have h1 : algebraMap L (PowerSeries L) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

variable {L} in

/--
@isnad1 id=eq.0h3v.s9.509aab01f183 from=translated src=- shape=b7c2790a vocab=c92d0a2d
-/
theorem coeffMap_algebraMap (φ : L →+* L) (c : L) :
    coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

variable [Algebra ℚ L]

def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=
  coeffMap (algebraMap ℚ L)

/--
@isnad1 id=eq.0h3v.s7.a57cd3aa0eaf from=translated src=- shape=b323617a vocab=652ba70b
-/
@[simp]
theorem coeffEmb_coeff (x : LaurentSeries ℚ) (k : ℤ) :
    (coeffEmb L x).coeff k = algebraMap ℚ L (x.coeff k) :=
  rfl

variable {L} in

/--
@isnad1 id=eq.0h3v.s9.0290ad1404d7 from=translated src=- shape=fcab3498 vocab=ebd442be
-/
theorem coeffMap_coeffEmb (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries ℚ) :
    coeffMap (σ : L →+* L) (coeffEmb L x) = coeffEmb L x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun c => σ.commutes c) x

end Constants

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

def laurentBaseChange : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))

variable {F₀} in

/--
@isnad1 id=mem.1h3v.s9.38b97bf66c57 from=translated src=- shape=3f62b87e vocab=9e28aab1
-/
theorem coeffEmb_mem_laurentBaseChange {x : LaurentSeries ℚ} (hx : x ∈ F₀) :
    coeffEmb L x ∈ laurentBaseChange L F₀ :=
  IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩

variable {L F₀} in

/--
@isnad1 id=iff.0h3v.s9.ba5edc072ad0 from=translated src=- shape=3025e97b vocab=7e85152b
-/
theorem mem_laurentBaseChange_iff {x : LaurentSeries L} :
    x ∈ laurentBaseChange L F₀ ↔
      x ∈ Subfield.closure
        (Set.range (algebraMap L (LaurentSeries L)) ∪
          (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :=
  Iff.rfl

variable {L F₀} in

/--
@isnad1 id=mem.1h4v.s9.f7f08624510b from=translated src=- shape=9e2d4dbe vocab=8abcfa3c
-/
theorem coeffMap_mem_laurentBaseChange (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap (σ : L →+* L) x ∈ laurentBaseChange L F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (laurentBaseChange L F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end BaseChange

end ModularCurve

end
