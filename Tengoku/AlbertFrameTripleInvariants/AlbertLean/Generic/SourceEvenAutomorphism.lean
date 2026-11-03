import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceEvenTriality
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CubicAutomorphismSource

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reflectV_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evenJEquiv_sourceNorm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceEvenAut` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Packages one normalized even pair of anisotropic Clifford reflections as a
source cubic-and-unit automorphism.  No generation or coverage statement is
made here.
-/

noncomputable section
namespace AlbertLean.Triality.SourceEvenAutomorphism

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceCliffordLinear SourceEvenReflections SourceEvenTriality
open AlbertLean.Generic

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem reflectV_add (a v w : VCoord K) :
    reflectV a (v + w) = reflectV a v + reflectV a w := by
  rw [reflectV, reflectV, reflectV, BV_add_right]
  module

theorem reflectV_smul (a v : VCoord K) (k : K) :
    reflectV a (k • v) = k • reflectV a v := by
  rw [reflectV, reflectV, BV_smul_right]
  module

theorem BV_reflectV (a v : VCoord K) (ha : nV a ≠ 0) :
    BV a (reflectV a v) = -BV a v := by
  rw [reflectV, sub_eq_add_neg, ← neg_smul, BV_add_right,
    BV_smul_right, BV_self_eq_two_nV]
  field_simp [ha]
  ring

theorem reflectV_involutive (a v : VCoord K) (ha : nV a ≠ 0) :
    reflectV a (reflectV a v) = v := by
  rw [reflectV, BV_reflectV a v ha, reflectV]
  field_simp [ha]
  module

def reflectVLinear (a : VCoord K) : VCoord K →ₗ[K] VCoord K where
  toFun := reflectV a
  map_add' := reflectV_add a
  map_smul' := fun k v => reflectV_smul a v k

def evenVLinear (a b : VCoord K) : VCoord K →ₗ[K] VCoord K :=
  (reflectVLinear a).comp (reflectVLinear b)

@[simp] theorem evenVLinear_apply (a b v : VCoord K) :
    evenVLinear a b v = evenV a b v := rfl

def evenVEquiv (a b : VCoord K) (ha : nV a ≠ 0) (hb : nV b ≠ 0) :
    VCoord K ≃ₗ[K] VCoord K :=
  { evenVLinear a b with
    invFun := evenVLinear b a
    left_inv := by
      intro v
      change reflectV b (reflectV a (reflectV a (reflectV b v))) = v
      rw [reflectV_involutive a _ ha, reflectV_involutive b _ hb]
    right_inv := by
      intro v
      change reflectV a (reflectV b (reflectV b (reflectV a v))) = v
      rw [reflectV_involutive b _ hb, reflectV_involutive a _ ha] }

def evenSLinear (a b : VCoord K) (rho : K) : SCoord K →ₗ[K] SCoord K :=
  rho⁻¹ • (muSLinear a).comp (muCLinear b)

@[simp] theorem evenSLinear_apply (a b : VCoord K) (rho : K) (s : SCoord K) :
    evenSLinear a b rho s = evenS a b rho s := rfl

set_option maxHeartbeats 600000 in
def evenSEquiv (a b : VCoord K) (rho : K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    SCoord K ≃ₗ[K] SCoord K :=
  { evenSLinear a b rho with
    invFun := evenSLinear b a rho
    left_inv := by
      intro s
      simpa only [LinearMap.toFun_eq_coe, evenSLinear_apply] using evenS_reverse a b rho s hrho hrho0
    right_inv := by
      intro s
      simpa only [LinearMap.toFun_eq_coe, evenSLinear_apply] using
        evenS_reverse b a rho s (by simpa [mul_comm] using hrho) hrho0 }

def evenCLinear (a b : VCoord K) (rho : K) : CCoord K →ₗ[K] CCoord K :=
  rho⁻¹ • (muCLinear a).comp (muSLinear b)

@[simp] theorem evenCLinear_apply (a b : VCoord K) (rho : K) (c : CCoord K) :
    evenCLinear a b rho c = evenC a b rho c := rfl

set_option maxHeartbeats 600000 in
def evenCEquiv (a b : VCoord K) (rho : K)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    CCoord K ≃ₗ[K] CCoord K :=
  { evenCLinear a b rho with
    invFun := evenCLinear b a rho
    left_inv := by
      intro c
      simpa only [LinearMap.toFun_eq_coe, evenCLinear_apply] using evenC_reverse a b rho c hrho hrho0
    right_inv := by
      intro c
      simpa only [LinearMap.toFun_eq_coe, evenCLinear_apply] using
        evenC_reverse b a rho c (by simpa [mul_comm] using hrho) hrho0 }

def evenJEquiv (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    JCoord K ≃ₗ[K] JCoord K where
  toFun x :=
    { d1 := x.d1, d2 := x.d2, d3 := x.d3
      v := evenVEquiv a b ha hb x.v
      s := evenSEquiv a b rho hrho hrho0 x.s
      c := evenCEquiv a b rho hrho hrho0 x.c }
  invFun x :=
    { d1 := x.d1, d2 := x.d2, d3 := x.d3
      v := (evenVEquiv a b ha hb).symm x.v
      s := (evenSEquiv a b rho hrho hrho0).symm x.s
      c := (evenCEquiv a b rho hrho hrho0).symm x.c }
  left_inv x := by
    apply JCoord.ext <;> simp
  right_inv x := by
    apply JCoord.ext <;> simp
  map_add' x y := by
    apply JCoord.ext <;> simp
  map_smul' k x := by
    apply JCoord.ext <;> simp

@[simp] theorem evenJEquiv_apply (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) (x : JCoord K) :
    evenJEquiv a b rho ha hb hrho hrho0 x =
      { d1 := x.d1, d2 := x.d2, d3 := x.d3
        v := evenV a b x.v
        s := evenS a b rho x.s
        c := evenC a b rho x.c } := rfl

theorem evenJEquiv_sourceNorm (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) (x : JCoord K) :
    sourceNorm (evenJEquiv a b rho ha hb hrho hrho0 x) = sourceNorm x := by
  rw [evenJEquiv_apply, sourceNorm_formula, sourceNorm_formula,
    nV_evenV a b x.v ha hb, nS_evenS a b rho x.s hrho hrho0,
    nC_evenC a b rho x.c hrho hrho0,
    triality_even a b rho x.v x.s x.c ha hb hrho hrho0]

theorem evenJEquiv_sourceOne (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :
    evenJEquiv a b rho ha hb hrho hrho0 sourceOne = sourceOne := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · exact (evenVEquiv a b ha hb).map_zero
  · exact (evenSEquiv a b rho hrho hrho0).map_zero
  · exact (evenCEquiv a b rho hrho hrho0).map_zero

/-- The normalized even pair as an actual automorphism of the recovered source
Springer algebra.-/
def sourceEvenAut (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) :=
  AlbertLean.Generic.CubicAutomorphism.sourceAutOfCubicUnit
    (evenJEquiv a b rho ha hb hrho hrho0)
    (evenJEquiv_sourceOne a b rho ha hb hrho hrho0)
    (evenJEquiv_sourceNorm a b rho ha hb hrho hrho0)

end AlbertLean.Triality.SourceEvenAutomorphism
