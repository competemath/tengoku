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

/--
@isnad1 id=eq.0h4v.s6.740ec0e45b95 from=translated src=- shape=b399cc4f vocab=fb524301
-/
theorem reflectV_add (a v w : VCoord K) :
    reflectV a (v + w) = reflectV a v + reflectV a w := by
  rw [reflectV, reflectV, reflectV, BV_add_right]
  module

/--
@isnad1 id=eq.0h4v.s8.3564fd1e2429 from=translated src=- shape=eb41e40a vocab=019f44b4
-/
theorem reflectV_smul (a v : VCoord K) (k : K) :
    reflectV a (k • v) = k • reflectV a v := by
  rw [reflectV, reflectV, BV_smul_right]
  module

/--
@isnad1 id=eq.1h3v.s6.606137ee8d58 from=translated src=- shape=6aab0813 vocab=d5139c86
-/
theorem BV_reflectV (a v : VCoord K) (ha : nV a ≠ 0) :
    BV a (reflectV a v) = -BV a v := by
  rw [reflectV, sub_eq_add_neg, ← neg_smul, BV_add_right,
    BV_smul_right, BV_self_eq_two_nV]
  field_simp [ha]
  ring

/--
@isnad1 id=eq.1h3v.s5.c08be15a3ee4 from=translated src=- shape=5db8a7e4 vocab=ae3db609
-/
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

/--
@isnad1 id=eq.0h4v.s8.903627b48e2d from=translated src=- shape=12c62803 vocab=c9919af5
-/
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

/--
@isnad1 id=eq.0h5v.s8.08e4935954bf from=translated src=- shape=aa7addc0 vocab=dee59d72
-/
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

/--
@isnad1 id=eq.0h5v.s8.ca47465181e7 from=translated src=- shape=aa7addc0 vocab=97fe10a7
-/
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

/--
@isnad1 id=eq.4h5v.s9.20b1267fc49f from=translated src=- shape=48db9e77 vocab=2a3d231f
-/
@[simp] theorem evenJEquiv_apply (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) (x : JCoord K) :
    evenJEquiv a b rho ha hb hrho hrho0 x =
      { d1 := x.d1, d2 := x.d2, d3 := x.d3
        v := evenV a b x.v
        s := evenS a b rho x.s
        c := evenC a b rho x.c } := rfl

/--
@isnad1 id=eq.4h5v.s9.741c3d5f400d from=translated src=- shape=e2085e8d vocab=a6eb9280
-/
theorem evenJEquiv_sourceNorm (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0) (x : JCoord K) :
    sourceNorm (evenJEquiv a b rho ha hb hrho hrho0 x) = sourceNorm x := by
  rw [evenJEquiv_apply, sourceNorm_formula, sourceNorm_formula,
    nV_evenV a b x.v ha hb, nS_evenS a b rho x.s hrho hrho0,
    nC_evenC a b rho x.c hrho hrho0,
    triality_even a b rho x.v x.s x.c ha hb hrho hrho0]

/--
@isnad1 id=eq.4h4v.s9.610a98874ed5 from=translated src=- shape=e4952d10 vocab=27e7c190
-/
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
