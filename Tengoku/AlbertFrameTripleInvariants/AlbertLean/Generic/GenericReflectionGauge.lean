import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms theta_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms triality_theta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceNorm_theta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceProduct_theta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAut` (it only prints; the queue checks the axioms of every declaration). -/

/-! The corrected reflection exchanges the two scalar
triality terms, and exchanges BW with pairW. All calculations are confined to
the three eight-dimensional slots before the cubic recovery theorem is used. -/
noncomputable section
namespace AlbertLean.Generic.GenericReflectionGauge

open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Triality.ExteriorSix

variable {K : Type*} [Field K] [CharZero K]

def thetaV (a : K) (v : VCoord K) : VCoord K where
  r := v.z / a
  z := a * v.r
  omega := fun
    | .i12 => v.omega .i34 / a
    | .i13 => -v.omega .i24
    | .i14 => v.omega .i23
    | .i23 => v.omega .i14
    | .i24 => -v.omega .i13
    | .i34 => a * v.omega .i12

def thetaS (a : K) (s : SCoord K) : SCoord K where
  p := ![s.phi 0 / a, s.phi 1 / a, s.phi 2, s.phi 3]
  phi := ![a * s.p 0, a * s.p 1, s.p 2, s.p 3]

def thetaC (a : K) (c : CCoord K) : CCoord K where
  q := ![c.psi 0, c.psi 1, a * c.psi 2, a * c.psi 3]
  psi := ![c.q 0, c.q 1, c.q 2 / a, c.q 3 / a]

def theta (a : K) (x : JCoord K) : JCoord K where
  d1 := x.d1
  d2 := x.d2
  d3 := x.d3
  v := thetaV a x.v
  s := thetaS a x.s
  c := thetaC a x.c

/--
@isnad1 id=eq.0h4v.s6.c8191cc463ff from=translated src=- shape=a0986e98 vocab=69a20cbf
-/
theorem thetaV_add (a : K) (v w : VCoord K) :
    thetaV a (v + w) = thetaV a v + thetaV a w := by
  apply VCoord.ext
  · simp [thetaV, add_div]
  · simp [thetaV, mul_add]
  · funext i
    cases i <;> simp [thetaV, add_div, mul_add, add_comm]

/--
@isnad1 id=eq.0h4v.s6.673851eb42f6 from=translated src=- shape=a0986e98 vocab=0cd04caa
-/
theorem thetaS_add (a : K) (s t : SCoord K) :
    thetaS a (s + t) = thetaS a s + thetaS a t := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [thetaS, add_div, mul_add]

/--
@isnad1 id=eq.0h4v.s6.6801927797b1 from=translated src=- shape=a0986e98 vocab=148e86ff
-/
theorem thetaC_add (a : K) (c d : CCoord K) :
    thetaC a (c + d) = thetaC a c + thetaC a d := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [thetaC, add_div, mul_add]

/--
@isnad1 id=eq.0h4v.s8.ef18c4385169 from=translated src=- shape=3bf57de3 vocab=c8623c96
-/
theorem thetaV_smul (a b : K) (v : VCoord K) :
    thetaV a (b • v) = b • thetaV a v := by
  apply VCoord.ext
  · simp [thetaV, smul_eq_mul, mul_div_assoc]
  · simp [thetaV, smul_eq_mul, mul_left_comm]
  · funext i
    cases i <;> simp [thetaV, smul_eq_mul, mul_div_assoc, mul_left_comm]

/--
@isnad1 id=eq.0h4v.s8.436e5ba0c28c from=translated src=- shape=3bf57de3 vocab=02cbffe2
-/
theorem thetaS_smul (a b : K) (s : SCoord K) :
    thetaS a (b • s) = b • thetaS a s := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [thetaS, smul_eq_mul, mul_div_assoc, mul_left_comm]

/--
@isnad1 id=eq.0h4v.s8.02d94f1b1729 from=translated src=- shape=3bf57de3 vocab=3a78fbae
-/
theorem thetaC_smul (a b : K) (c : CCoord K) :
    thetaC a (b • c) = b • thetaC a c := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [thetaC, smul_eq_mul, mul_div_assoc, mul_left_comm]

/--
@isnad1 id=eq.0h4v.s6.3ab141af88bb from=translated src=- shape=a0986e98 vocab=6d4e5306
-/
theorem theta_add (a : K) (x y : JCoord K) :
    theta a (x + y) = theta a x + theta a y := by
  apply JCoord.ext <;> simp [theta, thetaV_add, thetaS_add, thetaC_add]

/--
@isnad1 id=eq.0h4v.s8.1f4353721db6 from=translated src=- shape=3bf57de3 vocab=a67d6071
-/
theorem theta_smul (a b : K) (x : JCoord K) :
    theta a (b • x) = b • theta a x := by
  apply JCoord.ext <;> simp [theta, thetaV_smul, thetaS_smul, thetaC_smul]

/--
@isnad1 id=eq.1h3v.s5.1c9670c238d1 from=translated src=- shape=d448cfa0 vocab=06bcbf5d
-/
theorem thetaV_involutive (a : K) (ha : a ≠ 0) (v : VCoord K) :
    thetaV a (thetaV a v) = v := by
  apply VCoord.ext
  · simp [thetaV, ha] <;> field_simp
  · simp [thetaV, ha] <;> field_simp
  · funext i
    cases i <;> simp [thetaV, ha] <;> field_simp

/--
@isnad1 id=eq.1h3v.s5.135bb4ee8454 from=translated src=- shape=d448cfa0 vocab=2348bcea
-/
theorem thetaS_involutive (a : K) (ha : a ≠ 0) (s : SCoord K) :
    thetaS a (thetaS a s) = s := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;> simp [thetaS, ha] <;> field_simp

/--
@isnad1 id=eq.1h3v.s5.c7e96d7dc694 from=translated src=- shape=d448cfa0 vocab=4592d1f8
-/
theorem thetaC_involutive (a : K) (ha : a ≠ 0) (c : CCoord K) :
    thetaC a (thetaC a c) = c := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;> simp [thetaC, ha] <;> field_simp

/--
@isnad1 id=eq.1h3v.s5.e669ec4cc361 from=translated src=- shape=d448cfa0 vocab=00d76d8e
-/
theorem theta_involutive (a : K) (ha : a ≠ 0) (x : JCoord K) :
    theta a (theta a x) = x := by
  exact JCoord.ext rfl rfl rfl (thetaV_involutive a ha x.v)
    (thetaS_involutive a ha x.s) (thetaC_involutive a ha x.c)

def linearEquiv (a : K) (ha : a ≠ 0) : JCoord K ≃ₗ[K] JCoord K where
  toFun := theta a
  invFun := theta a
  left_inv := theta_involutive a ha
  right_inv := theta_involutive a ha
  map_add' := theta_add a
  map_smul' := theta_smul a

/--
@isnad1 id=eq.1h3v.s8.2c54d35cd08f from=translated src=- shape=ad50d2c5 vocab=d109b46f
-/
@[simp] theorem linearEquiv_apply (a : K) (ha : a ≠ 0) (x : JCoord K) :
    linearEquiv a ha x = theta a x := rfl

/--
@isnad1 id=eq.1h3v.s5.5d40f55c0c81 from=translated src=- shape=011428b1 vocab=c11de322
-/
theorem nV_thetaV (a : K) (ha : a ≠ 0) (v : VCoord K) :
    nV (thetaV a v) = nV v := by
  simp only [nV, pf_coordinate, thetaV]
  field_simp [ha] <;> ring

/--
@isnad1 id=eq.1h3v.s5.3a89b1b12b5c from=translated src=- shape=011428b1 vocab=61411728
-/
theorem nS_thetaS (a : K) (ha : a ≠ 0) (s : SCoord K) :
    nS (thetaS a s) = nS s := by
  simp [nS, evalU, thetaS]
  field_simp [ha] <;> ring

/--
@isnad1 id=eq.1h3v.s5.642a2d26ae16 from=translated src=- shape=011428b1 vocab=0423694f
-/
theorem nC_thetaC (a : K) (ha : a ≠ 0) (c : CCoord K) :
    nC (thetaC a c) = nC c := by
  simp [nC, evalU, thetaC]
  field_simp [ha] <;> ring

/--
@isnad1 id=eq.1h5v.s6.1e189529e4f5 from=translated src=- shape=afafb2c8 vocab=65f1f955
-/
theorem scalar_first_theta (a : K) (ha : a ≠ 0)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    (thetaV a v).r * evalU (thetaS a s).phi (thetaC a c).q =
      v.z * evalU c.psi s.p := by
  simp [thetaV, thetaS, thetaC, evalU]
  field_simp [ha] <;> ring

/--
@isnad1 id=eq.1h5v.s6.2e3277fd0ae2 from=translated src=- shape=0d72fffa vocab=65f1f955
-/
theorem scalar_second_theta (a : K) (ha : a ≠ 0)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    (thetaV a v).z * evalU (thetaC a c).psi (thetaS a s).p =
      v.r * evalU s.phi c.q := by
  have h := scalar_first_theta a ha (thetaV a v) (thetaS a s) (thetaC a c)
  simpa only [thetaV_involutive a ha, thetaS_involutive a ha,
    thetaC_involutive a ha] using h.symm

/--
@isnad1 id=eq.1h5v.s6.79a5a092fb26 from=translated src=- shape=85d56c9a vocab=b96f129b
-/
theorem BW_theta (a : K) (ha : a ≠ 0)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    BW (thetaV a v).omega (wedge2 (thetaS a s).p (thetaC a c).q) =
      pairW v.omega (dualWedge2 s.phi c.psi) := by
  simp [thetaV, thetaS, thetaC, BW, wedge2, pairW, dualWedge2]
  field_simp [ha] <;> ring

/--
@isnad1 id=eq.1h5v.s6.6cffdb1a4f8b from=translated src=- shape=85d56c9a vocab=b96f129b
-/
theorem pairW_theta (a : K) (ha : a ≠ 0)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    pairW (thetaV a v).omega (dualWedge2 (thetaS a s).phi (thetaC a c).psi) =
      BW v.omega (wedge2 s.p c.q) := by
  have h := BW_theta a ha (thetaV a v) (thetaS a s) (thetaC a c)
  simpa only [thetaV_involutive a ha, thetaS_involutive a ha,
    thetaC_involutive a ha] using h.symm

/--
@isnad1 id=eq.1h5v.s6.7251da2fd5f5 from=translated src=- shape=c224430c vocab=02d89a04
-/
theorem triality_theta (a : K) (ha : a ≠ 0)
    (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (thetaV a v) (thetaS a s) (thetaC a c) = triality v s c := by
  simp only [triality, scalar_first_theta a ha, scalar_second_theta a ha,
    BW_theta a ha, pairW_theta a ha]
  ring

/--
@isnad1 id=eq.1h3v.s5.ca321b823d16 from=translated src=- shape=011428b1 vocab=dc96d253
-/
theorem sourceNorm_theta (a : K) (ha : a ≠ 0) (x : JCoord K) :
    sourceNorm (theta a x) = sourceNorm x := by
  simp only [sourceNorm, theta, nV_thetaV a ha, nS_thetaS a ha,
    nC_thetaC a ha, triality_theta a ha]

/--
@isnad1 id=eq.0h2v.s5.88c70bac1ee8 from=translated src=- shape=24646ca3 vocab=d1efd1fd
-/
@[simp] theorem sourceOne_theta (a : K) :
    theta a (sourceOne : JCoord K) = sourceOne := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext
    · simp [theta, thetaV, sourceOne]
    · simp [theta, thetaV, sourceOne]
    · funext i
      cases i <;> simp [theta, thetaV, sourceOne]
  · apply SCoord.ext <;> funext i <;> fin_cases i <;>
      simp [theta, thetaS, sourceOne]
  · apply CCoord.ext <;> funext i <;> fin_cases i <;>
      simp [theta, thetaC, sourceOne]

/--
@isnad1 id=eq.0h3v.s5.790b10b6ba21 from=translated src=- shape=ff33cf9b vocab=0f1b3777
-/
theorem sourceTrace_theta (a : K) (x : JCoord K) :
    sourceTrace (theta a x) = sourceTrace x := rfl

/--
@isnad1 id=eq.1h4v.s6.8af414ba291d from=translated src=- shape=ab007a41 vocab=8434152f
-/
theorem sourceProduct_theta (a : K) (ha : a ≠ 0) (x y : JCoord K) :
    theta a (sourceProduct x y) = sourceProduct (theta a x) (theta a y) := by
  exact CubicAutomorphism.sourceProduct_invariant_of_cubic_unit
    (linearEquiv a ha) (sourceOne_theta a) (sourceNorm_theta a ha) x y

def sourceAut (a : K) (ha : a ≠ 0) : ResidualAction.SourceAut (K := K) where
  linear := linearEquiv a ha
  map_one := sourceOne_theta a
  map_product := sourceProduct_theta a ha

end AlbertLean.Generic.GenericReflectionGauge
