import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.CoordinateTensor
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceNorm_smul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceSpurPolar_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceTraceForm_nondegenerate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourcePolar_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms StructuredSourceCubicTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Source-locked structured cubic coordinates

This file is the independent source side of the cubic comparison.
It packages one literal `3 + 8 + 8 + 8` coordinate carrier and the locked
trace, spur, and cubic norm formulas.  It does not import the generated F0
tensor, define a flattening order, or identify the carrier with an Albert
algebra.  Such a comparison is deliberately a separate theorem surface.
-/

namespace AlbertLean.Triality.StructuredCubic

open ExteriorSix CoordinateTensor

/-- The literal structured `3 + 8 + 8 + 8` coordinate carrier.-/
@[ext]
structure JCoord (K : Type*) where
  d1 : K
  d2 : K
  d3 : K
  v : VCoord K
  s : SCoord K
  c : CCoord K

section LinearStructure

variable {K : Type*}

private def jCoordEquiv :
    JCoord K ≃ K × K × K × VCoord K × SCoord K × CCoord K where
  toFun x := (x.d1, x.d2, x.d3, x.v, x.s, x.c)
  invFun x :=
    { d1 := x.1
      d2 := x.2.1
      d3 := x.2.2.1
      v := x.2.2.2.1
      s := x.2.2.2.2.1
      c := x.2.2.2.2.2 }
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨d1, d2, d3, v, s, c⟩; rfl

instance [AddCommGroup K] : AddCommGroup (JCoord K) :=
  Equiv.addCommGroup (jCoordEquiv (K := K))

instance [Semiring R] [AddCommGroup K] [Module R K] : Module R (JCoord K) :=
  (Equiv.addEquiv (jCoordEquiv (K := K))).module R

/--
@isnad1 id=eq.0h3v.s5.e319d2f49c28 from=translated src=- shape=0090f101 vocab=8d0117b7
-/
@[simp] theorem add_d1 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d1 = x.d1 + y.d1 := rfl

/--
@isnad1 id=eq.0h3v.s5.68e6099a1576 from=translated src=- shape=0090f101 vocab=5a0f3793
-/
@[simp] theorem add_d2 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d2 = x.d2 + y.d2 := rfl

/--
@isnad1 id=eq.0h3v.s5.c21cc19fbc71 from=translated src=- shape=0090f101 vocab=505978e6
-/
@[simp] theorem add_d3 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d3 = x.d3 + y.d3 := rfl

/--
@isnad1 id=eq.0h3v.s6.fff5701c72b0 from=translated src=- shape=e69ef69b vocab=d3112452
-/
@[simp] theorem add_v [AddCommGroup K] (x y : JCoord K) :
    (x + y).v = x.v + y.v := rfl

/--
@isnad1 id=eq.0h3v.s6.5d7ba0c841c4 from=translated src=- shape=e69ef69b vocab=d9a5440d
-/
@[simp] theorem add_s [AddCommGroup K] (x y : JCoord K) :
    (x + y).s = x.s + y.s := rfl

/--
@isnad1 id=eq.0h3v.s6.0d50b98e7bb8 from=translated src=- shape=e69ef69b vocab=cb8cdad5
-/
@[simp] theorem add_c [AddCommGroup K] (x y : JCoord K) :
    (x + y).c = x.c + y.c := rfl

/--
@isnad1 id=eq.0h4v.s7.782ee96296ce from=translated src=- shape=4dad5650 vocab=86323857
-/
@[simp] theorem smul_d1 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d1 = a • x.d1 := rfl

/--
@isnad1 id=eq.0h4v.s7.225218c6f2c3 from=translated src=- shape=4dad5650 vocab=5b5a1306
-/
@[simp] theorem smul_d2 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d2 = a • x.d2 := rfl

/--
@isnad1 id=eq.0h4v.s7.680801bf9756 from=translated src=- shape=4dad5650 vocab=90a4a2be
-/
@[simp] theorem smul_d3 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d3 = a • x.d3 := rfl

/--
@isnad1 id=eq.0h4v.s7.d680ab86ff58 from=translated src=- shape=39484d90 vocab=ce552144
-/
@[simp] theorem smul_v [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).v = a • x.v := rfl

/--
@isnad1 id=eq.0h4v.s7.ad7fb4f4c514 from=translated src=- shape=39484d90 vocab=ed7468bb
-/
@[simp] theorem smul_s [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).s = a • x.s := rfl

/--
@isnad1 id=eq.0h4v.s7.91e845353896 from=translated src=- shape=39484d90 vocab=695f89f4
-/
@[simp] theorem smul_c [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).c = a • x.c := rfl

/--
@isnad1 id=eq.0h1v.s5.eb02e2d998b1 from=translated src=- shape=c6b7a0b8 vocab=9e932977
-/
@[simp] theorem zero_d1 [AddCommGroup K] : (0 : JCoord K).d1 = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.446d5e09d9e6 from=translated src=- shape=c6b7a0b8 vocab=3277b37d
-/
@[simp] theorem zero_d2 [AddCommGroup K] : (0 : JCoord K).d2 = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.65f22a3cf6e5 from=translated src=- shape=c6b7a0b8 vocab=331ff2ec
-/
@[simp] theorem zero_d3 [AddCommGroup K] : (0 : JCoord K).d3 = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.1e0d2839e4ec from=translated src=- shape=7b5bff60 vocab=02b063a5
-/
@[simp] theorem zero_v [AddCommGroup K] : (0 : JCoord K).v = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.63e848aab798 from=translated src=- shape=7b5bff60 vocab=1de9c35f
-/
@[simp] theorem zero_s [AddCommGroup K] : (0 : JCoord K).s = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.74ba93bc925f from=translated src=- shape=7b5bff60 vocab=a8683622
-/
@[simp] theorem zero_c [AddCommGroup K] : (0 : JCoord K).c = 0 := rfl

/--
@isnad1 id=eq.0h1v.s5.eeb7acb55637 from=translated src=- shape=c6b7a0b8 vocab=81d0bacd
-/
@[simp] theorem zero_v_r [AddCommGroup K] : (0 : VCoord K).r = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.e3bfbfe0e46a from=translated src=- shape=c6b7a0b8 vocab=2426faf1
-/
@[simp] theorem zero_v_z [AddCommGroup K] : (0 : VCoord K).z = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.165dbe24695a from=translated src=- shape=7b5bff60 vocab=acae6370
-/
@[simp] theorem zero_v_omega [AddCommGroup K] : (0 : VCoord K).omega = 0 := rfl
/--
@isnad1 id=eq.0h1v.s6.d3852fa58d98 from=translated src=- shape=7b5bff60 vocab=5be7f2e0
-/
@[simp] theorem zero_s_p [AddCommGroup K] : (0 : SCoord K).p = 0 := rfl
/--
@isnad1 id=eq.0h1v.s6.73c463c7b899 from=translated src=- shape=7b5bff60 vocab=5bd02d0a
-/
@[simp] theorem zero_s_phi [AddCommGroup K] : (0 : SCoord K).phi = 0 := rfl
/--
@isnad1 id=eq.0h1v.s6.325ac3fbb6bd from=translated src=- shape=7b5bff60 vocab=68f0ad06
-/
@[simp] theorem zero_c_q [AddCommGroup K] : (0 : CCoord K).q = 0 := rfl
/--
@isnad1 id=eq.0h1v.s6.c6f4312888db from=translated src=- shape=7b5bff60 vocab=8c6ca85c
-/
@[simp] theorem zero_c_psi [AddCommGroup K] : (0 : CCoord K).psi = 0 := rfl

end LinearStructure

section SourceCubic

variable {K : Type*} [Field K] [CharZero K]

/-- The source unit coordinate.  No multiplication structure is asserted.-/
def sourceOne : JCoord K :=
  { d1 := 1, d2 := 1, d3 := 1, v := 0, s := 0, c := 0 }

/-- A coordinate with only diagonal entries.-/
def diagonal (d1 d2 d3 : K) : JCoord K :=
  { d1 := d1, d2 := d2, d3 := d3, v := 0, s := 0, c := 0 }

/-- A coordinate with only the `V` slot populated.-/
def pureV (v : VCoord K) : JCoord K :=
  { d1 := 0, d2 := 0, d3 := 0, v := v, s := 0, c := 0 }

/-- A coordinate with only the `S` slot populated.-/
def pureS (s : SCoord K) : JCoord K :=
  { d1 := 0, d2 := 0, d3 := 0, v := 0, s := s, c := 0 }

/-- A coordinate with only the `C` slot populated.-/
def pureC (c : CCoord K) : JCoord K :=
  { d1 := 0, d2 := 0, d3 := 0, v := 0, s := 0, c := c }

/-- A coordinate with all three off-diagonal slots and zero diagonal.-/
def offDiagonal (v : VCoord K) (s : SCoord K) (c : CCoord K) : JCoord K :=
  { d1 := 0, d2 := 0, d3 := 0, v := v, s := s, c := c }

/-- The locked source trace formula.-/
def sourceTrace (x : JCoord K) : K := x.d1 + x.d2 + x.d3

/-- The locked source quadratic spur formula.-/
def sourceSpur (x : JCoord K) : K :=
  x.d1 * x.d2 + x.d1 * x.d3 + x.d2 * x.d3
    - nV x.v - nS x.s - nC x.c

/-- The locked source cubic norm formula.-/
def sourceNorm (x : JCoord K) : K :=
  x.d1 * x.d2 * x.d3
    - x.d1 * nV x.v - x.d2 * nS x.s - x.d3 * nC x.c
    + triality x.v x.s x.c

/-- The symmetric polarization of the quadratic spur.-/
def sourceSpurPolar (x y : JCoord K) : K :=
  sourceSpur (x + y) - sourceSpur x - sourceSpur y

/-- The finite-difference polarization of the cubic norm.-/
def sourcePolar (x y z : JCoord K) : K :=
  sourceNorm (x + y + z)
    - sourceNorm (x + y) - sourceNorm (x + z) - sourceNorm (y + z)
    + sourceNorm x + sourceNorm y + sourceNorm z

/-- The source trace form used by cubic-norm product recovery.-/
def sourceTraceForm (x y : JCoord K) : K :=
  sourceTrace x * sourceTrace y - sourceSpurPolar x y

/--
@isnad1 id=eq.0h2v.s6.e29e653e2618 from=translated src=- shape=e04c8fd4 vocab=3c204257
-/
theorem sourceTrace_formula (x : JCoord K) :
    sourceTrace x = x.d1 + x.d2 + x.d3 := rfl

/--
@isnad1 id=eq.0h2v.s7.af2d20038e31 from=translated src=- shape=ce246310 vocab=e5fcefa4
-/
theorem sourceSpur_formula (x : JCoord K) :
    sourceSpur x =
      x.d1 * x.d2 + x.d1 * x.d3 + x.d2 * x.d3
        - nV x.v - nS x.s - nC x.c := rfl

/--
@isnad1 id=eq.0h2v.s7.2a5b5aade4bc from=translated src=- shape=4514e83a vocab=40b1d879
-/
theorem sourceNorm_formula (x : JCoord K) :
    sourceNorm x =
      x.d1 * x.d2 * x.d3
        - x.d1 * nV x.v - x.d2 * nS x.s - x.d3 * nC x.c
        + triality x.v x.s x.c := rfl

/--
@isnad1 id=eq.0h3v.s6.ed0ae542af5b from=translated src=- shape=dfd2aa99 vocab=d05a487c
-/
theorem nS_add (s t : SCoord K) : nS (s + t) = nS s + nS t + BS s t := by
  simp [nS, BS, evalU]
  ring

/--
@isnad1 id=eq.0h3v.s6.e5b229e3d4c8 from=translated src=- shape=dfd2aa99 vocab=ccaaba13
-/
theorem nC_add (c d : CCoord K) : nC (c + d) = nC c + nC d + BC c d := by
  simp [nC, BC, evalU]
  ring

/--
@isnad1 id=eq.0h3v.s7.6f843638d893 from=translated src=- shape=09bc91e2 vocab=9d945a34
-/
theorem nS_smul (a : K) (s : SCoord K) : nS (a • s) = a ^ 2 * nS s := by
  simp [nS, evalU]
  ring

/--
@isnad1 id=eq.0h3v.s7.0a687d604b36 from=translated src=- shape=09bc91e2 vocab=d908bf55
-/
theorem nC_smul (a : K) (c : CCoord K) : nC (a • c) = a ^ 2 * nC c := by
  simp [nC, evalU]
  ring

/--
@isnad1 id=eq.0h5v.s9.28592cf625e3 from=translated src=- shape=75404580 vocab=14c7c573
-/
theorem triality_smul_all (a : K) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (a • v) (a • s) (a • c) = a ^ 3 * triality v s c := by
  rw [triality_smul_v, triality_smul_s, triality_smul_c]
  ring

/--
@isnad1 id=eq.0h3v.s7.a52beda7cc7b from=translated src=- shape=5a4b5452 vocab=432fc56d
-/
theorem sourceTrace_smul (a : K) (x : JCoord K) :
    sourceTrace (a • x) = a * sourceTrace x := by
  simp [sourceTrace]
  ring

/--
@isnad1 id=eq.0h3v.s7.9bcd63570a47 from=translated src=- shape=09bc91e2 vocab=93b5453b
-/
theorem sourceSpur_smul (a : K) (x : JCoord K) :
    sourceSpur (a • x) = a ^ 2 * sourceSpur x := by
  simp only [sourceSpur, smul_d1, smul_d2, smul_d3, smul_eq_mul, smul_v,
    smul_s, smul_c, nV_smul, nS_smul, nC_smul]
  ring

/-- Cubic homogeneity of the independently locked source norm.
@isnad1 id=eq.0h3v.s7.573ded6cf994 from=translated src=- shape=09bc91e2 vocab=9cc14fc5
-/
theorem sourceNorm_smul (a : K) (x : JCoord K) :
    sourceNorm (a • x) = a ^ 3 * sourceNorm x := by
  simp only [sourceNorm, smul_d1, smul_d2, smul_d3, smul_eq_mul, smul_v,
    smul_s, smul_c, nV_smul, nS_smul, nC_smul, triality_smul_all]
  ring

/--
@isnad1 id=eq.0h1v.s6.1f01da4cfe23 from=translated src=- shape=d4e3877e vocab=24f1f80b
-/
@[simp] theorem nV_zero : nV (0 : VCoord K) = 0 := by
  simp [nV, Pf, BW]

/--
@isnad1 id=eq.0h1v.s6.854b67d53fb0 from=translated src=- shape=d4e3877e vocab=2cdef3b4
-/
@[simp] theorem nS_zero : nS (0 : SCoord K) = 0 := by
  simp [nS, evalU]

/--
@isnad1 id=eq.0h1v.s6.333d8f899cab from=translated src=- shape=d4e3877e vocab=fc90bc44
-/
@[simp] theorem nC_zero : nC (0 : CCoord K) = 0 := by
  simp [nC, evalU]

/--
@isnad1 id=eq.0h2v.s6.693fbc58099d from=translated src=- shape=321750df vocab=0c30bac1
-/
@[simp] theorem BV_zero_right (v : VCoord K) : BV v 0 = 0 := by
  simp [BV, BW]

/--
@isnad1 id=eq.0h2v.s6.4cf027bb3e16 from=translated src=- shape=321750df vocab=d0512645
-/
@[simp] theorem BS_zero_right (s : SCoord K) : BS s 0 = 0 := by
  simp [BS, evalU]

/--
@isnad1 id=eq.0h2v.s6.8a9bc90f77bc from=translated src=- shape=321750df vocab=4da53a37
-/
@[simp] theorem BC_zero_right (c : CCoord K) : BC c 0 = 0 := by
  simp [BC, evalU]

/--
@isnad1 id=eq.0h2v.s6.e0cf05d4a189 from=translated src=- shape=addd94b6 vocab=0c30bac1
-/
@[simp] theorem BV_zero_left (v : VCoord K) : BV 0 v = 0 := by
  rw [BV_symmetric]
  exact BV_zero_right v

/--
@isnad1 id=eq.0h2v.s6.81fde010c276 from=translated src=- shape=addd94b6 vocab=d0512645
-/
@[simp] theorem BS_zero_left (s : SCoord K) : BS 0 s = 0 := by
  rw [BS_symmetric]
  exact BS_zero_right s

/--
@isnad1 id=eq.0h2v.s6.23884e68035d from=translated src=- shape=addd94b6 vocab=4da53a37
-/
@[simp] theorem BC_zero_left (c : CCoord K) : BC 0 c = 0 := by
  rw [BC_symmetric]
  exact BC_zero_right c

/--
@isnad1 id=eq.0h3v.s6.f7be2eb80fa4 from=translated src=- shape=f9a1af20 vocab=4bd9a0e7
-/
@[simp] theorem triality_zero_v (s : SCoord K) (c : CCoord K) :
    triality (0 : VCoord K) s c = 0 := by
  simp [triality, BW, pairW]

/--
@isnad1 id=eq.0h3v.s6.1598aad06ea8 from=translated src=- shape=44b65411 vocab=4bd9a0e7
-/
@[simp] theorem triality_zero_s (v : VCoord K) (c : CCoord K) :
    triality v (0 : SCoord K) c = 0 := by
  simp [triality, evalU, BW, pairW, wedge2, dualWedge2]

/--
@isnad1 id=eq.0h3v.s6.8acd47e5751d from=translated src=- shape=6ada60b6 vocab=4bd9a0e7
-/
@[simp] theorem triality_zero_c (v : VCoord K) (s : SCoord K) :
    triality v s (0 : CCoord K) = 0 := by
  simp [triality, evalU, BW, pairW, wedge2, dualWedge2]

/--
@isnad1 id=eq.0h1v.s5.ce3dc1d0542a from=translated src=- shape=e9245790 vocab=e08c62a0
-/
@[simp] theorem sourceTrace_one : sourceTrace (sourceOne : JCoord K) = 3 := by
  simp [sourceTrace, sourceOne]
  ring

/--
@isnad1 id=eq.0h1v.s5.67d6897c5130 from=translated src=- shape=e9245790 vocab=a2b8c0ec
-/
@[simp] theorem sourceSpur_one : sourceSpur (sourceOne : JCoord K) = 3 := by
  simp [sourceSpur, sourceOne]
  ring

/--
@isnad1 id=eq.0h1v.s5.c4950f370c61 from=translated src=- shape=e9245790 vocab=729ed7a7
-/
@[simp] theorem sourceNorm_one : sourceNorm (sourceOne : JCoord K) = 1 := by
  simp [sourceNorm, sourceOne]

/--
@isnad1 id=and.0h4v.s7.6c84240318c4 from=translated src=- shape=7726f1b5 vocab=526e176a
-/
theorem source_diagonal_restrictions (d1 d2 d3 : K) :
    sourceTrace (diagonal d1 d2 d3) = d1 + d2 + d3 ∧
    sourceSpur (diagonal d1 d2 d3) = d1 * d2 + d1 * d3 + d2 * d3 ∧
    sourceNorm (diagonal d1 d2 d3) = d1 * d2 * d3 := by
  simp [sourceTrace, sourceSpur, sourceNorm, diagonal, nV, nS, nC, triality,
    Pf, evalU, BW, pairW, wedge2, dualWedge2]

/--
@isnad1 id=and.0h2v.s6.3ad59c422975 from=translated src=- shape=0d47ae90 vocab=f918314c
-/
theorem source_pureV_restrictions (v : VCoord K) :
    sourceTrace (pureV v) = 0 ∧ sourceSpur (pureV v) = -nV v ∧
      sourceNorm (pureV v) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureV, nS, nC, triality,
    evalU, BW, pairW, wedge2, dualWedge2]

/--
@isnad1 id=and.0h2v.s6.aded72b8e0af from=translated src=- shape=0d47ae90 vocab=047ff80b
-/
theorem source_pureS_restrictions (s : SCoord K) :
    sourceTrace (pureS s) = 0 ∧ sourceSpur (pureS s) = -nS s ∧
      sourceNorm (pureS s) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureS, nV, nC, triality,
    Pf, evalU, BW, pairW]

/--
@isnad1 id=and.0h2v.s6.8dd7b3d6a177 from=translated src=- shape=0d47ae90 vocab=162ac8e5
-/
theorem source_pureC_restrictions (c : CCoord K) :
    sourceTrace (pureC c) = 0 ∧ sourceSpur (pureC c) = -nC c ∧
      sourceNorm (pureC c) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureC, nV, nS, triality,
    Pf, evalU, BW, pairW]

/--
@isnad1 id=and.0h4v.s7.90ebcbdb2430 from=translated src=- shape=d096ddfe vocab=740f4b87
-/
theorem source_offDiagonal_restrictions (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    sourceTrace (offDiagonal v s c) = 0 ∧
    sourceSpur (offDiagonal v s c) = -nV v - nS s - nC c ∧
    sourceNorm (offDiagonal v s c) = triality v s c := by
  simp [sourceTrace, sourceSpur, sourceNorm, offDiagonal]

/-- Explicit symmetric spur polarization, separated from cubic polarization.
@isnad1 id=eq.0h3v.s8.22ca4c9d9b99 from=translated src=- shape=394e7efe vocab=db007993
-/
theorem sourceSpurPolar_formula (x y : JCoord K) :
    sourceSpurPolar x y =
      x.d1 * y.d2 + y.d1 * x.d2
      + x.d1 * y.d3 + y.d1 * x.d3
      + x.d2 * y.d3 + y.d2 * x.d3
      - BV x.v y.v - BS x.s y.s - BC x.c y.c := by
  simp only [sourceSpurPolar, sourceSpur, add_d1, add_d2, add_d3, add_v, add_s,
    add_c, nV_add, nS_add, nC_add]
  ring

/--
@isnad1 id=eq.0h3v.s5.c75580f1b041 from=translated src=- shape=1bf5b2d1 vocab=6746ddd9
-/
theorem sourceSpurPolar_symmetric (x y : JCoord K) :
    sourceSpurPolar x y = sourceSpurPolar y x := by
  rw [sourceSpurPolar_formula, sourceSpurPolar_formula, BV_symmetric, BS_symmetric,
    BC_symmetric]
  ring

/--
@isnad1 id=eq.0h2v.s6.63c9b1616309 from=translated src=- shape=19ceee7b vocab=0ce65ab2
-/
theorem sourceSpurPolar_diagonal (x : JCoord K) :
    sourceSpurPolar x x = 2 * sourceSpur x := by
  rw [sourceSpurPolar_formula, BV_self_eq_two_nV, BS_self_eq_two_nS,
    BC_self_eq_two_nC]
  simp only [sourceSpur]
  ring

/--
@isnad1 id=eq.0h3v.s7.8bb2d9e34088 from=translated src=- shape=fc21a5d9 vocab=d173dceb
-/
theorem sourceTraceForm_formula (x y : JCoord K) :
    sourceTraceForm x y =
      x.d1 * y.d1 + x.d2 * y.d2 + x.d3 * y.d3
        + BV x.v y.v + BS x.s y.s + BC x.c y.c := by
  rw [sourceTraceForm, sourceSpurPolar_formula]
  simp only [sourceTrace]
  ring

/--
@isnad1 id=eq.0h3v.s5.cd88d10aee9b from=translated src=- shape=1bf5b2d1 vocab=59140c12
-/
theorem sourceTraceForm_symmetric (x y : JCoord K) :
    sourceTraceForm x y = sourceTraceForm y x := by
  rw [sourceTraceForm_formula, sourceTraceForm_formula, BV_symmetric, BS_symmetric,
    BC_symmetric]
  ring

/--
@isnad1 id=eq.0h2v.s5.0b15793a24a9 from=translated src=- shape=b689e310 vocab=2626d21b
-/
theorem sourceTraceForm_one_left (x : JCoord K) :
    sourceTraceForm (sourceOne : JCoord K) x = sourceTrace x := by
  rw [sourceTraceForm_formula]
  simp [sourceOne, sourceTrace]

/--
@isnad1 id=eq.1h2v.s6.a6c52b765313 from=translated src=- shape=59d462ba vocab=0c30bac1
-/
theorem BV_nondegenerate {v : VCoord K} (h : ∀ w : VCoord K, BV v w = 0) :
    v = 0 := by
  have hr : v.r = 0 := by
    have hv := h ({ r := 0, z := 1, omega := 0 } : VCoord K)
    simpa [BV, BW] using hv
  have hz : v.z = 0 := by
    have hv := h ({ r := 1, z := 0, omega := 0 } : VCoord K)
    simpa [BV, BW] using hv
  have homega : v.omega = 0 := by
    apply BW_nondegenerate
    intro w
    have hv := h ({ r := 0, z := 0, omega := w } : VCoord K)
    simpa [BV] using hv
  change v = ({ r := 0, z := 0, omega := 0 } : VCoord K)
  exact VCoord.ext hr hz homega

/-- The source trace form is nondegenerate on all 27 literal coordinates.
@isnad1 id=eq.1h2v.s6.ad93b488645e from=translated src=- shape=59d462ba vocab=59140c12
-/
theorem sourceTraceForm_nondegenerate {x : JCoord K}
    (h : ∀ y : JCoord K, sourceTraceForm x y = 0) : x = 0 := by
  have hd1 : x.d1 = 0 := by
    have hx := h (diagonal 1 0 0)
    rw [sourceTraceForm_formula] at hx
    simpa [diagonal] using hx
  have hd2 : x.d2 = 0 := by
    have hx := h (diagonal 0 1 0)
    rw [sourceTraceForm_formula] at hx
    simpa [diagonal] using hx
  have hd3 : x.d3 = 0 := by
    have hx := h (diagonal 0 0 1)
    rw [sourceTraceForm_formula] at hx
    simpa [diagonal] using hx
  have hv : x.v = 0 := by
    apply BV_nondegenerate
    intro v
    have hx := h (pureV v)
    rw [sourceTraceForm_formula] at hx
    simpa [pureV] using hx
  have hs : x.s = 0 := by
    apply BS_nondegenerate
    intro s
    have hx := h (pureS s)
    rw [sourceTraceForm_formula] at hx
    simpa [pureS] using hx
  have hc : x.c = 0 := by
    apply BC_nondegenerate
    intro c
    have hx := h (pureC c)
    rw [sourceTraceForm_formula] at hx
    simpa [pureC] using hx
  change x =
    ({ d1 := 0, d2 := 0, d3 := 0, v := 0, s := 0, c := 0 } : JCoord K)
  exact JCoord.ext hd1 hd2 hd3 hv hs hc

/--
@isnad1 id=eq.0h4v.s5.54966104a2b9 from=translated src=- shape=8cb4d701 vocab=ed8abc75
-/
theorem sourcePolar_swap_left (x y z : JCoord K) :
    sourcePolar x y z = sourcePolar y x z := by
  simp only [sourcePolar]
  have hxyz : y + x + z = x + y + z := by abel
  have hxy : y + x = x + y := add_comm _ _
  rw [hxyz, hxy]
  ring

/--
@isnad1 id=eq.0h4v.s5.74692c5f0414 from=translated src=- shape=f46dec1a vocab=ed8abc75
-/
theorem sourcePolar_swap_right (x y z : JCoord K) :
    sourcePolar x y z = sourcePolar x z y := by
  simp only [sourcePolar]
  have hxyz : x + z + y = x + y + z := by abel
  have hzy : z + y = y + z := add_comm _ _
  rw [hxyz, hzy]
  ring

/-- Polarizing the cubic once at the source unit recovers the spur polarization.
@isnad1 id=eq.0h3v.s5.aa1103200485 from=translated src=- shape=0afbaee1 vocab=c25cac24
-/
theorem sourcePolar_one (x y : JCoord K) :
    sourcePolar (sourceOne : JCoord K) x y = sourceSpurPolar x y := by
  simp only [sourcePolar, sourceSpurPolar_formula, sourceNorm, sourceOne, add_d1,
    add_d2, add_d3, add_v, add_s, add_c, nV_add, nS_add, nC_add,
    triality_add_v, triality_add_s, triality_add_c, nV_zero, nS_zero, nC_zero,
    triality_zero_c, zero_add]
  ring

/--
@isnad1 id=eq.0h2v.s6.71ee0113177a from=translated src=- shape=af597d50 vocab=c936ec09
-/
theorem sourcePolar_diagonal (x : JCoord K) : sourcePolar x x x = 6 * sourceNorm x := by
  have h2 : x + x = (2 : K) • x := by
    ext <;> simp <;> ring
  have h3 : x + x + x = (3 : K) • x := by
    ext <;> simp <;> ring
  rw [sourcePolar, h3, h2, sourceNorm_smul, sourceNorm_smul]
  ring

/--
Source-only capstone.  It binds the unit values, cubic homogeneity, complete
diagonal/off-diagonal restrictions, explicit trace-form formula, and
nondegeneracy without any use of generated F0 comparison data.
@isnad1 id=and.0h1v.s9.d95116fea18c from=translated src=- shape=22e9a5f0 vocab=15bc5928
-/
theorem StructuredSourceCubicTheorem :
    sourceTrace (sourceOne : JCoord K) = 3 ∧
    sourceSpur (sourceOne : JCoord K) = 3 ∧
    sourceNorm (sourceOne : JCoord K) = 1 ∧
    (∀ (a : K) (x : JCoord K), sourceNorm (a • x) = a ^ 3 * sourceNorm x) ∧
    (∀ x y : JCoord K,
      sourceTraceForm x y =
        x.d1 * y.d1 + x.d2 * y.d2 + x.d3 * y.d3
          + BV x.v y.v + BS x.s y.s + BC x.c y.c) ∧
    (∀ x : JCoord K, (∀ y : JCoord K, sourceTraceForm x y = 0) → x = 0) ∧
    (∀ d1 d2 d3 : K,
      sourceTrace (diagonal d1 d2 d3) = d1 + d2 + d3 ∧
      sourceSpur (diagonal d1 d2 d3) = d1 * d2 + d1 * d3 + d2 * d3 ∧
      sourceNorm (diagonal d1 d2 d3) = d1 * d2 * d3) ∧
    (∀ (v : VCoord K) (s : SCoord K) (c : CCoord K),
      sourceTrace (offDiagonal v s c) = 0 ∧
      sourceSpur (offDiagonal v s c) = -nV v - nS s - nC c ∧
      sourceNorm (offDiagonal v s c) = triality v s c) := by
  exact ⟨sourceTrace_one, sourceSpur_one, sourceNorm_one, sourceNorm_smul,
    sourceTraceForm_formula, fun _ => sourceTraceForm_nondegenerate,
    source_diagonal_restrictions, source_offDiagonal_restrictions⟩

end SourceCubic

end AlbertLean.Triality.StructuredCubic
