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

@[simp] theorem add_d1 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d1 = x.d1 + y.d1 := rfl

@[simp] theorem add_d2 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d2 = x.d2 + y.d2 := rfl

@[simp] theorem add_d3 [AddCommGroup K] (x y : JCoord K) :
    (x + y).d3 = x.d3 + y.d3 := rfl

@[simp] theorem add_v [AddCommGroup K] (x y : JCoord K) :
    (x + y).v = x.v + y.v := rfl

@[simp] theorem add_s [AddCommGroup K] (x y : JCoord K) :
    (x + y).s = x.s + y.s := rfl

@[simp] theorem add_c [AddCommGroup K] (x y : JCoord K) :
    (x + y).c = x.c + y.c := rfl

@[simp] theorem smul_d1 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d1 = a • x.d1 := rfl

@[simp] theorem smul_d2 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d2 = a • x.d2 := rfl

@[simp] theorem smul_d3 [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).d3 = a • x.d3 := rfl

@[simp] theorem smul_v [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).v = a • x.v := rfl

@[simp] theorem smul_s [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).s = a • x.s := rfl

@[simp] theorem smul_c [Semiring R] [AddCommGroup K] [Module R K]
    (a : R) (x : JCoord K) : (a • x).c = a • x.c := rfl

@[simp] theorem zero_d1 [AddCommGroup K] : (0 : JCoord K).d1 = 0 := rfl
@[simp] theorem zero_d2 [AddCommGroup K] : (0 : JCoord K).d2 = 0 := rfl
@[simp] theorem zero_d3 [AddCommGroup K] : (0 : JCoord K).d3 = 0 := rfl
@[simp] theorem zero_v [AddCommGroup K] : (0 : JCoord K).v = 0 := rfl
@[simp] theorem zero_s [AddCommGroup K] : (0 : JCoord K).s = 0 := rfl
@[simp] theorem zero_c [AddCommGroup K] : (0 : JCoord K).c = 0 := rfl

@[simp] theorem zero_v_r [AddCommGroup K] : (0 : VCoord K).r = 0 := rfl
@[simp] theorem zero_v_z [AddCommGroup K] : (0 : VCoord K).z = 0 := rfl
@[simp] theorem zero_v_omega [AddCommGroup K] : (0 : VCoord K).omega = 0 := rfl
@[simp] theorem zero_s_p [AddCommGroup K] : (0 : SCoord K).p = 0 := rfl
@[simp] theorem zero_s_phi [AddCommGroup K] : (0 : SCoord K).phi = 0 := rfl
@[simp] theorem zero_c_q [AddCommGroup K] : (0 : CCoord K).q = 0 := rfl
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

theorem sourceTrace_formula (x : JCoord K) :
    sourceTrace x = x.d1 + x.d2 + x.d3 := rfl

theorem sourceSpur_formula (x : JCoord K) :
    sourceSpur x =
      x.d1 * x.d2 + x.d1 * x.d3 + x.d2 * x.d3
        - nV x.v - nS x.s - nC x.c := rfl

theorem sourceNorm_formula (x : JCoord K) :
    sourceNorm x =
      x.d1 * x.d2 * x.d3
        - x.d1 * nV x.v - x.d2 * nS x.s - x.d3 * nC x.c
        + triality x.v x.s x.c := rfl

theorem nS_add (s t : SCoord K) : nS (s + t) = nS s + nS t + BS s t := by
  simp [nS, BS, evalU]
  ring

theorem nC_add (c d : CCoord K) : nC (c + d) = nC c + nC d + BC c d := by
  simp [nC, BC, evalU]
  ring

theorem nS_smul (a : K) (s : SCoord K) : nS (a • s) = a ^ 2 * nS s := by
  simp [nS, evalU]
  ring

theorem nC_smul (a : K) (c : CCoord K) : nC (a • c) = a ^ 2 * nC c := by
  simp [nC, evalU]
  ring

theorem triality_smul_all (a : K) (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    triality (a • v) (a • s) (a • c) = a ^ 3 * triality v s c := by
  rw [triality_smul_v, triality_smul_s, triality_smul_c]
  ring

theorem sourceTrace_smul (a : K) (x : JCoord K) :
    sourceTrace (a • x) = a * sourceTrace x := by
  simp [sourceTrace]
  ring

theorem sourceSpur_smul (a : K) (x : JCoord K) :
    sourceSpur (a • x) = a ^ 2 * sourceSpur x := by
  simp only [sourceSpur, smul_d1, smul_d2, smul_d3, smul_eq_mul, smul_v,
    smul_s, smul_c, nV_smul, nS_smul, nC_smul]
  ring

/-- Cubic homogeneity of the independently locked source norm.-/
theorem sourceNorm_smul (a : K) (x : JCoord K) :
    sourceNorm (a • x) = a ^ 3 * sourceNorm x := by
  simp only [sourceNorm, smul_d1, smul_d2, smul_d3, smul_eq_mul, smul_v,
    smul_s, smul_c, nV_smul, nS_smul, nC_smul, triality_smul_all]
  ring

@[simp] theorem nV_zero : nV (0 : VCoord K) = 0 := by
  simp [nV, Pf, BW]

@[simp] theorem nS_zero : nS (0 : SCoord K) = 0 := by
  simp [nS, evalU]

@[simp] theorem nC_zero : nC (0 : CCoord K) = 0 := by
  simp [nC, evalU]

@[simp] theorem BV_zero_right (v : VCoord K) : BV v 0 = 0 := by
  simp [BV, BW]

@[simp] theorem BS_zero_right (s : SCoord K) : BS s 0 = 0 := by
  simp [BS, evalU]

@[simp] theorem BC_zero_right (c : CCoord K) : BC c 0 = 0 := by
  simp [BC, evalU]

@[simp] theorem BV_zero_left (v : VCoord K) : BV 0 v = 0 := by
  rw [BV_symmetric]
  exact BV_zero_right v

@[simp] theorem BS_zero_left (s : SCoord K) : BS 0 s = 0 := by
  rw [BS_symmetric]
  exact BS_zero_right s

@[simp] theorem BC_zero_left (c : CCoord K) : BC 0 c = 0 := by
  rw [BC_symmetric]
  exact BC_zero_right c

@[simp] theorem triality_zero_v (s : SCoord K) (c : CCoord K) :
    triality (0 : VCoord K) s c = 0 := by
  simp [triality, BW, pairW]

@[simp] theorem triality_zero_s (v : VCoord K) (c : CCoord K) :
    triality v (0 : SCoord K) c = 0 := by
  simp [triality, evalU, BW, pairW, wedge2, dualWedge2]

@[simp] theorem triality_zero_c (v : VCoord K) (s : SCoord K) :
    triality v s (0 : CCoord K) = 0 := by
  simp [triality, evalU, BW, pairW, wedge2, dualWedge2]

@[simp] theorem sourceTrace_one : sourceTrace (sourceOne : JCoord K) = 3 := by
  simp [sourceTrace, sourceOne]
  ring

@[simp] theorem sourceSpur_one : sourceSpur (sourceOne : JCoord K) = 3 := by
  simp [sourceSpur, sourceOne]
  ring

@[simp] theorem sourceNorm_one : sourceNorm (sourceOne : JCoord K) = 1 := by
  simp [sourceNorm, sourceOne]

theorem source_diagonal_restrictions (d1 d2 d3 : K) :
    sourceTrace (diagonal d1 d2 d3) = d1 + d2 + d3 ∧
    sourceSpur (diagonal d1 d2 d3) = d1 * d2 + d1 * d3 + d2 * d3 ∧
    sourceNorm (diagonal d1 d2 d3) = d1 * d2 * d3 := by
  simp [sourceTrace, sourceSpur, sourceNorm, diagonal, nV, nS, nC, triality,
    Pf, evalU, BW, pairW, wedge2, dualWedge2]

theorem source_pureV_restrictions (v : VCoord K) :
    sourceTrace (pureV v) = 0 ∧ sourceSpur (pureV v) = -nV v ∧
      sourceNorm (pureV v) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureV, nS, nC, triality,
    evalU, BW, pairW, wedge2, dualWedge2]

theorem source_pureS_restrictions (s : SCoord K) :
    sourceTrace (pureS s) = 0 ∧ sourceSpur (pureS s) = -nS s ∧
      sourceNorm (pureS s) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureS, nV, nC, triality,
    Pf, evalU, BW, pairW]

theorem source_pureC_restrictions (c : CCoord K) :
    sourceTrace (pureC c) = 0 ∧ sourceSpur (pureC c) = -nC c ∧
      sourceNorm (pureC c) = 0 := by
  simp [sourceTrace, sourceSpur, sourceNorm, pureC, nV, nS, triality,
    Pf, evalU, BW, pairW]

theorem source_offDiagonal_restrictions (v : VCoord K) (s : SCoord K) (c : CCoord K) :
    sourceTrace (offDiagonal v s c) = 0 ∧
    sourceSpur (offDiagonal v s c) = -nV v - nS s - nC c ∧
    sourceNorm (offDiagonal v s c) = triality v s c := by
  simp [sourceTrace, sourceSpur, sourceNorm, offDiagonal]

/-- Explicit symmetric spur polarization, separated from cubic polarization.-/
theorem sourceSpurPolar_formula (x y : JCoord K) :
    sourceSpurPolar x y =
      x.d1 * y.d2 + y.d1 * x.d2
      + x.d1 * y.d3 + y.d1 * x.d3
      + x.d2 * y.d3 + y.d2 * x.d3
      - BV x.v y.v - BS x.s y.s - BC x.c y.c := by
  simp only [sourceSpurPolar, sourceSpur, add_d1, add_d2, add_d3, add_v, add_s,
    add_c, nV_add, nS_add, nC_add]
  ring

theorem sourceSpurPolar_symmetric (x y : JCoord K) :
    sourceSpurPolar x y = sourceSpurPolar y x := by
  rw [sourceSpurPolar_formula, sourceSpurPolar_formula, BV_symmetric, BS_symmetric,
    BC_symmetric]
  ring

theorem sourceSpurPolar_diagonal (x : JCoord K) :
    sourceSpurPolar x x = 2 * sourceSpur x := by
  rw [sourceSpurPolar_formula, BV_self_eq_two_nV, BS_self_eq_two_nS,
    BC_self_eq_two_nC]
  simp only [sourceSpur]
  ring

theorem sourceTraceForm_formula (x y : JCoord K) :
    sourceTraceForm x y =
      x.d1 * y.d1 + x.d2 * y.d2 + x.d3 * y.d3
        + BV x.v y.v + BS x.s y.s + BC x.c y.c := by
  rw [sourceTraceForm, sourceSpurPolar_formula]
  simp only [sourceTrace]
  ring

theorem sourceTraceForm_symmetric (x y : JCoord K) :
    sourceTraceForm x y = sourceTraceForm y x := by
  rw [sourceTraceForm_formula, sourceTraceForm_formula, BV_symmetric, BS_symmetric,
    BC_symmetric]
  ring

theorem sourceTraceForm_one_left (x : JCoord K) :
    sourceTraceForm (sourceOne : JCoord K) x = sourceTrace x := by
  rw [sourceTraceForm_formula]
  simp [sourceOne, sourceTrace]

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

/-- The source trace form is nondegenerate on all 27 literal coordinates.-/
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

theorem sourcePolar_swap_left (x y z : JCoord K) :
    sourcePolar x y z = sourcePolar y x z := by
  simp only [sourcePolar]
  have hxyz : y + x + z = x + y + z := by abel
  have hxy : y + x = x + y := add_comm _ _
  rw [hxyz, hxy]
  ring

theorem sourcePolar_swap_right (x y z : JCoord K) :
    sourcePolar x y z = sourcePolar x z y := by
  simp only [sourcePolar]
  have hxyz : x + z + y = x + y + z := by abel
  have hzy : z + y = y + z := add_comm _ _
  rw [hxyz, hzy]
  ring

/-- Polarizing the cubic once at the source unit recovers the spur polarization.-/
theorem sourcePolar_one (x y : JCoord K) :
    sourcePolar (sourceOne : JCoord K) x y = sourceSpurPolar x y := by
  simp only [sourcePolar, sourceSpurPolar_formula, sourceNorm, sourceOne, add_d1,
    add_d2, add_d3, add_v, add_s, add_c, nV_add, nS_add, nC_add,
    triality_add_v, triality_add_s, triality_add_c, nV_zero, nS_zero, nC_zero,
    triality_zero_c, zero_add]
  ring

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
nondegeneracy without any use of generated F0 comparison data.-/
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
