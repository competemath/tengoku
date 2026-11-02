import Tengoku.AlbertFrameTripleInvariants.AlbertLean.CubicNorm.ProductRecovery
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Triality.StructuredCubic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourcePolar_eq_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceExplicitAdjoint_characterization` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAdjoint_eq_explicit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sourceAdjoint_one` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Trace-dual adjoint of the structured source cubic

The product data in this file is reconstructed only from the locked source
trace, trace form, and finite-difference cubic polarization.  The explicit
coordinate adjoint is proved to satisfy the same universal characterization;
the external JSON was used only as an implementation and mutation oracle.
-/

namespace AlbertLean.Triality.StructuredAdjoint

open AlbertLean.CubicNorm
open ExteriorSix CoordinateTensor StructuredCubic

variable {K : Type*} [Field K] [CharZero K]

theorem BV_add_left (u v w : VCoord K) : BV (u + v) w = BV u w + BV v w := by
  simp [BV, BW]
  ring

theorem BV_add_right (u v w : VCoord K) : BV u (v + w) = BV u v + BV u w := by
  rw [BV_symmetric, BV_add_left, BV_symmetric v, BV_symmetric w]

theorem BV_smul_left (a : K) (v w : VCoord K) : BV (a • v) w = a * BV v w := by
  simp [BV, BW]
  ring

theorem BV_smul_right (a : K) (v w : VCoord K) : BV v (a • w) = a * BV v w := by
  rw [BV_symmetric, BV_smul_left, BV_symmetric]

theorem BS_add_left (r s t : SCoord K) : BS (r + s) t = BS r t + BS s t := by
  simp [BS, evalU]
  ring

theorem BS_add_right (r s t : SCoord K) : BS r (s + t) = BS r s + BS r t := by
  rw [BS_symmetric, BS_add_left, BS_symmetric s, BS_symmetric t]

theorem BS_smul_left (a : K) (s t : SCoord K) : BS (a • s) t = a * BS s t := by
  simp [BS, evalU]
  ring

theorem BS_smul_right (a : K) (s t : SCoord K) : BS s (a • t) = a * BS s t := by
  rw [BS_symmetric, BS_smul_left, BS_symmetric]

theorem BC_add_left (b c d : CCoord K) : BC (b + c) d = BC b d + BC c d := by
  simp [BC, evalU]
  ring

theorem BC_add_right (b c d : CCoord K) : BC b (c + d) = BC b c + BC b d := by
  rw [BC_symmetric, BC_add_left, BC_symmetric c, BC_symmetric d]

theorem BC_smul_left (a : K) (c d : CCoord K) : BC (a • c) d = a * BC c d := by
  simp [BC, evalU]
  ring

theorem BC_smul_right (a : K) (c d : CCoord K) : BC c (a • d) = a * BC c d := by
  rw [BC_symmetric, BC_smul_left, BC_symmetric]

/-- The direct symmetric trilinear expansion of the locked source cubic.-/
def sourcePolarFormula (x y z : JCoord K) : K :=
  x.d1 * y.d2 * z.d3 + x.d1 * z.d2 * y.d3
    + y.d1 * x.d2 * z.d3 + y.d1 * z.d2 * x.d3
    + z.d1 * x.d2 * y.d3 + z.d1 * y.d2 * x.d3
    - (x.d1 * BV y.v z.v + y.d1 * BV x.v z.v + z.d1 * BV x.v y.v)
    - (x.d2 * BS y.s z.s + y.d2 * BS x.s z.s + z.d2 * BS x.s y.s)
    - (x.d3 * BC y.c z.c + y.d3 * BC x.c z.c + z.d3 * BC x.c y.c)
    + triality x.v y.s z.c + triality x.v z.s y.c
    + triality y.v x.s z.c + triality y.v z.s x.c
    + triality z.v x.s y.c + triality z.v y.s x.c

/-- The direct trilinear expansion equals finite-difference polarization.-/
theorem sourcePolar_eq_formula (x y z : JCoord K) :
    sourcePolar x y z = sourcePolarFormula x y z := by
  simp only [sourcePolar, sourceNorm, sourcePolarFormula, add_d1, add_d2, add_d3,
    add_v, add_s, add_c, nV_add, nS_add, nC_add, triality_add_v,
    triality_add_s, triality_add_c, BV_add_left, BV_add_right, BS_add_left,
    BS_add_right, BC_add_left, BC_add_right]
  ring

/-- The locked trace form as a curried linear map.-/
def sourceTraceFormLinear : JCoord K →ₗ[K] JCoord K →ₗ[K] K where
  toFun x :=
    { toFun := fun y => sourceTraceForm x y
      map_add' := by
        intro y z
        rw [sourceTraceForm_formula, sourceTraceForm_formula,
          sourceTraceForm_formula]
        simp [BV_add_right, BS_add_right, BC_add_right]
        ring
      map_smul' := by
        intro a y
        rw [sourceTraceForm_formula, sourceTraceForm_formula]
        simp [BV_smul_right, BS_smul_right, BC_smul_right]
        ring }
  map_add' := by
    intro x y
    ext z
    change sourceTraceForm (x + y) z = sourceTraceForm x z + sourceTraceForm y z
    rw [sourceTraceForm_formula, sourceTraceForm_formula,
      sourceTraceForm_formula]
    simp [BV_add_left, BS_add_left, BC_add_left]
    ring
  map_smul' := by
    intro a x
    ext y
    change sourceTraceForm (a • x) y = a • sourceTraceForm x y
    rw [sourceTraceForm_formula, sourceTraceForm_formula]
    simp [BV_smul_left, BS_smul_left, BC_smul_left]
    ring

@[simp] theorem sourceTraceFormLinear_apply (x y : JCoord K) :
    sourceTraceFormLinear x y = sourceTraceForm x y := rfl

/-- The locked trace as a linear functional.-/
def sourceTraceLinear : JCoord K →ₗ[K] K where
  toFun := sourceTrace
  map_add' := by
    intro x y
    simp [sourceTrace]
    ring
  map_smul' := by
    intro a x
    simp [sourceTrace]
    ring

@[simp] theorem sourceTraceLinear_apply (x : JCoord K) :
    sourceTraceLinear x = sourceTrace x := rfl

/-- The source polarization packaged as a trilinear map.-/
def sourcePolarLinear : JCoord K →ₗ[K] JCoord K →ₗ[K] JCoord K →ₗ[K] K where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => sourcePolarFormula x y z
          map_add' := by
            intro z w
            simp [sourcePolarFormula, BV_add_right, BS_add_right, BC_add_right,
              triality_add_v, triality_add_s, triality_add_c]
            ring
          map_smul' := by
            intro a z
            simp [sourcePolarFormula, BV_smul_right, BS_smul_right, BC_smul_right,
              triality_smul_v, triality_smul_s, triality_smul_c]
            ring }
      map_add' := by
        intro y z
        ext w
        simp [sourcePolarFormula, BV_add_left, BV_add_right, BS_add_left,
          BS_add_right, BC_add_left, BC_add_right, triality_add_v,
          triality_add_s, triality_add_c]
        ring
      map_smul' := by
        intro a y
        ext z
        simp [sourcePolarFormula, BV_smul_left, BV_smul_right, BS_smul_left,
          BS_smul_right, BC_smul_left, BC_smul_right, triality_smul_v,
          triality_smul_s, triality_smul_c]
        ring }
  map_add' := by
    intro x y
    ext z w
    simp [sourcePolarFormula, BV_add_left, BV_add_right, BS_add_left,
      BS_add_right, BC_add_left, BC_add_right, triality_add_v,
      triality_add_s, triality_add_c]
    ring
  map_smul' := by
    intro a x
    ext y z
    simp [sourcePolarFormula, BV_smul_left, BV_smul_right, BS_smul_left,
      BS_smul_right, BC_smul_left, BC_smul_right, triality_smul_v,
      triality_smul_s, triality_smul_c]
    ring

@[simp] theorem sourcePolarLinear_apply (x y z : JCoord K) :
    sourcePolarLinear x y z = sourcePolar x y z := by
  exact (sourcePolar_eq_formula x y z).symm

private def vCoordEmbedding : VCoord K →ₗ[K] K × K × W K where
  toFun v := (v.r, v.z, v.omega)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

private theorem vCoordEmbedding_injective :
    Function.Injective (vCoordEmbedding (K := K)) := by
  intro x y h
  exact VCoord.ext (congrArg Prod.fst h)
    (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)

noncomputable instance vCoordFiniteDimensional : FiniteDimensional K (VCoord K) :=
  FiniteDimensional.of_injective vCoordEmbedding vCoordEmbedding_injective

private def sCoordEmbedding : SCoord K →ₗ[K] U K × Udual K where
  toFun s := (s.p, s.phi)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

private theorem sCoordEmbedding_injective :
    Function.Injective (sCoordEmbedding (K := K)) := by
  intro x y h
  exact SCoord.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance sCoordFiniteDimensional : FiniteDimensional K (SCoord K) :=
  FiniteDimensional.of_injective sCoordEmbedding sCoordEmbedding_injective

private def cCoordEmbedding : CCoord K →ₗ[K] U K × Udual K where
  toFun c := (c.q, c.psi)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

private theorem cCoordEmbedding_injective :
    Function.Injective (cCoordEmbedding (K := K)) := by
  intro x y h
  exact CCoord.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable instance cCoordFiniteDimensional : FiniteDimensional K (CCoord K) :=
  FiniteDimensional.of_injective cCoordEmbedding cCoordEmbedding_injective

private def jCoordEmbedding :
    JCoord K →ₗ[K] K × K × K × VCoord K × SCoord K × CCoord K where
  toFun x := (x.d1, x.d2, x.d3, x.v, x.s, x.c)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

private theorem jCoordEmbedding_injective :
    Function.Injective (jCoordEmbedding (K := K)) := by
  intro x y h
  exact JCoord.ext (congrArg Prod.fst h)
    (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2.1) h)
    (congrArg (fun z => z.2.2.2.1) h) (congrArg (fun z => z.2.2.2.2.1) h)
    (congrArg (fun z => z.2.2.2.2.2) h)

noncomputable instance jCoordFiniteDimensional : FiniteDimensional K (JCoord K) :=
  FiniteDimensional.of_injective jCoordEmbedding jCoordEmbedding_injective

/-- Cubic-recovery data built solely from source-locked definitions.-/
noncomputable def sourceRecoveryData : RecoveryData K (JCoord K) where
  traceForm := sourceTraceFormLinear
  polar := sourcePolarLinear
  trace := sourceTraceLinear
  one := sourceOne
  traceForm_nondegenerate := by
    intro x h
    exact sourceTraceForm_nondegenerate (fun y => h y)

/-- The independently expanded `S` component of the source adjoint.-/
def sourceMuS (c : CCoord K) (v : VCoord K) : SCoord K :=
  { p := ![
      c.psi 1 * v.omega .i12 + c.psi 2 * v.omega .i13 + c.psi 3 * v.omega .i14 + c.q 0 * v.r,
      -c.psi 0 * v.omega .i12 + c.psi 2 * v.omega .i23 + c.psi 3 * v.omega .i24 + c.q 1 * v.r,
      -c.psi 0 * v.omega .i13 - c.psi 1 * v.omega .i23 + c.psi 3 * v.omega .i34 + c.q 2 * v.r,
      -c.psi 0 * v.omega .i14 - c.psi 1 * v.omega .i24 - c.psi 2 * v.omega .i34 + c.q 3 * v.r]
    phi := ![
      c.psi 0 * v.z + c.q 1 * v.omega .i34 - c.q 2 * v.omega .i24 + c.q 3 * v.omega .i23,
      c.psi 1 * v.z - c.q 0 * v.omega .i34 + c.q 2 * v.omega .i14 - c.q 3 * v.omega .i13,
      c.psi 2 * v.z + c.q 0 * v.omega .i24 - c.q 1 * v.omega .i14 + c.q 3 * v.omega .i12,
      c.psi 3 * v.z - c.q 0 * v.omega .i23 + c.q 1 * v.omega .i13 - c.q 2 * v.omega .i12] }

/-- The independently expanded `C` component of the source adjoint.-/
def sourceMuC (v : VCoord K) (s : SCoord K) : CCoord K :=
  { q := ![
      s.p 0 * v.z - s.phi 1 * v.omega .i12 - s.phi 2 * v.omega .i13 - s.phi 3 * v.omega .i14,
      s.p 1 * v.z + s.phi 0 * v.omega .i12 - s.phi 2 * v.omega .i23 - s.phi 3 * v.omega .i24,
      s.p 2 * v.z + s.phi 0 * v.omega .i13 + s.phi 1 * v.omega .i23 - s.phi 3 * v.omega .i34,
      s.p 3 * v.z + s.phi 0 * v.omega .i14 + s.phi 1 * v.omega .i24 + s.phi 2 * v.omega .i34]
    psi := ![
      -s.p 1 * v.omega .i34 + s.p 2 * v.omega .i24 - s.p 3 * v.omega .i23 + s.phi 0 * v.r,
      s.p 0 * v.omega .i34 - s.p 2 * v.omega .i14 + s.p 3 * v.omega .i13 + s.phi 1 * v.r,
      -s.p 0 * v.omega .i24 + s.p 1 * v.omega .i14 - s.p 3 * v.omega .i12 + s.phi 2 * v.r,
      s.p 0 * v.omega .i23 - s.p 1 * v.omega .i13 + s.p 2 * v.omega .i12 + s.phi 3 * v.r] }

/-- The complete explicit 27-coordinate source adjoint.-/
def sourceExplicitAdjoint (x : JCoord K) : JCoord K :=
  { d1 := x.d2 * x.d3 - nV x.v
    d2 := x.d1 * x.d3 - nS x.s
    d3 := x.d1 * x.d2 - nC x.c
    v := normalizedMuV x.s x.c - x.d1 • x.v
    s := sourceMuS x.c x.v - x.d2 • x.s
    c := sourceMuC x.v x.s - x.d3 • x.c }

@[simp] theorem sub_v_r (v w : VCoord K) : (v - w).r = v.r - w.r := rfl
@[simp] theorem sub_v_z (v w : VCoord K) : (v - w).z = v.z - w.z := rfl
@[simp] theorem sub_v_omega (v w : VCoord K) : (v - w).omega = v.omega - w.omega := rfl
@[simp] theorem sub_s_p (s t : SCoord K) : (s - t).p = s.p - t.p := rfl
@[simp] theorem sub_s_phi (s t : SCoord K) : (s - t).phi = s.phi - t.phi := rfl
@[simp] theorem sub_c_q (c d : CCoord K) : (c - d).q = c.q - d.q := rfl
@[simp] theorem sub_c_psi (c d : CCoord K) : (c - d).psi = c.psi - d.psi := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Universal coordinate verification of the independently regenerated adjoint.-/
theorem sourceExplicitAdjoint_characterization (x y : JCoord K) :
    sourceTraceForm (sourceExplicitAdjoint x) y = sourcePolar x x y / 2 := by
  rw [sourceTraceForm_formula, sourcePolar_eq_formula]
  simp [sourceExplicitAdjoint, sourceMuS, sourceMuC, sourcePolarFormula,
    normalizedMuV, muV, nV, nS, nC, pf_coordinate, BV, BS, BC, triality,
    evalU, BW, pairW, wedge2, dualWedge2, hodgeStar]
  field_simp
  ring

/-- The canonical source adjoint, defined abstractly by trace duality.-/
noncomputable def sourceAdjoint (x : JCoord K) : JCoord K :=
  (sourceRecoveryData (K := K)).adjoint x

theorem sourceAdjoint_characterization (x y : JCoord K) :
    sourceTraceForm (sourceAdjoint x) y = sourcePolar x x y / 2 := by
  simpa [sourceAdjoint, sourceRecoveryData] using
    (sourceRecoveryData (K := K)).adjoint_characterization x y

/-- The abstract trace-dual adjoint equals the explicit 27-coordinate formula.-/
theorem sourceAdjoint_eq_explicit (x : JCoord K) :
    sourceAdjoint x = sourceExplicitAdjoint x := by
  apply sub_eq_zero.mp
  apply sourceTraceForm_nondegenerate
  intro y
  change sourceTraceFormLinear (sourceAdjoint x - sourceExplicitAdjoint x) y = 0
  simp only [map_sub, LinearMap.sub_apply]
  change sourceTraceForm (sourceAdjoint x) y -
      sourceTraceForm (sourceExplicitAdjoint x) y = 0
  rw [sourceAdjoint_characterization, sourceExplicitAdjoint_characterization]
  ring

@[simp] theorem sourceAdjoint_one :
    sourceAdjoint (sourceOne : JCoord K) = sourceOne := by
  rw [sourceAdjoint_eq_explicit]
  ext <;>
    simp [sourceExplicitAdjoint, sourceOne, sourceMuS, sourceMuC,
      normalizedMuV, muV, nV, nS, nC, Pf, evalU, BW, pairW, wedge2,
      dualWedge2, hodgeStar]
  all_goals
    rename_i i
    fin_cases i <;> simp

end AlbertLean.Triality.StructuredAdjoint
