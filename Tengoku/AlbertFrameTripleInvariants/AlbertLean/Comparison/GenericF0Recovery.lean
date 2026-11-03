import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.GenericF0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms f0RecoveryDataK` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms structuredEquivK_map_sourceProduct_to_genericRecovery` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms f0RecoveredProductLinearK` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @f0RecoveryDataK` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @structuredEquivK_map_sourceProduct_to_genericRecovery` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @f0RecoveredProductLinearK` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Recovery data for the generic F0 coordinate cubic

This module packages the already accepted generic coordinate functions as
linear and multilinear maps, proves trace-form nondegeneracy through the
accepted structured-coordinate equivalence, and applies the source-independent
`RecoveryData.map_product` theorem.  It does not unfold or use the frozen F0
product tensor.

The resulting comparison is between a source-defined cubic recovery product
and a target-defined cubic recovery product.  It is not a split-Albert
classification, a Jordan-identity proof, or a physics statement.
-/

namespace AlbertLean.Comparison.GenericF0Recovery

open AlbertLean
open AlbertLean.CubicNorm
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Comparison.GenericF0

variable {K : Type*} [Field K] [CharZero K]

/-- The accepted generic coordinate trace as a linear functional.-/
def f0TraceLinearK : F0Coord K →ₗ[K] K where
  toFun := f0TraceK
  map_add' x y := by
    simp [f0TraceK]
    ring
  map_smul' a x := by
    simp [f0TraceK]
    ring

/--
@isnad1 id=eq.0h2v.s8.926b887882e8 from=translated src=- shape=c715cac7 vocab=d7b22022
-/
@[simp] theorem f0TraceLinearK_apply (x : F0Coord K) :
    f0TraceLinearK x = f0TraceK x := rfl

/--
@isnad1 id=eq.0h3v.s5.74f162b36dca from=translated src=- shape=1bf5b2d1 vocab=a92789f1
-/
theorem f0TraceFormK_symmetric (x y : F0Coord K) :
    f0TraceFormK x y = f0TraceFormK y x := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  rw [← sourceTraceForm_agrees_with_f0K,
    ← sourceTraceForm_agrees_with_f0K, sourceTraceForm_symmetric]

/--
@isnad1 id=eq.0h4v.s6.c40e0679e73f from=translated src=- shape=d5ef01f1 vocab=131fd6bf
-/
theorem f0TraceFormK_add_right (x y z : F0Coord K) :
    f0TraceFormK x (y + z) = f0TraceFormK x y + f0TraceFormK x z := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  obtain ⟨sz, rfl⟩ := (structuredEquivK K).surjective z
  rw [← (structuredEquivK K).map_add sy sz]
  rw [← sourceTraceForm_agrees_with_f0K,
    ← sourceTraceForm_agrees_with_f0K,
    ← sourceTraceForm_agrees_with_f0K]
  exact (sourceTraceFormLinear (K := K) sx).map_add sy sz

/--
@isnad1 id=eq.0h4v.s6.af4753c6e3d4 from=translated src=- shape=eca8c0db vocab=26810123
-/
theorem f0TraceFormK_smul_right (a : K) (x y : F0Coord K) :
    f0TraceFormK x (a • y) = a * f0TraceFormK x y := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  rw [← (structuredEquivK K).map_smul a sy]
  rw [← sourceTraceForm_agrees_with_f0K,
    ← sourceTraceForm_agrees_with_f0K]
  have hlin := (sourceTraceFormLinear (K := K) sx).map_smul a sy
  change sourceTraceForm sx (a • sy) = a • sourceTraceForm sx sy at hlin
  simpa only [smul_eq_mul] using hlin

/--
@isnad1 id=eq.0h4v.s6.db8b9dfe8be7 from=translated src=- shape=832dc70b vocab=131fd6bf
-/
theorem f0TraceFormK_add_left (x y z : F0Coord K) :
    f0TraceFormK (x + y) z = f0TraceFormK x z + f0TraceFormK y z := by
  rw [f0TraceFormK_symmetric, f0TraceFormK_add_right,
    f0TraceFormK_symmetric z x, f0TraceFormK_symmetric z y]

/--
@isnad1 id=eq.0h4v.s6.5c923a251086 from=translated src=- shape=bfb42e0a vocab=26810123
-/
theorem f0TraceFormK_smul_left (a : K) (x y : F0Coord K) :
    f0TraceFormK (a • x) y = a * f0TraceFormK x y := by
  rw [f0TraceFormK_symmetric, f0TraceFormK_smul_right,
    f0TraceFormK_symmetric y x]

/-- The accepted generic trace form as a curried bilinear map.-/
def f0TraceFormLinearK : F0Coord K →ₗ[K] F0Coord K →ₗ[K] K where
  toFun x :=
    { toFun := f0TraceFormK x
      map_add' := f0TraceFormK_add_right x
      map_smul' := by
        intro a y
        simpa [smul_eq_mul] using f0TraceFormK_smul_right a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact f0TraceFormK_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    simpa [smul_eq_mul] using f0TraceFormK_smul_left a x y

/--
@isnad1 id=eq.0h3v.s10.120a5a7dd8a0 from=translated src=- shape=ad41807b vocab=b806a45e
-/
@[simp] theorem f0TraceFormLinearK_apply (x y : F0Coord K) :
    f0TraceFormLinearK x y = f0TraceFormK x y := rfl

/--
@isnad1 id=eq.0h5v.s6.dc6fdfdaeb98 from=translated src=- shape=399861e9 vocab=2eec5b0c
-/
theorem f0PolarK_add_right (x y z w : F0Coord K) :
    f0PolarK x y (z + w) = f0PolarK x y z + f0PolarK x y w := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  obtain ⟨sz, rfl⟩ := (structuredEquivK K).surjective z
  obtain ⟨sw, rfl⟩ := (structuredEquivK K).surjective w
  rw [← (structuredEquivK K).map_add sz sw]
  rw [← sourcePolar_agrees_with_f0K,
    ← sourcePolar_agrees_with_f0K,
    ← sourcePolar_agrees_with_f0K]
  simpa only [sourcePolarLinear_apply] using
    (sourcePolarLinear (K := K) sx sy).map_add sz sw

/--
@isnad1 id=eq.0h5v.s6.3eb7cb40b9ce from=translated src=- shape=51f99fdd vocab=3ff45434
-/
theorem f0PolarK_smul_right (a : K) (x y z : F0Coord K) :
    f0PolarK x y (a • z) = a * f0PolarK x y z := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  obtain ⟨sz, rfl⟩ := (structuredEquivK K).surjective z
  rw [← (structuredEquivK K).map_smul a sz]
  rw [← sourcePolar_agrees_with_f0K,
    ← sourcePolar_agrees_with_f0K]
  simpa only [sourcePolarLinear_apply, smul_eq_mul] using
    (sourcePolarLinear (K := K) sx sy).map_smul a sz

/--
@isnad1 id=eq.0h4v.s5.28b3c1e8cdec from=translated src=- shape=8cb4d701 vocab=06341fdf
-/
theorem f0PolarK_swap_left (x y z : F0Coord K) :
    f0PolarK x y z = f0PolarK y x z := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  obtain ⟨sz, rfl⟩ := (structuredEquivK K).surjective z
  rw [← sourcePolar_agrees_with_f0K,
    ← sourcePolar_agrees_with_f0K, sourcePolar_swap_left]

/--
@isnad1 id=eq.0h4v.s5.cd88ee1a2933 from=translated src=- shape=f46dec1a vocab=06341fdf
-/
theorem f0PolarK_swap_right (x y z : F0Coord K) :
    f0PolarK x y z = f0PolarK x z y := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  obtain ⟨sy, rfl⟩ := (structuredEquivK K).surjective y
  obtain ⟨sz, rfl⟩ := (structuredEquivK K).surjective z
  rw [← sourcePolar_agrees_with_f0K,
    ← sourcePolar_agrees_with_f0K, sourcePolar_swap_right]

/--
@isnad1 id=eq.0h5v.s6.fed7e5aee94d from=translated src=- shape=25696a0d vocab=2eec5b0c
-/
theorem f0PolarK_add_middle (x y z w : F0Coord K) :
    f0PolarK x (y + z) w = f0PolarK x y w + f0PolarK x z w := by
  rw [f0PolarK_swap_right x (y + z) w, f0PolarK_add_right,
    f0PolarK_swap_right x w y, f0PolarK_swap_right x w z]

/--
@isnad1 id=eq.0h5v.s6.cc63b57fa126 from=translated src=- shape=1fc95748 vocab=3ff45434
-/
theorem f0PolarK_smul_middle (a : K) (x y z : F0Coord K) :
    f0PolarK x (a • y) z = a * f0PolarK x y z := by
  rw [f0PolarK_swap_right x (a • y) z, f0PolarK_smul_right,
    f0PolarK_swap_right x z y]

/--
@isnad1 id=eq.0h5v.s6.d3567baf99a8 from=translated src=- shape=71b31773 vocab=2eec5b0c
-/
theorem f0PolarK_add_left (x y z w : F0Coord K) :
    f0PolarK (x + y) z w = f0PolarK x z w + f0PolarK y z w := by
  rw [f0PolarK_swap_left (x + y) z w, f0PolarK_add_middle,
    f0PolarK_swap_left z x w, f0PolarK_swap_left z y w]

/--
@isnad1 id=eq.0h5v.s6.0e186effef30 from=translated src=- shape=c37b43f3 vocab=3ff45434
-/
theorem f0PolarK_smul_left (a : K) (x y z : F0Coord K) :
    f0PolarK (a • x) y z = a * f0PolarK x y z := by
  rw [f0PolarK_swap_left (a • x) y z, f0PolarK_smul_middle,
    f0PolarK_swap_left y x z]

/-- The accepted generic polarization as a curried trilinear map.-/
def f0PolarLinearK :
    F0Coord K →ₗ[K] F0Coord K →ₗ[K] F0Coord K →ₗ[K] K where
  toFun x :=
    { toFun := fun y ↦
        { toFun := f0PolarK x y
          map_add' := f0PolarK_add_right x y
          map_smul' := by
            intro a z
            simpa [smul_eq_mul] using f0PolarK_smul_right a x y z }
      map_add' := by
        intro y z
        apply LinearMap.ext
        intro w
        exact f0PolarK_add_middle x y z w
      map_smul' := by
        intro a y
        apply LinearMap.ext
        intro z
        simpa [smul_eq_mul] using f0PolarK_smul_middle a x y z }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    exact f0PolarK_add_left x y z w
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simpa [smul_eq_mul] using f0PolarK_smul_left a x y z

/--
@isnad1 id=eq.0h4v.s12.618ed933d260 from=translated src=- shape=0f1106b0 vocab=93ab482f
-/
@[simp] theorem f0PolarLinearK_apply (x y z : F0Coord K) :
    f0PolarLinearK x y z = f0PolarK x y z := rfl

/-- Nondegeneracy of the generic coordinate trace form.
@isnad1 id=eq.1h2v.s6.3f1f35b75101 from=translated src=- shape=59d462ba vocab=6ad0c8a4
-/
theorem f0TraceFormK_nondegenerate {x : F0Coord K}
    (h : ∀ y : F0Coord K, f0TraceFormK x y = 0) : x = 0 := by
  obtain ⟨sx, rfl⟩ := (structuredEquivK K).surjective x
  have hs : ∀ sy : JCoord K, sourceTraceForm sx sy = 0 := by
    intro sy
    rw [sourceTraceForm_agrees_with_f0K]
    exact h (structuredEquivK K sy)
  have hx : sx = 0 := sourceTraceForm_nondegenerate hs
  rw [hx, map_zero]

/-- Recovery data made from the literal accepted generic F0 cubic functions.-/
noncomputable def f0RecoveryDataK : RecoveryData K (F0Coord K) where
  traceForm := f0TraceFormLinearK
  polar := f0PolarLinearK
  trace := f0TraceLinearK
  one := f0OneK
  traceForm_nondegenerate := by
    intro x h
    exact f0TraceFormK_nondegenerate (fun y ↦ h y)

/--
Compact source-to-target recovery bridge.  The tensor product is deliberately
absent; comparison with the explicit tensor is a separate statement.
@isnad1 id=eq.0h3v.s10.8adcd8636e40 from=translated src=- shape=43f35cb9 vocab=fb5c2c0e
-/
theorem structuredEquivK_map_sourceProduct_to_genericRecovery
    (x y : JCoord K) :
    structuredEquivK K (sourceProduct x y) =
      (f0RecoveryDataK (K := K)).product
        (structuredEquivK K x) (structuredEquivK K y) := by
  change structuredEquivK K ((sourceRecoveryData (K := K)).product x y) = _
  apply (sourceRecoveryData (K := K)).map_product
    (f0RecoveryDataK (K := K)) (structuredEquivK K)
  · simpa [sourceRecoveryData, f0RecoveryDataK] using
      (structuredEquivK_sourceOne (K := K))
  · intro z
    simpa [sourceRecoveryData, f0RecoveryDataK] using
      (sourceTrace_agrees_with_f0K z).symm
  · intro z w
    simpa [sourceRecoveryData, f0RecoveryDataK] using
      (sourceTraceForm_agrees_with_f0K z w).symm
  · intro z w u
    simpa [sourceRecoveryData, f0RecoveryDataK] using
      (sourcePolar_agrees_with_f0K z w u).symm

/-- The recovered target product packaged as a curried linear map.-/
noncomputable def f0RecoveredProductLinearK :
    F0Coord K →ₗ[K] F0Coord K →ₗ[K] F0Coord K where
  toFun x :=
    { toFun := (f0RecoveryDataK (K := K)).product x
      map_add' := (f0RecoveryDataK (K := K)).product_add_right
        f0TraceFormK_symmetric x
      map_smul' := by
        intro a y
        exact (f0RecoveryDataK (K := K)).product_smul_right
          f0TraceFormK_symmetric a x y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    exact (f0RecoveryDataK (K := K)).product_add_left x y z
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    exact (f0RecoveryDataK (K := K)).product_smul_left a x y

/--
@isnad1 id=eq.0h3v.s10.679d3f54c08a from=translated src=- shape=e2059839 vocab=35e46da3
-/
@[simp] theorem f0RecoveredProductLinearK_apply (x y : F0Coord K) :
    f0RecoveredProductLinearK x y = (f0RecoveryDataK (K := K)).product x y := rfl

/-- The source cross rewritten through the accepted explicit adjoint formula.
@isnad1 id=eq.0h3v.s7.78555da60924 from=translated src=- shape=0c1d779f vocab=8e62c1e1
-/
theorem sourceCross_eq_explicitPolarizationK (x y : JCoord K) :
    sourceCross x y =
      sourceExplicitAdjoint (x + y) - sourceExplicitAdjoint x -
        sourceExplicitAdjoint y := by
  change sourceAdjoint (x + y) - sourceAdjoint x - sourceAdjoint y = _
  rw [sourceAdjoint_eq_explicit, sourceAdjoint_eq_explicit,
    sourceAdjoint_eq_explicit]

end AlbertLean.Comparison.GenericF0Recovery
