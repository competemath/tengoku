import Tengoku.RainichKaluzaReconstruction.RainichKaluza.PolynomialProjector
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full simple-spectrum polynomial projectors

For four pairwise distinct roots, the Lagrange polynomial

`P_a = ((a-b)(a-c)(a-d))⁻¹ (R-bI)(R-cI)(R-dI)`

defines the projector onto the `a` eigenspace without choosing eigenvectors.
The pointwise action, resolution of the identity, and idempotence are proved
under an explicit four-eigenspace decomposition hypothesis.  This is the
finite-dimensional algebraic input needed before smooth projector fields and
their covariant derivatives can be reconstructed from the Ricci operator.
-/

namespace RainichKaluza

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The linear factor `R-rI` used in Lagrange spectral projectors.-/
def eigenFactor (R : Module.End ℝ E) (r : ℝ) : Module.End ℝ E :=
  R - r • 1

/-- The eigenvector-free Lagrange projector associated with the first of four
roots.-/
noncomputable def fourRootProjector
    (R : Module.End ℝ E) (a b c d : ℝ) : Module.End ℝ E :=
  (((a - b) * (a - c) * (a - d))⁻¹) •
    ((eigenFactor R b * eigenFactor R c) * eigenFactor R d)

@[simp]
theorem eigenFactor_apply_of_eigenvector
    (R : Module.End ℝ E) (r a : ℝ) (y : E) (hy : R y = a • y) :
    eigenFactor R r y = (a - r) • y := by
  simp only [eigenFactor, LinearMap.sub_apply, LinearMap.smul_apply, hy]
  module

/-- Evaluation of the four-root Lagrange polynomial on any eigenvector.-/
theorem fourRootProjector_apply_of_eigenvector
    (R : Module.End ℝ E) (a b c d r : ℝ) (y : E)
    (hy : R y = r • y) :
    fourRootProjector R a b c d y =
      (((a - b) * (a - c) * (a - d))⁻¹ *
        ((r - b) * (r - c) * (r - d))) • y := by
  unfold fourRootProjector
  change (((a - b) * (a - c) * (a - d))⁻¹) •
      eigenFactor R b (eigenFactor R c (eigenFactor R d y)) = _
  rw [eigenFactor_apply_of_eigenvector R d r y hy]
  rw [map_smul, eigenFactor_apply_of_eigenvector R c r y hy]
  rw [map_smul, map_smul, eigenFactor_apply_of_eigenvector R b r y hy]
  simp only [smul_smul]
  congr 1
  ring

/-- The four-root projector is the identity on its target eigenspace.-/
theorem fourRootProjector_apply_eq_self
    (R : Module.End ℝ E) (a b c d : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (y : E) (hy : R y = a • y) :
    fourRootProjector R a b c d y = y := by
  have hden : (a - b) * (a - c) * (a - d) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hac))
      (sub_ne_zero.mpr had)
  rw [fourRootProjector_apply_of_eigenvector R a b c d a y hy]
  rw [inv_mul_cancel₀ hden]
  simp

/-- The four-root projector vanishes on its first complementary eigenspace.-/
theorem fourRootProjector_apply_eq_zero_of_second
    (R : Module.End ℝ E) (a b c d : ℝ) (y : E)
    (hy : R y = b • y) :
    fourRootProjector R a b c d y = 0 := by
  rw [fourRootProjector_apply_of_eigenvector R a b c d b y hy]
  simp

/-- The four-root projector vanishes on its second complementary eigenspace.-/
theorem fourRootProjector_apply_eq_zero_of_third
    (R : Module.End ℝ E) (a b c d : ℝ) (y : E)
    (hy : R y = c • y) :
    fourRootProjector R a b c d y = 0 := by
  rw [fourRootProjector_apply_of_eigenvector R a b c d c y hy]
  simp

/-- The four-root projector vanishes on its third complementary eigenspace.-/
theorem fourRootProjector_apply_eq_zero_of_fourth
    (R : Module.End ℝ E) (a b c d : ℝ) (y : E)
    (hy : R y = d • y) :
    fourRootProjector R a b c d y = 0 := by
  rw [fourRootProjector_apply_of_eigenvector R a b c d d y hy]
  simp

/-- Every polynomial Lagrange projector commutes with the operator from which
it is constructed.-/
theorem fourRootProjector_commutes
    (R : Module.End ℝ E) (a b c d : ℝ) :
    fourRootProjector R a b c d * R =
      R * fourRootProjector R a b c d := by
  have hb : eigenFactor R b * R = R * eigenFactor R b := by
    simpa [eigenFactor, twoRootProjectorNumerator] using
      twoRootProjectorNumerator_commutes R b
  have hc : eigenFactor R c * R = R * eigenFactor R c := by
    simpa [eigenFactor, twoRootProjectorNumerator] using
      twoRootProjectorNumerator_commutes R c
  have hd : eigenFactor R d * R = R * eigenFactor R d := by
    simpa [eigenFactor, twoRootProjectorNumerator] using
      twoRootProjectorNumerator_commutes R d
  unfold fourRootProjector
  rw [smul_mul_assoc, mul_smul_comm]
  congr 1
  calc
    ((eigenFactor R b * eigenFactor R c) * eigenFactor R d) * R =
        (eigenFactor R b * eigenFactor R c) * (eigenFactor R d * R) := by
          rw [mul_assoc]
    _ = (eigenFactor R b * eigenFactor R c) * (R * eigenFactor R d) := by
          rw [hd]
    _ = (eigenFactor R b * (eigenFactor R c * R)) * eigenFactor R d := by
          simp only [mul_assoc]
    _ = (eigenFactor R b * (R * eigenFactor R c)) * eigenFactor R d := by
          rw [hc]
    _ = (eigenFactor R b * R) * (eigenFactor R c * eigenFactor R d) := by
          simp only [mul_assoc]
    _ = (R * eigenFactor R b) * (eigenFactor R c * eigenFactor R d) := by
          rw [hb]
    _ = R * ((eigenFactor R b * eigenFactor R c) * eigenFactor R d) := by
          simp only [mul_assoc]

/-- Explicit hypothesis that the module is the sum of the four specified
eigenspaces.  No basis or orientation of any eigenspace is selected.-/
def HasFourEigenspaceDecomposition
    (R : Module.End ℝ E) (a b c d : ℝ) : Prop :=
  ∀ y : E, ∃ ya yb yc yd : E,
    y = ya + yb + yc + yd ∧
    R ya = a • ya ∧ R yb = b • yb ∧
    R yc = c • yc ∧ R yd = d • yd

/-- Under a four-eigenspace decomposition, the Lagrange projector extracts
exactly its target component.-/
theorem fourRootProjector_apply_eq_component
    (R : Module.End ℝ E) (a b c d : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (y ya yb yc yd : E)
    (hy : y = ya + yb + yc + yd)
    (hya : R ya = a • ya) (hyb : R yb = b • yb)
    (hyc : R yc = c • yc) (hyd : R yd = d • yd) :
    fourRootProjector R a b c d y = ya := by
  rw [hy]
  simp only [map_add]
  rw [fourRootProjector_apply_eq_self R a b c d hab hac had ya hya]
  rw [fourRootProjector_apply_eq_zero_of_second R a b c d yb hyb]
  rw [fourRootProjector_apply_eq_zero_of_third R a b c d yc hyc]
  rw [fourRootProjector_apply_eq_zero_of_fourth R a b c d yd hyd]
  simp

/-- With distinct target and complementary roots, the full Lagrange projector
is idempotent whenever the stated four-eigenspace decomposition exists.-/
theorem fourRootProjector_sq
    (R : Module.End ℝ E) (a b c d : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hdecomp : HasFourEigenspaceDecomposition R a b c d) :
    fourRootProjector R a b c d * fourRootProjector R a b c d =
      fourRootProjector R a b c d := by
  ext y
  obtain ⟨ya, yb, yc, yd, hy, hya, hyb, hyc, hyd⟩ := hdecomp y
  have hPy : fourRootProjector R a b c d y = ya :=
    fourRootProjector_apply_eq_component R a b c d hab hac had
      y ya yb yc yd hy hya hyb hyc hyd
  change fourRootProjector R a b c d (fourRootProjector R a b c d y) =
    fourRootProjector R a b c d y
  rw [hPy]
  exact fourRootProjector_apply_eq_self R a b c d hab hac had ya hya

/-- Pairwise distinct roots give a basis-free resolution of the identity by
the four Lagrange projectors.-/
theorem fourRootProjectors_sum_eq_one
    (R : Module.End ℝ E) (a b c d : ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hdecomp : HasFourEigenspaceDecomposition R a b c d) :
    fourRootProjector R a b c d +
      fourRootProjector R b a c d +
      fourRootProjector R c a b d +
      fourRootProjector R d a b c = 1 := by
  ext y
  obtain ⟨ya, yb, yc, yd, hy, hya, hyb, hyc, hyd⟩ := hdecomp y
  change fourRootProjector R a b c d y +
      fourRootProjector R b a c d y +
      fourRootProjector R c a b d y +
      fourRootProjector R d a b c y = y
  rw [fourRootProjector_apply_eq_component R a b c d hab hac had
    y ya yb yc yd hy hya hyb hyc hyd]
  rw [fourRootProjector_apply_eq_component R b a c d hab.symm hbc hbd
    y yb ya yc yd]
  · rw [fourRootProjector_apply_eq_component R c a b d hac.symm hbc.symm hcd
      y yc ya yb yd]
    · rw [fourRootProjector_apply_eq_component R d a b c had.symm hbd.symm hcd.symm
        y yd ya yb yc]
      · exact hy.symm
      · simpa [add_assoc, add_left_comm, add_comm] using hy
      · exact hyd
      · exact hya
      · exact hyb
      · exact hyc
    · simpa [add_assoc, add_left_comm, add_comm] using hy
    · exact hyc
    · exact hya
    · exact hyb
    · exact hyd
  · simpa [add_assoc, add_left_comm, add_comm] using hy
  · exact hyb
  · exact hya
  · exact hyc
  · exact hyd

end RainichKaluza
