/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.AngularGlobalInverse
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.MinimumEquioscillation
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.RegularHeights
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.NodeTransport
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.OneNode
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.ComplexNodes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full minimizer classification for Lagrange interpolation on the unit circle

Existence of a minimum and the deleted-row descent argument force its actual
gap heights to be equal. Global injectivity of the actual height-difference map
identifies that configuration with the literal regular polygon. Rotation and
enumeration invariance then give the classification for arbitrary original
complex nodes. The one-node case is included separately.

The mathematical theorem is due to Brutman and Brutman–Pinkus, using the
trigonometric/global framework of de Boor–Pinkus. Reused generic proof kernels
retain their notices in the corresponding modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The actual zero of the circular difference map is exactly the regular polygon.
@isnad1 id=iff.1h2v.s6.182079a15c52 from=translated src=- shape=155e967f vocab=ee03b91a
-/
theorem heightDifferenceMap_eq_zero_iff_regular (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    heightDifferenceMap hsize u = 0 ↔ u.val = regularAngularParameters d := by
  let r : angularParameterDomain d :=
    ⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩
  have hr : heightDifferenceMap hsize r = 0 :=
    parameterAdjacentHeightDifferences_regular_eq_zero hsize
  constructor
  · intro hu
    exact congrArg Subtype.val (heightDifferenceMap_injective hsize (hu.trans hr.symm))
  · intro hu
    have hur : u = r := Subtype.ext hu
    exact hur ▸ hr

/--
@isnad1 id=iff.1h2v.s7.1fe459426653 from=translated src=- shape=4d8e5239 vocab=3dd1aa98
-/
theorem equal_parameterOrderedHeights_iff_regular (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    (∀ i, parameterOrderedHeight hsize i u.val = parameterOrderedHeight hsize 0 u.val) ↔
      u.val = regularAngularParameters d := by
  rw [← heightDifferenceMap_eq_zero_iff, heightDifferenceMap_eq_zero_iff_regular]

/-- The literal circle objective has exactly one normalized minimizer.
@isnad1 id=iff.1h2v.s6.a68712bf8dc2 from=translated src=- shape=863dd34d vocab=4d96dc2c
-/
theorem minimum_angularParameterAmplification_iff_regular (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    (∀ v : angularParameterDomain d,
      angularParameterAmplification hsize u ≤ angularParameterAmplification hsize v) ↔
        u.val = regularAngularParameters d := by
  constructor
  · intro hmin
    exact (equal_parameterOrderedHeights_iff_regular hsize u).mp
      (equal_parameterOrderedHeights_of_minimum hsize u hmin)
  · intro hu
    obtain ⟨m, hm⟩ := exists_minimum_angularParameterAmplification hsize
    have hmreg := (equal_parameterOrderedHeights_iff_regular hsize m).mp
      (equal_parameterOrderedHeights_of_minimum hsize m hm)
    have hum : u = m := Subtype.ext (hu.trans hmreg.symm)
    exact hum ▸ hm

/--
@isnad1 id=eq.1h1v.s6.a66b8e5f721f from=translated src=- shape=01046e6f vocab=c002f725
-/
lemma angularParameterAmplification_regular (hsize : 2 ≤ d + 1) :
    angularParameterAmplification hsize
      ⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩ =
        amplification (regularNodes (d + 1) (Nat.succ_pos d)) := by
  change amplification _ = _
  rw [regularAngularParameters_toNodeFamily]

/--
@isnad1 id=eq.1h2v.s6.c2b0be8846d7 from=translated src=- shape=1d5cabb2 vocab=3a43f05f
-/
lemma angularParameterAmplification_ordered (hsize : 2 ≤ d + 1)
    (nodes : NodeFamily (d + 1)) :
    angularParameterAmplification hsize
      ⟨(orderedAngles nodes (Nat.succ_pos d)).interiorParameters,
        (orderedAngles nodes (Nat.succ_pos d)).interiorParameters_mem_domain⟩ =
          amplification nodes := by
  change angularAmplification _ = _
  rw [cyclicAnglesOfParameters_interiorParameters, angularAmplification_orderedAngles]

/-- Regular nodes minimize the actual full-circle supremum against all distinct circle nodes.
@isnad1 id=isminimi.1h1v.s5.f1dfa2e04e75 from=translated src=- shape=a9a15702 vocab=d6594c43
-/
theorem isMinimizer_regularNodes_of_two_le (hsize : 2 ≤ d + 1) :
    IsMinimizer (regularNodes (d + 1) (Nat.succ_pos d)) := by
  have hmin := (minimum_angularParameterAmplification_iff_regular hsize
    ⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩).mpr rfl
  intro other
  have h := hmin
    ⟨(orderedAngles other (Nat.succ_pos d)).interiorParameters,
      (orderedAngles other (Nat.succ_pos d)).interiorParameters_mem_domain⟩
  rwa [angularParameterAmplification_regular, angularParameterAmplification_ordered] at h

/--
@isnad1 id=isregula.2h2v.s6.59b7ed749773 from=translated src=- shape=8e1971f7 vocab=38e36c8c
-/
theorem isRegularRotation_of_isMinimizer_of_two_le (hsize : 2 ≤ d + 1)
    (nodes : NodeFamily (d + 1)) (hmin : IsMinimizer nodes) : IsRegularRotation nodes := by
  let angles := orderedAngles nodes (Nat.succ_pos d)
  let u : angularParameterDomain d :=
    ⟨angles.interiorParameters, angles.interiorParameters_mem_domain⟩
  have hu : ∀ v : angularParameterDomain d,
      angularParameterAmplification hsize u ≤ angularParameterAmplification hsize v := by
    intro v
    have hleft : angularParameterAmplification hsize u = amplification nodes :=
      angularParameterAmplification_ordered hsize nodes
    rw [hleft]
    exact hmin (cyclicAnglesOfParameters v.val v.property).toNodeFamily
  have hreg : angles.interiorParameters = regularAngularParameters d :=
    (minimum_angularParameterAmplification_iff_regular hsize u).mp hu
  exact (isRegularRotation_orderedAngles_iff nodes (Nat.succ_pos d)).mp
    (angles.isRegularRotation_of_parameters_eq_regular hreg)

/--
@isnad1 id=isminimi.2h2v.s6.c332096cb253 from=translated src=- shape=8e1971f7 vocab=38e36c8c
-/
theorem isMinimizer_of_isRegularRotation_of_two_le (hsize : 2 ≤ d + 1)
    (nodes : NodeFamily (d + 1)) (hreg : IsRegularRotation nodes) : IsMinimizer nodes := by
  obtain ⟨rotation, permutation, hpoints⟩ := hreg
  have heq : nodes =
      ((regularNodes (d + 1) (Nat.succ_pos d)).reindex permutation).rotate rotation :=
    NodeFamily.eq_of_points_eq _ _ hpoints
  rw [heq, isMinimizer_rotate_iff, isMinimizer_reindex_iff]
  exact isMinimizer_regularNodes_of_two_le hsize

/-- Complete classification for every positive number of nodes and every enumeration.
@isnad1 id=iff.1h2v.s4.5b7f338ad3d4 from=translated src=- shape=2b3dbf42 vocab=a4f17e1f
-/
theorem minimizer_iff_regular (n : ℕ) (hn : 0 < n) (nodes : NodeFamily n) :
    IsMinimizer nodes ↔ IsRegularRotation nodes := by
  cases n with
  | zero => omega
  | succ d =>
    by_cases hd : d = 0
    · subst d
      exact minimizer_iff_regular_one nodes
    · have hsize : 2 ≤ d + 1 := by omega
      exact ⟨isRegularRotation_of_isMinimizer_of_two_le hsize nodes,
        isMinimizer_of_isRegularRotation_of_two_le hsize nodes⟩

/--
@isnad1 id=isminimi.1h1v.s4.9c148a427f42 from=translated src=- shape=dd19ab6e vocab=c9e3326c
-/
theorem isMinimizer_regularNodes (n : ℕ) (hn : 0 < n) : IsMinimizer (regularNodes n hn) :=
  (minimizer_iff_regular n hn _).mpr (regularNodes_isRegularRotation n hn)

/-- An inhabitant of the full original target, including existence and both classification directions.
@isnad1 id=target.0h0v.s0.456cebbb4dbe from=translated src=- shape=45709ebd vocab=456cebbb
-/
theorem unitCircleInterpolation_target : Target := by
  intro n hn
  exact ⟨⟨regularNodes n hn, isMinimizer_regularNodes n hn⟩, minimizer_iff_regular n hn⟩

/-- The same classification for arbitrary injective complex unit-modulus coordinates.
@isnad1 id=iff.3h2v.s5.076189dcbd0c from=translated src=- shape=0e4f698d vocab=918c7d95
-/
theorem complex_minimizer_iff_regular (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    IsComplexMinimizer z ↔ IsComplexRegularRotation z := by
  rw [isComplexMinimizer_ofCoordinates_iff z hunit hinj,
    isComplexRegularRotation_ofCoordinates_iff z hunit hinj]
  exact minimizer_iff_regular n hn _

/-- The original lower bound uses the literal cardinal product and supremum on the whole unit circle.
@isnad1 id=le.3h2v.s5.7823517e1bee from=translated src=- shape=82e590f4 vocab=438ef664
-/
theorem complexAmplification_regular_le (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    complexAmplification (regularNodes n hn).coordinates ≤ complexAmplification z :=
  isMinimizer_regularNodes n hn (NodeFamily.ofCoordinates z hunit hinj)

end

end UnitCircleInterpolation
