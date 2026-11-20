/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.AngularDomainTopology
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapPeaks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact transport between original nodes and normalized angular configurations -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n d : ℕ}

lemma NodeFamily.eq_of_points_eq (nodes other : NodeFamily n)
    (h : ∀ i, nodes.point i = other.point i) : nodes = other := by
  have hp : nodes.point = other.point := funext h
  cases nodes
  cases other
  cases hp
  rfl

/--
@isnad1 id=eq.1h2v.s5.9e57e68bebbb from=translated src=- shape=dc90c2dd vocab=bb5c38c0
-/
lemma orderedAngles_toNodeFamily_eq (nodes : NodeFamily n) (hn : 0 < n) :
    (orderedAngles nodes hn).toNodeFamily =
      (anchoredNodes nodes hn).reindex (anchoredNodes nodes hn).sortedPermutation := by
  apply NodeFamily.eq_of_points_eq
  intro i
  exact (anchoredNodes nodes hn).exp_sortedPhase i

/--
@isnad1 id=eq.1h2v.s4.286adf17f6ba from=translated src=- shape=885d83f2 vocab=85cc4548
-/
lemma angularAmplification_orderedAngles (nodes : NodeFamily n) (hn : 0 < n) :
    angularAmplification (orderedAngles nodes hn) = amplification nodes := by
  unfold angularAmplification
  rw [orderedAngles_toNodeFamily_eq, amplification_reindex]
  exact amplification_rotate nodes _

/--
@isnad1 id=iff.1h2v.s4.5287f0871316 from=translated src=- shape=5cc094d6 vocab=a28d2d12
-/
lemma isMinimizer_orderedAngles_iff (nodes : NodeFamily n) (hn : 0 < n) :
    IsMinimizer (orderedAngles nodes hn).toNodeFamily ↔ IsMinimizer nodes := by
  rw [orderedAngles_toNodeFamily_eq, isMinimizer_reindex_iff]
  exact isMinimizer_rotate_iff nodes _

/--
@isnad1 id=iff.1h2v.s4.ca500abaa1dc from=translated src=- shape=5cc094d6 vocab=1a64cc7c
-/
lemma isRegularRotation_orderedAngles_iff (nodes : NodeFamily n) (hn : 0 < n) :
    IsRegularRotation (orderedAngles nodes hn).toNodeFamily ↔ IsRegularRotation nodes := by
  rw [orderedAngles_toNodeFamily_eq, isRegularRotation_reindex_iff]
  exact isRegularRotation_rotate_iff nodes _

/--
@isnad1 id=eq.0h1v.s5.53bf8b950034 from=translated src=- shape=d777db40 vocab=49cdf74e
-/
lemma regularAngularParameters_toNodeFamily (d : ℕ) :
    (cyclicAnglesOfParameters (regularAngularParameters d)
      (regularAngularParameters_mem_domain d)).toNodeFamily =
        regularNodes (d + 1) (Nat.succ_pos d) := by
  apply NodeFamily.eq_of_points_eq
  intro i
  change Circle.exp (angularParameterAngles (regularAngularParameters d) i) = regularPoint _ i
  rw [angularParameterAngles_regular]
  rfl

/--
@isnad1 id=isregula.1h2v.s5.741a98ca5bea from=translated src=- shape=eaa48004 vocab=807a2152
-/
lemma CyclicAngles.isRegularRotation_of_parameters_eq_regular
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (h : angles.interiorParameters = regularAngularParameters d) :
    IsRegularRotation angles.toNodeFamily := by
  have hpoints : ∀ i, angles.toNodeFamily.point i = (regularNodes (d + 1) (Nat.succ_pos d)).point i := by
    intro i
    change Circle.exp (angles.angle i) = regularPoint _ i
    rw [← angularParameterAngles_interiorParameters angles, h, angularParameterAngles_regular]
    rfl
  rw [NodeFamily.eq_of_points_eq _ _ hpoints]
  exact regularNodes_isRegularRotation _ _

end

end UnitCircleInterpolation
