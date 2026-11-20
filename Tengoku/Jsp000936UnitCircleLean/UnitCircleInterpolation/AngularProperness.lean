/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakLocalInverse
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.HeightDifferenceBoundary
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.AngularCompactSets
import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Topology.Maps.Proper.CompactlyGenerated

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Properness of the actual height-difference map

A compact set of height differences has a bounded norm. The literal collision
estimate puts its preimage in a compact angular simplex whose gaps are uniformly
positive. Continuity makes this preimage closed in the actual domain, so it is
compact. No global inverse or minimizer hypothesis enters this proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/--
@isnad1 id=iscompac.1h2v.s7.016a78d0f268 from=translated src=- shape=2a179791 vocab=b65957c7
-/
lemma isCompact_shrunkenAngularSimplex_subtype {ε : ℝ} (hε : 0 < ε) :
    IsCompact {u : angularParameterDomain d | u.val ∈ shrunkenAngularSimplex d ε} := by
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    (isCompact_shrunkenAngularSimplex hε)
  intro u hu
  exact ⟨⟨u, shrunkenAngularSimplex_subset_domain hε hu⟩, rfl⟩

/-- Every compact set of actual height differences has compact preimage.
@isnad1 id=iscompac.2h2v.s6.ae904c37edf2 from=translated src=- shape=02b626c0 vocab=f7158001
-/
theorem isCompact_preimage_heightDifferenceMap (hsize : 2 ≤ d + 1)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    IsCompact (heightDifferenceMap hsize ⁻¹' K) := by
  obtain ⟨R, hR, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  let ε := heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R)
  have hε : 0 < ε := heightDifferenceBoundaryMargin_pos d R hR.le
  apply (isCompact_shrunkenAngularSimplex_subtype hε).of_isClosed_subset
    (hK.isClosed.preimage (continuous_heightDifferenceMap hsize))
  intro u hu cut
  exact parameterGapWidth_lower_of_adjacent_height_norm_le hsize u.val u.property R hR.le
    (hnorm (heightDifferenceMap hsize u) hu) cut

/-- The actual difference map is proper on the admissible angular domain.
@isnad1 id=isproper.1h1v.s6.aa662ed3747b from=translated src=- shape=2176ad16 vocab=01402597
-/
theorem isProperMap_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    IsProperMap (heightDifferenceMap hsize) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  exact ⟨continuous_heightDifferenceMap hsize,
    fun _ hK => isCompact_preimage_heightDifferenceMap hsize hK⟩

end

end UnitCircleInterpolation
