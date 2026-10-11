/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Tengoku

/-!
# Unit-distance counting

The unit-distance pair count for finite planar sets, the ordered variant
for subsets of `ℂ`, and transport along the isometry `ℂ ≃ ℝ²`.
-/

open scoped Classical

namespace Erdos

/-! ## Unit-distance counting -/

/-- For a finite planar set `P ⊆ ℝ²`, `unitDist P` is the number of
unordered pairs `{x, y} ⊆ P` at Euclidean distance exactly `1`.
(Identical to the definition in the lean-eval problem
`erdos_unit_distance_conjecture_false`.) -/
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2

/-- The number of *ordered* pairs of distinct points of `P ⊆ ℂ` at
distance exactly `1`.  The geometric core produces planar sets inside `ℂ`;
`exists_euclidean_copy` transports the count to `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def unitPairsC (P : Finset ℂ) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/-- The standard real-linear isometry `ℂ ≃ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def complexToPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

end Erdos
