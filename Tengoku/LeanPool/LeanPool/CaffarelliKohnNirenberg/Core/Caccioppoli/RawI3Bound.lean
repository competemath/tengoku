/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.RawI3
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Raw I3 Bound

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

/-- Raw pressure contribution paired with velocity and the spatial gradient of the heat cutoff. -/
def caccioppoliI3HeatCutoffRaw
    {p : ParabolicPoint → ℝ} {v : ParabolicPoint → Vec3}
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) : ℝ :=
  (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
      (2 : ℝ≥0∞) * ENNReal.ofReal |p w| *
        ENNReal.ofReal (vec3EuclideanNorm (v w)) *
        ENNReal.ofReal (∑ i, |spatialPartial (fun y : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r y) i w|)).toReal

end CKN
