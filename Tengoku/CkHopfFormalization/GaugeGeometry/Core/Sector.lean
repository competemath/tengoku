import Tengoku.Seed.Data.Rat.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace GaugeGeometry.Core

/--
Bookkeeping labels for the three gauge sectors.
This file is intentionally neutral and upstream of all QFT layers.-/
inductive GaugeSector where
  | hypercharge
  | weak
  | color
  deriving DecidableEq, Repr

/--
A minimal record of sector weights.

Interpretation is deferred to downstream layers:
- `hypercharge` : U(1) sector weight
- `weak`        : SU(2) sector weight
- `color`       : SU(3) sector weight-/
structure SectorWeights where
  hypercharge : ℚ
  weak : ℚ
  color : ℚ
  deriving Repr

/--
Access a sector weight by label.-/
def SectorWeights.get (w : SectorWeights) : GaugeSector → ℚ
  | .hypercharge => w.hypercharge
  | .weak        => w.weak
  | .color       => w.color

@[simp] theorem SectorWeights.get_hypercharge (w : SectorWeights) :
    w.get GaugeSector.hypercharge = w.hypercharge := by
  rfl

@[simp] theorem SectorWeights.get_weak (w : SectorWeights) :
    w.get GaugeSector.weak = w.weak := by
  rfl

@[simp] theorem SectorWeights.get_color (w : SectorWeights) :
    w.get GaugeSector.color = w.color := by
  rfl

/--
A convenience constructor from a sector-indexed function.-/
def sectorWeightsOfFn (f : GaugeSector → ℚ) : SectorWeights where
  hypercharge := f .hypercharge
  weak := f .weak
  color := f .color

@[simp] theorem sectorWeightsOfFn_get (f : GaugeSector → ℚ) (s : GaugeSector) :
    (sectorWeightsOfFn f).get s = f s := by
  cases s <;> rfl

/--
Extensionality for sector weights.-/
theorem SectorWeights.ext
    (w₁ w₂ : SectorWeights)
    (hhyper : w₁.hypercharge = w₂.hypercharge)
    (hweak : w₁.weak = w₂.weak)
    (hcolor : w₁.color = w₂.color) :
    w₁ = w₂ := by
  cases w₁
  cases w₂
  simp at hhyper hweak hcolor
  simp [hhyper, hweak, hcolor]

/--
Equivalent extensionality phrased through sector access.-/
theorem SectorWeights.ext_get
    (w₁ w₂ : SectorWeights)
    (h : ∀ s : GaugeSector, w₁.get s = w₂.get s) :
    w₁ = w₂ := by
  apply SectorWeights.ext
  · simpa using h .hypercharge
  · simpa using h .weak
  · simpa using h .color

end GaugeGeometry.Core
