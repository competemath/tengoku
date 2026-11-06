import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

variable [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A]

end FormalGroup

end

end

end

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

noncomputable def nthSeries (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries

end FormalGroup

end

end

end

section
section

open scoped Classical

namespace MvPowerSeries
variable {σ : Type*} {R : Type*} [CommRing R]

end MvPowerSeries

end

end

section
section

noncomputable section

open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

end FormalGroup

end

end

end

section
section

set_option maxHeartbeats 1200000

noncomputable section
open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

end FormalGroup

end

end

end
