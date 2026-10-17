import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.CoordinatePartials

namespace OAI

/-! Transport the actual coordinate partials through a specified, proved
algebra equivalence. Coefficients in the whole relative coefficient algebra
are fixed, even when the derivations are viewed over a smaller ground ring. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L I : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L]

def localizedPartial (e : L ≃ₐ[K] MvPolynomial I B) (i : I) : Derivation K L L :=
  transportDerivation e ((pderiv i : Derivation B (MvPolynomial I B) _).restrictScalars K)

/--
@isnad1 id=eq.0h7v.s9.6e20fef63cfa from=translated src=- shape=593328c4 vocab=85120e80
-/
@[simp] theorem localizedPartial_apply (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = e.symm (pderiv i (e a)) := rfl

/--
@isnad1 id=locallyn.0h6v.s6.4e02ee2ae037 from=translated src=- shape=0c6431c8 vocab=8b561616
-/
theorem localizedPartial_locallyNilpotent (e : L ≃ₐ[K] MvPolynomial I B) (i : I) :
    LocallyNilpotent (localizedPartial e i) :=
  transportDerivation_locallyNilpotent e _ (coordinate_partial_locallyNilpotent i)

/--
@isnad1 id=eq.1h8v.s8.6c5e5d4ce601 from=translated src=- shape=2a210299 vocab=88dce007
-/
theorem localizedPartial_fixes_relative (e : L ≃ₐ[K] MvPolynomial I B)
    (i : I) (a : L) (b : B) (hab : e a = C b) : localizedPartial e i a = 0 := by
  rw [localizedPartial_apply, hab, pderiv_C, map_zero]

/--
@isnad1 id=eq.0h7v.s8.3f7344395819 from=translated src=- shape=a3d15263 vocab=390c47be
-/
theorem localizedPartial_coordinate [DecidableEq I]
    (e : L ≃ₐ[K] MvPolynomial I B) (i j : I) :
    localizedPartial e i (e.symm (X j)) = if i = j then 1 else 0 := by
  simp [localizedPartial_apply, pderiv_X, Pi.single_apply, eq_comm]

/--
@isnad1 id=iff.0h7v.s9.d32569b71f59 from=translated src=- shape=37d2e878 vocab=bc7cdf61
-/
theorem localizedPartial_kernel (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = 0 ↔ pderiv i (e a) = 0 := by
  constructor
  · intro h
    have hh := congrArg e h
    simpa only [localizedPartial_apply, e.apply_symm_apply, map_zero] using hh
  · intro h
    rw [localizedPartial_apply, h, map_zero]

end AbhyankarSathaye.CommutingDerivations

end

end OAI
