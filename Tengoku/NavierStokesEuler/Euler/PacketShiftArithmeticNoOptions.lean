import Tengoku.NavierStokesEuler.Euler.EulerProof

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Packet shift arithmetic with default resource limits

This is an independent copy of `Euler.PacketShiftArithmetic`, in a separate namespace
so both modules can be imported together. The definitions and theorem statements are
unchanged.

Removing the original recursion-depth override makes all nine `simp only` calls fail
before reaching `omega`. Replacing them with `dsimp only` suffices: only definitional
unfolding is needed, and all the original `omega` steps then succeed with Lean's default
recursion-depth and heartbeat limits. No resource-limit override is needed in this file.

Check with the Euler library's strict compiler options:
`lake env lean -DautoImplicit=false -DwarningAsError=true Euler/PacketShiftArithmeticNoOptions.lean`
-/

namespace EulerPacketShiftArithmeticNoOptions

def highShift (p : ℕ) : ℕ := 100*p-80
def meanShift (p : ℕ) : ℕ := 100*p-140
def highForceShift (p : ℕ) : ℕ := highShift p-10
def meanForceShift (p : ℕ) : ℕ := meanShift p-10

/--
@isnad1 id=eq.0h0v.s3.c9c709129988 from=translated src=- shape=3c26ae4f vocab=27776032
-/
theorem primary_shift : highShift 1=20 := rfl

/--
@isnad1 id=le.3h3v.s6.dcc858dbcae9 from=translated src=- shape=7f371e0e vocab=6912fdb3
-/
theorem slow_high_high_room (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
    highShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.3h3v.s6.614c87f35ff8 from=translated src=- shape=acc439bf vocab=ff5a00f9
-/
theorem slow_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p) :
    meanShift i+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.3h3v.s6.9b0f23339698 from=translated src=- shape=7f371e0e vocab=138f86f7
-/
theorem slow_mean_mean_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hp : i+j=p) :
    meanShift i+meanShift j+2+8 ≤ meanForceShift p := by
  dsimp only [meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.3h3v.s6.8ffa7dd687d8 from=translated src=- shape=0d8dd01e vocab=f1ab8b3a
-/
theorem fast_mean_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
    meanShift i+highShift j+2+8 ≤ highForceShift p := by
  dsimp only [highShift, meanShift, highForceShift]
  omega

/--
@isnad1 id=le.3h3v.s6.cbbaeb0413ba from=translated src=- shape=4cf84fb6 vocab=4e3d0350
-/
theorem fast_corrector_high_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hp : i+j=p+1) :
    highShift (i-1)+highShift j+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.3h3v.s6.7287e06679a8 from=translated src=- shape=1db78c30 vocab=4e3d0350
-/
theorem fast_corrector_corrector_room (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i+j=p+1) :
    highShift (i-1)+highShift (j-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.1h1v.s5.9124216fb5d8 from=translated src=- shape=6bbd2c4d vocab=4e3d0350
-/
theorem previous_linear_room (p : ℕ) (hp : 2 ≤ p) :
    highShift (p-1)+2+8 ≤ meanForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift]
  omega

/--
@isnad1 id=le.0h1v.s3.e1a0c11bb32d from=translated src=- shape=0fc427d2 vocab=b15c1636
-/
theorem mean_force_le_high_force (p : ℕ) : meanForceShift p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega

/--
@isnad1 id=and.1h1v.s5.9f0932957f06 from=translated src=- shape=a3a67172 vocab=c76d67a2
-/
theorem force_shift_dominates_grade (p : ℕ) (hp : 2 ≤ p) :
    25*p ≤ meanForceShift p ∧ 25*p ≤ highForceShift p := by
  dsimp only [highShift, meanShift, meanForceShift, highForceShift]
  omega

end EulerPacketShiftArithmeticNoOptions
