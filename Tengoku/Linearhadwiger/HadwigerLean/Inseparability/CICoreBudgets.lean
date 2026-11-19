import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial core budget for the CI stage invariant

The quadratic bound pays for one small piece per old block, the
knitting piece, and the new region tangencies at every stage.
-/

namespace HadwigerLean.Inseparability

def ciCoreBound (N x u : ℕ) : ℕ := 2 * u * u * (N + x)

/--
@isnad1 id=eq.0h2v.s4.2b064f1232be from=translated src=- shape=9bf57cd7 vocab=c072fd33
-/
@[simp] theorem ciCoreBound_zero (N x : ℕ) :
    ciCoreBound N x 0 = 0 := by
  simp [ciCoreBound]

/--
@isnad1 id=le.1h4v.s4.59a2151fef08 from=translated src=- shape=299e37de vocab=f06d1f89
-/
theorem ciCoreBound_mono (N x u r : ℕ) (hur : u ≤ r) :
    ciCoreBound N x u ≤ ciCoreBound N x r := by
  unfold ciCoreBound
  calc
    2 * u * u * (N + x) = 2 * (u * u) * (N + x) := by ring
    _ ≤ 2 * (r * r) * (N + x) :=
      Nat.mul_le_mul_right (N + x)
        (Nat.mul_le_mul_left 2 (Nat.mul_self_le_mul_self hur))
    _ = 2 * r * r * (N + x) := by ring

/--
@isnad1 id=le.0h2v.s4.573459214d4e from=translated src=- shape=8f256d52 vocab=35dc928b
-/
theorem ciCoreBound_first (N x : ℕ) :
    N + x ≤ ciCoreBound N x 1 := by
  simp only [ciCoreBound, mul_one, one_mul]
  omega

/--
@isnad1 id=le.0h3v.s6.a8f99221a5e0 from=translated src=- shape=1288812b vocab=5be7a085
-/
theorem ciCoreBound_step (N x u : ℕ) :
    ciCoreBound N x u + u * N + N + (u + 1) * x ≤
      ciCoreBound N x (u + 1) := by
  unfold ciCoreBound
  nlinarith [Nat.zero_le (u * (N + x))]

/--
@isnad1 id=le.1h3v.s5.4a25c8f91db3 from=translated src=- shape=0a861586 vocab=e728ffd6
-/
theorem ciCoreBound_localWindow (N x r : ℕ) (hr : 0 < r) :
    r * N ≤ 3 * ciCoreBound N x r := by
  unfold ciCoreBound
  have hr1 : 1 ≤ r := hr
  nlinarith [Nat.zero_le (r * x), Nat.zero_le (r * N)]

end HadwigerLean.Inseparability
