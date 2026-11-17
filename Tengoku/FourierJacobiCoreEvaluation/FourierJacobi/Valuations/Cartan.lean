import Tengoku.Seed.Data.Int.Order.Basic
import Tengoku.Seed.Tactic.SplitIfs
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Algebra.Ring.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer valuation calculation for the three region tables

The central index r = 0 means z = 0; r = 1 or 2 means v(z) = -r.
The other coordinates have finite valuations k, j, h. Zero coordinates, their
measure-zero contribution, and the local-field Cartan decomposition are separate
obligations. These theorems prove the integer calculations without a finite cutoff.
-/

namespace FourierJacobi
namespace Valuations

def baseMinimum (k j h : ℤ) : ℤ :=
  min (min (min (min (min 0 k) (-k)) (k + j)) h) (k + h)

def entryMinimum (r k j h : ℤ) : ℤ :=
  if r = 0 then baseMinimum k j h else min (baseMinimum k j h) (-r)

def determinantValuation (r j h c : ℤ) : ℤ :=
  if 2 * h = j - r then 2 * h + c else min (2 * h) (j - r)

def minorMinimum (r k j h c : ℤ) : ℤ :=
  if r = 0 then min (baseMinimum k j h) (k + 2 * h)
  else min (min (min (baseMinimum k j h) (k - r)) (-k - r))
    (k + determinantValuation r j h c)

/-- (ell, b), recovered from the minima of entries and two-by-two minors.-/
def cartanIndices (r k j h c : ℤ) : ℤ × ℤ :=
  let u := entryMinimum r k j h
  let s := minorMinimum r k j h c
  (-2 * (s - u), s - 2 * u)

def tableZero (k j h : ℤ) : ℤ × ℤ :=
  if 0 ≤ k then
    if -2 * k ≤ j then
      if -k ≤ h then (0, k) else (-2 * k - 2 * h, k)
    else if h < k + j then (-2 * k - 2 * h, k)
    else if j ≤ 2 * h then (0, -k - j)
    else (2 * j - 4 * h, 2 * h - 2 * j - k)
  else
    if 0 ≤ j then
      if 0 ≤ h then (0, -k) else (-2 * h, -k)
    else if h < j then (-2 * h, -k)
    else if j ≤ 2 * h then (0, -k - j)
    else (2 * j - 4 * h, 2 * h - 2 * j - k)

/--
@isnad1 id=eq.0h4v.s4.bdd57ab11085 from=translated src=- shape=f2181c3d vocab=b1677f78
-/
theorem tableZero_correct (k j h c : ℤ) :
    tableZero k j h = cartanIndices 0 k j h c := by
  unfold tableZero cartanIndices entryMinimum minorMinimum baseMinimum
  simp only [ite_true]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/-- The shared rows 3a--3d and 8a--8d, including the cancellation depth.-/
def collisionRows (r k j h c : ℤ) : ℤ × ℤ :=
  if j - r + 1 ≤ 2 * h then (2 * r, -k - j - r)
  else if 2 * h = j - r then (2 * (r - min c r), -k - j - r + min c r)
  else (2 * j - 4 * h, 2 * h - 2 * j - k)

def tableOne (k j h c : ℤ) : ℤ × ℤ :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then (-2 * k - 2 * h, k) else (2, k - 1)
    else if h < k + j then (-2 * k - 2 * h, k)
    else collisionRows 1 k j h c
  else
    if 0 ≤ j then
      if h < 0 then (-2 * h, -k)
      else if k = 0 then (0, 1) else (2, -k - 1)
    else if h < j then (-2 * h, -k)
    else collisionRows 1 k j h c

/--
@isnad1 id=eq.1h4v.s5.7d6dcaf246c5 from=translated src=- shape=7d72fec3 vocab=353ffdcc
-/
theorem tableOne_correct (k j h c : ℤ) (hc : 0 ≤ c) :
    tableOne k j h c = cartanIndices 1 k j h c := by
  unfold tableOne collisionRows cartanIndices entryMinimum minorMinimum
    determinantValuation baseMinimum
  simp only [one_ne_zero, ite_false]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

def tableTwo (k j h c : ℤ) : ℤ × ℤ :=
  if 1 ≤ k then
    if -2 * k ≤ j then
      if h < -k then (-2 * k - 2 * h, k)
      else if 2 ≤ k then (4, k - 2) else (2, 1)
    else if h < k + j then (-2 * k - 2 * h, k)
    else collisionRows 2 k j h c
  else
    if k = 0 ∧ -1 ≤ j then
      if h ≤ -2 then (-2 * h, 0)
      else if 0 ≤ j then (0, 2) else (2, 1)
    else if k ≤ -1 ∧ 0 ≤ j then
      if h ≤ -1 then (-2 * h, -k)
      else if k = -1 then (2, 1) else (4, -k - 2)
    else if k ≤ -1 ∧ j = -1 then
      if h ≤ -2 then
        if k = -1 then (-2 * h, 1) else (-2 * h, -k)
      else if k = -1 then (4, 0) else (4, -k - 1)
    else if h < j then (-2 * h, -k)
    else collisionRows 2 k j h c

set_option maxHeartbeats 2000000 in
/--
@isnad1 id=eq.1h4v.s5.331bcad11d53 from=translated src=- shape=7d72fec3 vocab=34cfef08
-/
theorem tableTwo_correct (k j h c : ℤ) (hc : 0 ≤ c) :
    tableTwo k j h c = cartanIndices 2 k j h c := by
  unfold tableTwo collisionRows cartanIndices entryMinimum minorMinimum
    determinantValuation baseMinimum
  simp only [show (2 : ℤ) ≠ 0 by decide, ite_false]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

/--
@isnad1 id=and.1h5v.s5.8cd64b93ba3e from=translated src=- shape=7a91ac6b vocab=9db68563
-/
theorem entry_minor_bounds (r k j h c : ℤ) (hc : 0 ≤ c) :
    2 * entryMinimum r k j h ≤ minorMinimum r k j h c ∧
      minorMinimum r k j h c ≤ entryMinimum r k j h := by
  unfold entryMinimum minorMinimum baseMinimum determinantValuation
  split_ifs <;> omega

/--
@isnad1 id=and.1h5v.s5.322bfa8f5af9 from=translated src=- shape=f1a385d7 vocab=a605baa6
-/
theorem cartanIndices_nonnegative (r k j h c : ℤ) (hc : 0 ≤ c) :
    0 ≤ (cartanIndices r k j h c).1 ∧ 0 ≤ (cartanIndices r k j h c).2 := by
  have hb := entry_minor_bounds r k j h c hc
  unfold cartanIndices
  simp only
  omega

/--
@isnad1 id=even.0h5v.s4.24e35ef0c951 from=translated src=- shape=9812e0ec vocab=f572bb1f
-/
theorem cartanIndices_even (r k j h c : ℤ) : Even (cartanIndices r k j h c).1 := by
  change Even (-2 * (minorMinimum r k j h c - entryMinimum r k j h))
  refine ⟨entryMinimum r k j h - minorMinimum r k j h c, ?_⟩
  omega

/-- The elementary inequality underlying the fixed-central-coordinate majorant.
@isnad1 id=le.0h2v.s6.85f8c91f402e from=translated src=- shape=fb4e01c3 vocab=ff1b0ec2
-/
theorem central_majorant (u v : ℤ) :
    2 * (u + v - max u v - max u (2 * v)) ≤ -max u v := by
  omega

end Valuations
end FourierJacobi
