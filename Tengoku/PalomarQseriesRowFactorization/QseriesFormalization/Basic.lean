import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic objects for q-series formalization

Definitions used throughout *An Invitation to q-Series* (Hei-Chi Chan, 2011):
partitions, triangular and pentagonal numbers, the q-Pochhammer symbol,
finite sums, and Gaussian (q-binomial) coefficients.

These live in the root `QseriesFormalization` namespace so individual
chapters (in `QseriesFormalization.PartI.Ch02` etc.) can reuse them
without prefix juggling.
-/

namespace QseriesFormalization

/-! ### Partitions (Ch 1) -/

/-- A partition is represented by a weakly decreasing list of nonnegative integers.-/
def IsPartition (l : List Nat) : Prop :=
  l.Pairwise (fun a b => b ≤ a)

/-- The size (or weight) of a partition.-/
def partitionWeight : List Nat → Nat
  | [] => 0
  | n :: l => n + partitionWeight l

/--
@isnad1 id=eq.0h0v.s3.2149de86df34 from=translated src=- shape=c15d4c7a vocab=84b53204
-/
@[simp] theorem partitionWeight_nil : partitionWeight [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.4034d757586e from=translated src=- shape=fcb3fea8 vocab=02983570
-/
@[simp] theorem partitionWeight_cons (n : Nat) (l : List Nat) :
    partitionWeight (n :: l) = n + partitionWeight l := rfl

/--
@isnad1 id=eq.0h2v.s5.50ff9aeb44c5 from=translated src=- shape=22876443 vocab=94732b43
-/
theorem partitionWeight_append (l1 l2 : List Nat) :
    partitionWeight (l1 ++ l2) = partitionWeight l1 + partitionWeight l2 := by
  induction l1 with
  | nil =>
      simp [partitionWeight]
  | cons a t ih =>
      simpa [partitionWeight, Nat.add_assoc] using congrArg (fun x => a + x) ih

/-! ### Triangular and pentagonal numbers (Ch 1, Ch 4) -/

/-- Triangular number `n (n + 1) / 2`.-/
def triangular (n : Nat) : Nat :=
  n * (n + 1) / 2

/--
@isnad1 id=eq.0h0v.s3.2e264d2910ff from=translated src=- shape=3c26ae4f vocab=8c612d63
-/
@[simp] theorem triangular_zero : triangular 0 = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.d05c9351d1a4 from=translated src=- shape=3c26ae4f vocab=8c612d63
-/
@[simp] theorem triangular_one : triangular 1 = 1 := by
  simp [triangular]

/-- `triangular` recursion: T(n+1) = T(n) + (n+1).
@isnad1 id=eq.0h1v.s4.1d6286d51462 from=translated src=- shape=a0ed7b26 vocab=58e96b90
-/
theorem triangular_succ (n : Nat) :
    triangular (Nat.succ n) = triangular n + Nat.succ n := by
  simpa [triangular, Nat.succ_eq_add_one, Nat.mul_comm] using Nat.triangle_succ (Nat.succ n)

/-- `triangular` doubled is n(n+1).
@isnad1 id=eq.0h1v.s5.7e30b39f0953 from=translated src=- shape=e492614d vocab=6101bfc5
-/
theorem two_mul_triangular (n : Nat) :
    2 * triangular n = n * (n + 1) := by
  have hchoose : Nat.choose (n + 1) 2 = triangular n := by
    rw [Nat.choose_two_right]
    simp [triangular, Nat.mul_comm]
  have hmul := Nat.add_one_mul_choose_eq n 1
  simp [Nat.choose_one_right] at hmul
  rw [hchoose] at hmul
  simpa [Nat.mul_comm] using hmul.symm

/-- Pentagonal number `k (3k - 1) / 2`, used in Euler's pentagonal theorem.-/
def pentagonalNumber (k : Nat) : Nat :=
  k * (3 * k - 1) / 2

/--
@isnad1 id=eq.0h0v.s3.299a1f3f79f0 from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
@[simp] theorem pentagonalNumber_zero : pentagonalNumber 0 = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.5d0a26ad8e3b from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
@[simp] theorem pentagonalNumber_one : pentagonalNumber 1 = 1 := by
  simp [pentagonalNumber]

/-- pentagonalNumber recursion: P(k+1) = P(k) + (3k+1).
@isnad1 id=eq.0h1v.s5.64a806b39726 from=translated src=- shape=0450d5a3 vocab=f7b42bac
-/
theorem pentagonalNumber_succ (k : Nat) :
    pentagonalNumber (Nat.succ k) = pentagonalNumber k + (3 * k + 1) := by
  have hp : ∀ k : Nat, pentagonalNumber k = Nat.choose k 2 + k * k := by
    intro k
    unfold pentagonalNumber
    rw [Nat.choose_two_right]
    have hnum : k * (3 * k - 1) = k * (k - 1) + 2 * (k * k) := by
      cases k with
      | zero =>
          norm_num
      | succ j =>
          have h₁ : 3 * (j + 1) - 1 = 3 * j + 2 := by omega
          have h₂ : j + 1 - 1 = j := by omega
          rw [h₁, h₂]
          ring
    rw [hnum]
    rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  rw [hp (Nat.succ k), hp k]
  have hchoose : Nat.choose (Nat.succ k) 2 = Nat.choose k 2 + k := by
    rw [show 2 = Nat.succ 1 by rfl, Nat.choose_succ_succ]
    simp [Nat.choose_one_right, Nat.add_comm]
  rw [hchoose, Nat.succ_eq_add_one]
  ring

/-- Concrete value of the second pentagonal number.
@isnad1 id=eq.0h0v.s3.5804e7e6c87a from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
theorem pentagonalNumber_two : pentagonalNumber 2 = 5 := by
  norm_num [pentagonalNumber]

/-- Concrete value of the third pentagonal number.
@isnad1 id=eq.0h0v.s3.d9642e3a53c1 from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
theorem pentagonalNumber_three : pentagonalNumber 3 = 12 := by
  norm_num [pentagonalNumber]

/-- Concrete value of the fourth pentagonal number.
@isnad1 id=eq.0h0v.s3.cefa01a8047c from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
theorem pentagonalNumber_four : pentagonalNumber 4 = 22 := by
  norm_num [pentagonalNumber]

/-- Concrete value of the fifth pentagonal number.
@isnad1 id=eq.0h0v.s3.a36882d24431 from=translated src=- shape=3c26ae4f vocab=99f44db7
-/
theorem pentagonalNumber_five : pentagonalNumber 5 = 35 := by
  norm_num [pentagonalNumber]

/-! ### q-Pochhammer (Ch 1) -/

section CommRing

variable {R : Type*} [CommRing R]

/-- Finite q-Pochhammer symbol `(q; q)_n = ∏_{j=1}^n (1 - q^j)`.-/
def qPochhammer (q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qPochhammer q n * (1 - q ^ (Nat.succ n))

/-- General q-Pochhammer symbol `(a; q)_n = ∏_{k=0}^{n-1} (1 - a q^k)`.-/
def qPoch (a q : R) : Nat → R
  | 0 => 1
  | Nat.succ n => qPoch a q n * (1 - a * q ^ n)

/--
@isnad1 id=eq.0h2v.s5.7bec67c1a413 from=translated src=- shape=4e114734 vocab=837bc2b2
-/
@[simp] theorem qPochhammer_zero (q : R) : qPochhammer q 0 = 1 := rfl

/--
@isnad1 id=eq.0h3v.s6.e986434bb6c4 from=translated src=- shape=e6b43771 vocab=2b823de8
-/
@[simp] theorem qPochhammer_succ (q : R) (n : Nat) :
    qPochhammer q (Nat.succ n) = qPochhammer q n * (1 - q ^ (Nat.succ n)) := rfl

/--
@isnad1 id=eq.0h3v.s5.813ea7e96ead from=translated src=- shape=9c02e61a vocab=5d70eb9c
-/
@[simp] theorem qPoch_zero (a q : R) : qPoch a q 0 = 1 := rfl

/--
@isnad1 id=eq.0h4v.s6.18bc8df2ff69 from=translated src=- shape=d2b755f8 vocab=dc7b58c6
-/
@[simp] theorem qPoch_succ (a q : R) (n : Nat) :
    qPoch a q (Nat.succ n) = qPoch a q n * (1 - a * q ^ n) := rfl

/--
@isnad1 id=eq.0h3v.s4.3bce17cdddc1 from=translated src=- shape=e5128f7a vocab=0c944108
-/
@[simp] theorem qPoch_q_eq_qPochhammer (q : R) (n : Nat) : qPoch q q n = qPochhammer q n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [qPoch_succ, qPochhammer_succ, ih, pow_succ]
      ring

/--
@isnad1 id=eq.0h2v.s5.3cdc1b8a5c43 from=translated src=- shape=dbaa1b2b vocab=c1c0b7f8
-/
@[simp] theorem qPochhammer_one_succ (n : Nat) :
    qPochhammer (R := R) 1 (Nat.succ n) = 0 := by
  simp [qPochhammer]

/--
@isnad1 id=eq.0h2v.s5.d2e979d670f6 from=translated src=- shape=003ae1f3 vocab=5b3c95eb
-/
theorem qPochhammer_one (q : R) :
    qPochhammer q 1 = 1 - q := by
  simp [qPochhammer]

end CommRing

/-! ### Finite sums (Ch 3) -/

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- A simple finite summation helper: `natSum f n = f 0 + … + f n`.-/
def natSum (f : Nat → R) : Nat → R
  | 0 => f 0
  | Nat.succ n => natSum f n + f (Nat.succ n)

/--
@isnad1 id=eq.0h2v.s4.ef8dafac4191 from=translated src=- shape=72df634b vocab=c0959463
-/
@[simp] theorem natSum_zero (f : Nat → R) : natSum f 0 = f 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.a70207a873e8 from=translated src=- shape=3a1dc862 vocab=ca6825aa
-/
@[simp] theorem natSum_succ (f : Nat → R) (n : Nat) :
    natSum f (Nat.succ n) = natSum f n + f (Nat.succ n) := rfl

/-- Bilateral sum `∑_{j = -N}^{N} f j`. Implemented as
`f 0 + ∑_{k=1}^{N} (f k + f (-k))`.-/
def bilateralSum (f : Int → R) : Nat → R
  | 0 => f 0
  | Nat.succ n => bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int)))

/--
@isnad1 id=eq.0h2v.s4.bda11de97351 from=translated src=- shape=e7af9fd2 vocab=8aa9e8ac
-/
@[simp] theorem bilateralSum_zero (f : Int → R) : bilateralSum f 0 = f 0 := rfl

/--
@isnad1 id=eq.0h3v.s6.14da643c27f9 from=translated src=- shape=b19d82bf vocab=556e68aa
-/
@[simp] theorem bilateralSum_succ (f : Int → R) (n : Nat) :
    bilateralSum f (Nat.succ n) =
      bilateralSum f n + (f (n + 1 : Int) + f (-(n + 1 : Int))) := rfl

/--
@isnad1 id=eq.1h4v.s5.0c6ea0df05f2 from=translated src=- shape=2314f591 vocab=323cff0c
-/
theorem bilateralSum_congr {f g : Int → R} :
    ∀ n : Nat, (∀ j : Int, -(n : Int) ≤ j ∧ j ≤ (n : Int) → f j = g j) →
      bilateralSum f n = bilateralSum g n := by
  intro n
  induction n with
  | zero =>
      intro h
      exact h 0 (by omega)
  | succ n ih =>
      intro h
      rw [bilateralSum_succ, bilateralSum_succ]
      have hprev : bilateralSum f n = bilateralSum g n := by
        exact ih (by
          intro j hj
          exact h j (by omega))
      have hpos : f (n + 1 : Int) = g (n + 1 : Int) := h (n + 1 : Int) (by omega)
      have hneg : f (-(n + 1 : Int)) = g (-(n + 1 : Int)) := h (-(n + 1 : Int)) (by omega)
      rw [hprev, hpos, hneg]

/--
@isnad1 id=eq.0h3v.s4.8f1f5187471e from=translated src=- shape=b3673c03 vocab=1f4171bf
-/
theorem bilateralSum_neg (f : Int → R) (n : Nat) :
    bilateralSum (fun j => f (-j)) n = bilateralSum f n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [bilateralSum_succ, bilateralSum_succ, ih]
      simp [add_comm]

/-! ### Gaussian (q-binomial) coefficients (Ch 3) -/

/-- Gaussian (q-binomial) coefficients, defined recursively as in Chapter 3.-/
def gaussianBinom (q : R) : Nat → Nat → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k =>
      gaussianBinom q n (Nat.succ k) + q ^ (n - k) * gaussianBinom q n k

/--
@isnad1 id=eq.0h3v.s5.25d761c0ad80 from=translated src=- shape=0fc5a075 vocab=2f82dd73
-/
@[simp] theorem gaussianBinom_zero_right (q : R) (n : Nat) : gaussianBinom q n 0 = 1 := by
  cases n <;> rfl

/--
@isnad1 id=eq.0h3v.s5.d616a10b4e33 from=translated src=- shape=d9fbf27c vocab=ce4d630c
-/
@[simp] theorem gaussianBinom_zero_left_succ (q : R) (k : Nat) :
    gaussianBinom q 0 (Nat.succ k) = 0 := rfl

end CommSemiring

end QseriesFormalization
