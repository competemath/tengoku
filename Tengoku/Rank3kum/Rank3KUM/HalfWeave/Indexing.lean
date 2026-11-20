import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Rank3KUM.HalfWeave

/-- When `k = 0` there are no cyclic positions.
@isnad1 id=not.0h0v.s3.5130d5b01bbb from=translated src=- shape=375783c1 vocab=33b9c383
-/
theorem no_positions_when_k_zero :
    ¬ Nonempty (Fin 0 × Bool) := by
  rintro ⟨p⟩
  exact Fin.elim0 p.1

/-- The first-half index `y_i`, regarded as an index in `Fin (2k)`.-/
def firstIndex (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨i.val, by omega⟩

/-- The second-half index `y_(k+i)`, regarded as an index in `Fin (2k)`.-/
def secondIndex (k : ℕ) (i : Fin k) : Fin (2 * k) :=
  ⟨k + i.val, by omega⟩

/--
@isnad1 id=eq.0h2v.s4.e78253aa0d2d from=translated src=- shape=20839efd vocab=6e6d9206
-/
@[simp] theorem firstIndex_val
    (k : ℕ) (i : Fin k) :
    (firstIndex k i).val = i.val := by
  rfl

/--
@isnad1 id=eq.0h2v.s5.084abae5ded0 from=translated src=- shape=34752e8d vocab=da4c3fcb
-/
@[simp] theorem secondIndex_val
    (k : ℕ) (i : Fin k) :
    (secondIndex k i).val = k + i.val := by
  rfl

/-- Split a Boolean-labelled copy of `Fin k` into two summands.-/
def boolHalfEquiv (k : ℕ) :
    Fin k × Bool ≃ Fin k ⊕ Fin k where
  toFun
    | (i, false) => Sum.inl i
    | (i, true) => Sum.inr i
  invFun
    | Sum.inl i => (i, false)
    | Sum.inr i => (i, true)
  left_inv := by
    rintro ⟨i, b⟩
    cases b <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

/--
The explicit equivalence implementing
`y₀, y_k, y₁, y_(k+1), ..., y_(k-1), y_(2k-1)`.-/
def halfWeaveEquiv (k : ℕ) (_hk : 0 < k) :
    Fin k × Bool ≃ Fin (2 * k) :=
  (boolHalfEquiv k).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

/--
@isnad1 id=eq.1h2v.s7.ed21a1f2d4ec from=translated src=- shape=fbb2c8a8 vocab=321f4f11
-/
@[simp] theorem halfWeaveEquiv_false
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    halfWeaveEquiv k hk (i, false) =
      firstIndex k i := by
  apply Fin.ext
  simp [halfWeaveEquiv, boolHalfEquiv, firstIndex]

/--
@isnad1 id=eq.1h2v.s7.37c2c16fe37f from=translated src=- shape=fbb2c8a8 vocab=e98d5b87
-/
@[simp] theorem halfWeaveEquiv_true
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    halfWeaveEquiv k hk (i, true) =
      secondIndex k i := by
  apply Fin.ext
  simp [halfWeaveEquiv, boolHalfEquiv, secondIndex]
  omega

/-- Cyclic addition by one on `Fin k`.-/
def cyclicSuccEquiv (k : ℕ) (hk : 0 < k) :
    Fin k ≃ Fin k :=
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  Equiv.addRight 1

def cyclicSucc (k : ℕ) (hk : 0 < k)
    (i : Fin k) : Fin k :=
  cyclicSuccEquiv k hk i

/--
@isnad1 id=eq.1h2v.s5.f78ac78cdb2a from=translated src=- shape=8be2a821 vocab=9dac5844
-/
@[simp] theorem cyclicSucc_val
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (cyclicSucc k hk i).val =
      (i.val + 1) % k := by
  simp [cyclicSucc, cyclicSuccEquiv, Fin.add_def]

/--
@isnad1 id=bijectiv.1h1v.s4.f179324b49fc from=translated src=- shape=63f8cf57 vocab=f14052a3
-/
theorem cyclicSucc_bijective
    (k : ℕ) (hk : 0 < k) :
    Function.Bijective (cyclicSucc k hk) :=
  (cyclicSuccEquiv k hk).bijective

def lastFin (k : ℕ) (hk : 0 < k) : Fin k :=
  ⟨k - 1, by omega⟩

def zeroFin (k : ℕ) (hk : 0 < k) : Fin k :=
  ⟨0, hk⟩

/-- The cyclic successor of `k-1` is explicitly zero.
@isnad1 id=eq.1h1v.s4.d93b3c4b1916 from=translated src=- shape=09eb948d vocab=0a6f3f07
-/
@[simp] theorem cyclicSucc_last
    (k : ℕ) (hk : 0 < k) :
    cyclicSucc k hk (lastFin k hk) =
      zeroFin k hk := by
  apply Fin.ext
  simp [lastFin, zeroFin,
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hk)]

/-- Alternate within a pair, then advance cyclically to the next pair.-/
def weaveNext (k : ℕ) (hk : 0 < k) :
    Fin k × Bool → Fin k × Bool
  | (i, false) => (i, true)
  | (i, true) => (cyclicSucc k hk i, false)

/--
@isnad1 id=eq.1h2v.s5.ee5b9a4575e1 from=translated src=- shape=badbd5a7 vocab=dbae6ceb
-/
@[simp] theorem weaveNext_false
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    weaveNext k hk (i, false) = (i, true) := by
  rfl

/--
@isnad1 id=eq.1h2v.s5.6ac5e98fec7c from=translated src=- shape=7143f446 vocab=ad85e58d
-/
@[simp] theorem weaveNext_true
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    weaveNext k hk (i, true) =
      (cyclicSucc k hk i, false) := by
  rfl

/--
@isnad1 id=bijectiv.1h1v.s4.aabe7cc76ab1 from=translated src=- shape=8222235d vocab=b93c0b7c
-/
theorem weaveNext_bijective
    (k : ℕ) (hk : 0 < k) :
    Function.Bijective (weaveNext k hk) := by
  constructor
  · rintro ⟨i, b⟩ ⟨j, c⟩ h
    cases b <;> cases c
    · have hij : i = j := congrArg Prod.fst h
      subst j
      rfl
    · simp at h
    · simp at h
    · have hs :
          cyclicSucc k hk i = cyclicSucc k hk j :=
        congrArg Prod.fst h
      have hij : i = j :=
        (cyclicSucc_bijective k hk).1 hs
      subst j
      rfl
  · rintro ⟨i, b⟩
    cases b
    · obtain ⟨j, hj⟩ :=
        (cyclicSucc_bijective k hk).2 i
      exact ⟨(j, true), by simp [hj]⟩
    · exact ⟨(i, false), by simp⟩

/-- Advance the `Fin k` coordinate cyclically `n` times.-/
def cyclicAdvance
    (k : ℕ) (hk : 0 < k)
    (n : ℕ) (i : Fin k) : Fin k :=
  ((cyclicSucc k hk)^[n]) i

/-- Every even iterate returns to the first half.
@isnad1 id=eq.1h3v.s5.cc6f799fa23d from=translated src=- shape=13258770 vocab=7390433d
-/
theorem weaveNext_iterate_even
    (k : ℕ) (hk : 0 < k)
    (n : ℕ) (i : Fin k) :
    ((weaveNext k hk)^[2 * n]) (i, false) =
      (cyclicAdvance k hk n i, false) := by
  induction n generalizing i with
  | zero =>
      simp [cyclicAdvance]
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      rw [Function.iterate_add_apply]
      have htwo :
          ((weaveNext k hk)^[2]) (i, false) =
            (cyclicSucc k hk i, false) := by
        simp [Function.iterate_succ_apply]
      rw [htwo, ih]
      simp [cyclicAdvance, Function.iterate_succ_apply]

/-- Every odd iterate lies in the corresponding second-half position.
@isnad1 id=eq.1h3v.s6.1c4e62ca89a6 from=translated src=- shape=39f36adf vocab=f46124e9
-/
theorem weaveNext_iterate_odd
    (k : ℕ) (hk : 0 < k)
    (n : ℕ) (i : Fin k) :
    ((weaveNext k hk)^[2 * n + 1]) (i, false) =
      (cyclicAdvance k hk n i, true) := by
  rw [show 2 * n + 1 = 1 + 2 * n by omega]
  rw [Function.iterate_add_apply]
  rw [weaveNext_iterate_even]
  simp

/-- A first-half successor is exactly the index pair `(i, k+i)`.
@isnad1 id=eq.1h2v.s8.637f674b42cb from=translated src=- shape=fe06967a vocab=8586cb25
-/
theorem halfWeave_successor_false
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (halfWeaveEquiv k hk (i, false),
     halfWeaveEquiv k hk
       (weaveNext k hk (i, false))) =
    (firstIndex k i, secondIndex k i) := by
  simp

/-- A second-half successor is exactly `(k+i, i+1 mod k)`.
@isnad1 id=eq.1h2v.s8.d1d4143f8a4d from=translated src=- shape=a2451a30 vocab=f625f6e5
-/
theorem halfWeave_successor_true
    (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (halfWeaveEquiv k hk (i, true),
     halfWeaveEquiv k hk
       (weaveNext k hk (i, true))) =
    (secondIndex k i,
     firstIndex k (cyclicSucc k hk i)) := by
  simp

/-- The final second-half index wraps explicitly to first-half index zero.
@isnad1 id=eq.1h1v.s8.95bbc065fa0f from=translated src=- shape=4da3d36b vocab=02dc66df
-/
theorem halfWeave_successor_wraparound
    (k : ℕ) (hk : 0 < k) :
    (halfWeaveEquiv k hk (lastFin k hk, true),
     halfWeaveEquiv k hk
       (weaveNext k hk (lastFin k hk, true))) =
    (secondIndex k (lastFin k hk),
     firstIndex k (zeroFin k hk)) := by
  simp

/-- Transport an arbitrary enumeration through the half weave.-/
def woven {α : Type*}
    (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α) :
    Fin k × Bool ≃ α :=
  (halfWeaveEquiv k hk).trans y

/--
@isnad1 id=eq.1h4v.s7.1eb6114db7ee from=translated src=- shape=7e5e6f78 vocab=621fb4b1
-/
@[simp] theorem woven_false
    {α : Type*}
    (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α)
    (i : Fin k) :
    woven k hk y (i, false) =
      y (firstIndex k i) := by
  simp [woven]

/--
@isnad1 id=eq.1h4v.s7.c6a4210a8f70 from=translated src=- shape=7e5e6f78 vocab=5d7f8ce7
-/
@[simp] theorem woven_true
    {α : Type*}
    (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α)
    (i : Fin k) :
    woven k hk y (i, true) =
      y (secondIndex k i) := by
  simp [woven]

/-- The final woven adjacency also wraps explicitly to `y_0`.
@isnad1 id=eq.1h3v.s8.ee2c18a0f7b7 from=translated src=- shape=6c0447d8 vocab=ea6f2c0d
-/
theorem woven_successor_wraparound
    {α : Type*}
    (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α) :
    (woven k hk y (lastFin k hk, true),
     woven k hk y
       (weaveNext k hk (lastFin k hk, true))) =
    (y (secondIndex k (lastFin k hk)),
     y (firstIndex k (zeroFin k hk))) := by
  simp

/--
Every successor adjacency is either `y_i,y_(k+i)` or
`y_(k+i),y_(i+1 mod k)`.
@isnad1 id=or.1h4v.s9.70f2b1b16385 from=translated src=- shape=d4c0bc45 vocab=0478f8eb
-/
theorem woven_successor_adjacency
    {α : Type*}
    (k : ℕ) (hk : 0 < k)
    (y : Fin (2 * k) ≃ α)
    (p : Fin k × Bool) :
    (∃ i : Fin k,
        p = (i, false) ∧
        (woven k hk y p,
         woven k hk y (weaveNext k hk p)) =
        (y (firstIndex k i),
         y (secondIndex k i))) ∨
    (∃ i : Fin k,
        p = (i, true) ∧
        (woven k hk y p,
         woven k hk y (weaveNext k hk p)) =
        (y (secondIndex k i),
         y (firstIndex k (cyclicSucc k hk i)))) := by
  rcases p with ⟨i, b⟩
  cases b
  · left
    exact ⟨i, rfl, by simp⟩
  · right
    exact ⟨i, rfl, by simp⟩

end Rank3KUM.HalfWeave
