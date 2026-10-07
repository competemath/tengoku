/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Action.Pi
public import Tengoku.Seed.Algebra.Group.End
public import Tengoku.Seed.Algebra.Module.NatInt
public import Tengoku.Seed.Algebra.Order.Archimedean.Basic
import Tengoku.Seed.Algebra.Order.Group.Basic

/-!
# Maps (semi)conjugating a shift to a shift

Denote by $S^1$ the unit circle `UnitAddCircle`.
A common way to study a self-map $f\colon S^1\to S^1$ of degree `1`
is to lift it to a map $\tilde f\colon \mathbb R\to \mathbb R$
such that $\tilde f(x + 1) = \tilde f(x)+1$ for all `x`.

In this file we define a structure and a typeclass
for bundled maps satisfying `f (x + a) = f x + b`.

We use parameters `a` and `b` instead of `1` to accommodate for two use cases:

- maps between circles of different lengths;
- self-maps $f\colon S^1\to S^1$ of degree other than one,
  including orientation-reversing maps.
-/

@[expose] public section

assert_not_exists Finset

open Function Set

/-- A bundled map `f : G → H` such that `f (x + a) = f x + b` for all `x`,
denoted as `f : G →+c[a, b] H`.

One can think about `f` as a lift to `G` of a map between two `AddCircle`s. -/
structure AddConstMap (G H : Type*) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G → H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead. -/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b

@[inherit_doc]
scoped[AddConstMap] notation:25 G " →+c[" a ", " b "] " H => AddConstMap G H a b

/-- Typeclass for maps satisfying `f (x + a) = f x + b`.

Note that `a` and `b` are `outParam`s,
so one should not add instances like
`[AddConstMapClass F G H a b] : AddConstMapClass F G H (-a) (-b)`. -/
class AddConstMapClass (F : Type*) (G H : outParam Type*) [Add G] [Add H]
    (a : outParam G) (b : outParam H) [FunLike F G H] : Prop where
  /-- A map of `AddConstMapClass` class semiconjugates shift by `a` to the shift by `b`:
  `∀ x, f (x + a) = f x + b`. -/
  map_add_const (f : F) (x : G) : f (x + a) = f x + b

namespace AddConstMapClass

/-!
### Properties of `AddConstMapClass` maps

In this section we prove properties like `f (x + n • a) = f x + n • b`.
-/

scoped[AddConstMapClass] attribute [simp] map_add_const

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

/--
@isnad1 id=semiconj.0h6v.s6.95ca5393f4f3 from=seed src=0 shape=8767d678 vocab=c969a115
-/
protected theorem semiconj [Add G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    Semiconj f (· + a) (· + b) :=
  map_add_const f

/--
@isnad1 id=eq.0h8v.s6.3d03a542cade from=seed src=0 shape=8efa479f vocab=08f0d348
-/
@[scoped simp]
theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

/--
@isnad1 id=eq.0h7v.s6.cea2ff9e4320 from=seed src=0 shape=6836da2a vocab=939f1d6a
-/
@[scoped simp]
theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by simp [← map_add_nsmul]

/--
@isnad1 id=eq.0h6v.s6.a3de171a8933 from=seed src=0 shape=ab4a6b83 vocab=87421653
-/
theorem map_add_one [AddMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x + 1) = f x + b := map_add_const f x

/--
@isnad1 id=eq.0h7v.s7.642454ea4759 from=seed src=0 shape=c9583f13 vocab=4c543a84
-/
@[scoped simp]
theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : ℕ) • b :=
  map_add_nat' f x n

/--
@isnad1 id=eq.0h6v.s6.cab5ea7c9fc0 from=seed src=0 shape=f8d582fe vocab=69c141dc
-/
theorem map_add_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n := by simp

/--
@isnad1 id=eq.0h6v.s7.379546e37d22 from=seed src=0 shape=d256c30e vocab=bade7084
-/
theorem map_add_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + ofNat(n) := map_add_nat f x n

/--
@isnad1 id=eq.0h6v.s6.15bc2035cda7 from=seed src=0 shape=d477cd85 vocab=993e9b45
-/
@[scoped simp]
theorem map_const [AddZeroClass G] [Add H] [AddConstMapClass F G H a b] (f : F) :
    f a = f 0 + b := by
  simpa using map_add_const f 0

/--
@isnad1 id=eq.0h5v.s6.1147f72d555c from=seed src=0 shape=364ad0dd vocab=0811a30d
-/
theorem map_one [AddZeroClass G] [One G] [Add H] [AddConstMapClass F G H 1 b] (f : F) :
    f 1 = f 0 + b :=
  map_const f

/--
@isnad1 id=eq.0h7v.s6.f9ea0a326656 from=seed src=0 shape=722e8fb1 vocab=08f0d348
-/
@[scoped simp]
theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_nsmul f 0 n

/--
@isnad1 id=eq.0h6v.s6.aa0c92368ba8 from=seed src=0 shape=f8526ce5 vocab=939f1d6a
-/
@[scoped simp]
theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) : f n = f 0 + n • b := by
  simpa using map_add_nat' f 0 n

/--
@isnad1 id=eq.0h6v.s6.c300d6b5f3d2 from=seed src=0 shape=04b557ca vocab=4c543a84
-/
theorem map_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f (ofNat(n)) = f 0 + (ofNat(n) : ℕ) • b :=
  map_nat' f n

/--
@isnad1 id=eq.0h5v.s6.db83b7c7676c from=seed src=0 shape=aac66ce2 vocab=69c141dc
-/
theorem map_nat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) : f n = f 0 + n := by simp

/--
@isnad1 id=eq.0h5v.s6.f9425ea4fbfd from=seed src=0 shape=387f0121 vocab=bade7084
-/
theorem map_ofNat [AddMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] :
    f ofNat(n) = f 0 + ofNat(n) := map_nat f n

/--
@isnad1 id=eq.0h7v.s6.9f2bb6a91c07 from=seed src=0 shape=29a94316 vocab=3677bc81
-/
@[scoped simp]
theorem map_const_add [AddCommMagma G] [Add H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (a + x) = f x + b := by
  rw [add_comm, map_add_const]

/--
@isnad1 id=eq.0h6v.s6.3ab3b6009b95 from=seed src=0 shape=f3e13481 vocab=e74db809
-/
theorem map_one_add [AddCommMonoidWithOne G] [Add H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (1 + x) = f x + b := map_const_add f x

/--
@isnad1 id=eq.0h8v.s6.5c43a52e9e8c from=seed src=0 shape=4a8ad7b6 vocab=0b402079
-/
@[scoped simp]
theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_nsmul]

/--
@isnad1 id=eq.0h7v.s6.525cead0f21e from=seed src=0 shape=62402349 vocab=3fb566b6
-/
@[scoped simp]
theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using map_nsmul_add f n x

/--
@isnad1 id=eq.0h7v.s7.b14fac5e39aa from=seed src=0 shape=73bace03 vocab=4f9b2d60
-/
theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b :=
  map_nat_add' f n x

/--
@isnad1 id=eq.0h6v.s6.815993ccb180 from=seed src=0 shape=51ad6d08 vocab=3c640778
-/
theorem map_nat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n := by simp

/--
@isnad1 id=eq.0h6v.s7.6ea7abfd30c5 from=seed src=0 shape=1042febd vocab=64b5b8b6
-/
theorem map_ofNat_add [AddCommMonoidWithOne G] [AddMonoidWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) :=
  map_nat_add f n x

/--
@isnad1 id=eq.0h8v.s7.3dea0f5b9871 from=seed src=0 shape=8efa479f vocab=324d7d89
-/
@[scoped simp]
theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), map_add_nsmul, add_sub_cancel_right]

/--
@isnad1 id=eq.0h7v.s6.33f8ef709879 from=seed src=0 shape=0346c2f8 vocab=dda6e6ee
-/
@[scoped simp]
theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using map_sub_nsmul f x 1

/--
@isnad1 id=eq.0h6v.s6.08270d7e9a8a from=seed src=0 shape=13d82bf2 vocab=303e4891
-/
theorem map_sub_one [AddGroup G] [One G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) : f (x - 1) = f x - b :=
  map_sub_const f x

/--
@isnad1 id=eq.0h7v.s7.6f15eecaa9bf from=seed src=0 shape=6836da2a vocab=34b20650
-/
@[scoped simp]
theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using map_sub_nsmul f x n

/--
@isnad1 id=eq.0h7v.s7.7eec1b31c6a6 from=seed src=0 shape=c9583f13 vocab=e9130553
-/
@[scoped simp]
theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b :=
  map_sub_nat' f x n

/--
@isnad1 id=eq.0h8v.s7.79a0347c795d from=seed src=0 shape=8efa479f vocab=f1d9f57b
-/
@[scoped simp]
theorem map_add_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : ∀ n : ℤ, f (x + n • a) = f x + n • b
  | (n : ℕ) => by simp
  | .negSucc n => by simp [← sub_eq_add_neg]

/--
@isnad1 id=eq.0h7v.s7.00032a5ebf93 from=seed src=0 shape=722e8fb1 vocab=f1d9f57b
-/
@[scoped simp]
theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  simpa using map_add_zsmul f 0 n

/--
@isnad1 id=eq.0h7v.s7.c79510936e8d from=seed src=0 shape=6836da2a vocab=bcc061a6
-/
@[scoped simp]
theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  rw [← map_add_zsmul f x n, zsmul_one]

/--
@isnad1 id=eq.0h6v.s7.755cc4683434 from=seed src=0 shape=f8d582fe vocab=544a46dc
-/
theorem map_add_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n := by simp

/--
@isnad1 id=eq.0h8v.s6.8e70e21cafef from=seed src=0 shape=8efa479f vocab=61cbe227
-/
@[scoped simp]
theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using map_add_zsmul f x (-n)

/--
@isnad1 id=eq.0h7v.s6.31965085aba3 from=seed src=0 shape=6836da2a vocab=2f581a40
-/
@[scoped simp]
theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  rw [← map_sub_zsmul, zsmul_one]

/--
@isnad1 id=eq.0h6v.s6.4644c4271691 from=seed src=0 shape=f8d582fe vocab=a6ca6ea8
-/
theorem map_sub_int [AddGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n := by simp

/--
@isnad1 id=eq.0h8v.s7.1aed0f2a5ec9 from=seed src=0 shape=4a8ad7b6 vocab=4ccfbbf1
-/
@[scoped simp]
theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, map_add_zsmul]

/--
@isnad1 id=eq.0h7v.s7.ffefbf6e0378 from=seed src=0 shape=62402349 vocab=6de97311
-/
@[scoped simp]
theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← map_zsmul_add, zsmul_one]

/--
@isnad1 id=eq.0h6v.s7.6a330655d485 from=seed src=0 shape=51ad6d08 vocab=ceca0df0
-/
theorem map_int_add [AddCommGroupWithOne G] [AddGroupWithOne H] [AddConstMapClass F G H 1 1]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n := by simp

/--
@isnad1 id=eq.0h6v.s6.f14d7b02f98c from=seed src=0 shape=4d06f87f vocab=cb3a4f8f
-/
theorem map_fract {R : Type*} [Ring R] [LinearOrder R] [FloorRing R] [AddGroup H]
    [FunLike F R H] [AddConstMapClass F R H 1 b] (f : F) (x : R) :
    f (Int.fract x) = f x - ⌊x⌋ • b :=
  map_sub_int' ..

open scoped Relator in
/-- Auxiliary lemmas for the "monotonicity on a fundamental interval implies monotonicity" lemmas.
We formulate it for any relation so that the proof works both for `Monotone` and `StrictMono`.
@isnad1 id=liftfun.1h9v.s8.33e60599bdda from=seed src=0 shape=89749bb2 vocab=ce80ba07
-/
protected theorem rel_map_of_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Archimedean G] [AddGroup H]
    [AddConstMapClass F G H a b] {f : F} {R : H → H → Prop} [IsTrans H R]
    [hR : CovariantClass H H (fun x y ↦ y + x) R] (ha : 0 < a) {l : G}
    (hf : ∀ x ∈ Icc l (l + a), ∀ y ∈ Icc l (l + a), x < y → R (f x) (f y)) :
    ((· < ·) ⇒ R) f f := fun x y hxy ↦ by
  replace hR := hR.elim
  have ha' : 0 ≤ a := ha.le
  -- Shift both points by `m • a` so that `l ≤ x < l + a`
  wlog hx : x ∈ Ico l (l + a) generalizing x y
  · rcases existsUnique_sub_zsmul_mem_Ico ha x l with ⟨m, hm, -⟩
    suffices R (f (x - m • a)) (f (y - m • a)) by simpa using hR (m • b) this
    exact this _ _ (by simpa) hm
  · -- Now find `n` such that `l + n • a < y ≤ l + (n + 1) • a`
    rcases existsUnique_sub_zsmul_mem_Ioc ha y l with ⟨n, hny, -⟩
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · -- Since `l ≤ x ≤ y`, the case `n < 0` is impossible
      refine absurd ?_ hxy.not_ge
      calc
        y ≤ l + a + n • a := sub_le_iff_le_add.1 hny.2
        _ = l + (n + 1) • a := by rw [add_comm n, add_smul, one_smul, add_assoc]
        _ ≤ l + (0 : ℤ) • a := by gcongr; lia
        _ ≤ x := by simpa using hx.1
    · -- If `n = 0`, then `l < y ≤ l + a`, hence we can apply the assumption
      exact hf x (Ico_subset_Icc_self hx) y (by simpa using Ioc_subset_Icc_self hny) hxy
    · -- In the remaining case `0 < n` we use transitivity.
      -- If `R = (· < ·)`, then the proof looks like
      -- `f x < f (l + a) ≤ f (l + n • a) < f y`
      trans f (l + (1 : ℤ) • a)
      · grind
      have hy : R (f (l + n • a)) (f y) := by
        rw [← sub_add_cancel y (n • a), map_add_zsmul, map_add_zsmul]
        refine hR _ <| hf _ ?_ _ (Ioc_subset_Icc_self hny) hny.1; simpa
      rw [← Int.add_one_le_iff, zero_add] at hn
      rcases hn.eq_or_lt with rfl | hn; · assumption
      trans f (l + n • a)
      · refine Int.rel_of_forall_rel_succ_of_lt R (f := (f <| l + · • a)) (fun k ↦ ?_) hn
        simp_rw [add_comm k 1, add_zsmul, ← add_assoc, one_zsmul, map_add_zsmul]
        refine hR (k • b) (hf _ ?_ _ ?_ ?_) <;> simpa
      · assumption

/--
@isnad1 id=iff.1h7v.s7.09edf67c3c90 from=seed src=0 shape=db296098 vocab=01929b83
-/
theorem monotone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Monotone f ↔ MonotoneOn f (Icc l (l + a)) :=
  ⟨(Monotone.monotoneOn · _), fun hf ↦ monotone_iff_forall_lt.2 <|
    AddConstMapClass.rel_map_of_Icc ha fun _x hx _y hy hxy ↦ hf hx hy hxy.le⟩

/--
@isnad1 id=iff.1h7v.s7.83dedd52e16c from=seed src=0 shape=db296098 vocab=a4e182e2
-/
theorem antitone_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    Antitone f ↔ AntitoneOn f (Icc l (l + a)) :=
  monotone_iff_Icc (H := Hᵒᵈ) ha l

/--
@isnad1 id=iff.1h7v.s7.6cdfb5fda410 from=seed src=0 shape=db296098 vocab=86bf8a76
-/
theorem strictMono_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictMono f ↔ StrictMonoOn f (Icc l (l + a)) :=
  ⟨(StrictMono.strictMonoOn · _), AddConstMapClass.rel_map_of_Icc ha⟩

/--
@isnad1 id=iff.1h7v.s7.83666d5b95c1 from=seed src=0 shape=db296098 vocab=d1b38a9d
-/
theorem strictAnti_iff_Icc [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G]
    [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]
    [AddConstMapClass F G H a b] {f : F} (ha : 0 < a) (l : G) :
    StrictAnti f ↔ StrictAntiOn f (Icc l (l + a)) :=
  strictMono_iff_Icc (H := Hᵒᵈ) ha l

end AddConstMapClass

open AddConstMapClass

namespace AddConstMap

section Add

variable {G H : Type*} [Add G] [Add H] {a : G} {b : H}

/-!
### Coercion to function
-/

instance : FunLike (G →+c[a, b] H) G H where
  coe := AddConstMap.toFun
  coe_injective | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
@isnad1 id=eq.1h5v.s6.f793ceb7aa89 from=seed src=0 shape=e9fb7b11 vocab=8f35b46b
-/
@[simp, push_cast] theorem coe_mk (f : G → H) (hf) : ⇑(mk f hf : G →+c[a, b] H) = f := rfl
/--
@isnad1 id=eq.0h5v.s5.c4672870ceb8 from=seed src=0 shape=eba702ef vocab=e5485896
-/
@[simp] theorem mk_coe (f : G →+c[a, b] H) : mk f f.2 = f := rfl
/--
@isnad1 id=eq.0h5v.s5.9b4cc7fe4a1d from=seed src=0 shape=e7e787f4 vocab=35a5877d
-/
@[simp] theorem toFun_eq_coe (f : G →+c[a, b] H) : f.toFun = f := rfl

instance : AddConstMapClass (G →+c[a, b] H) G H a b where
  map_add_const f := f.map_add_const'

/--
@isnad1 id=eq.1h6v.s6.f8037268f1cf from=seed src=0 shape=0d965dfb vocab=e2b182e1
-/
@[ext] protected theorem ext {f g : G →+c[a, b] H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

initialize_simps_projections AddConstMap (toFun → coe, as_prefix coe)

/-!
### Constructions about `G →+c[a, b] H`
-/

/-- The identity map as `G →+c[a, a] G`. -/
@[simps -fullyApplied]
protected def id : G →+c[a, a] G := ⟨id, fun _ ↦ rfl⟩

instance : Inhabited (G →+c[a, a] G) := ⟨.id⟩

/-- Composition of two `AddConstMap`s. -/
@[simps -fullyApplied]
def comp {K : Type*} [Add K] {c : K} (g : H →+c[b, c] K) (f : G →+c[a, b] H) :
    G →+c[a, c] K :=
  ⟨g ∘ f, by simp⟩

/--
@isnad1 id=eq.0h5v.s5.cf09be723c88 from=seed src=0 shape=fa9f23c0 vocab=79111a04
-/
@[simp] theorem comp_id (f : G →+c[a, b] H) : f.comp .id = f := rfl
/--
@isnad1 id=eq.0h5v.s5.4d4088ede5a6 from=seed src=0 shape=9dab73a1 vocab=79111a04
-/
@[simp] theorem id_comp (f : G →+c[a, b] H) : .comp .id f = f := rfl

/-- Change constants `a` and `b` in `(f : G →+c[a, b] H)` to improve definitional equalities. -/
@[simps -fullyApplied]
def replaceConsts (f : G →+c[a, b] H) (a' b') (ha : a = a') (hb : b = b') :
    G →+c[a', b'] H where
  toFun := f
  map_add_const' := ha ▸ hb ▸ f.map_add_const'

/-!
### Additive action on `G →+c[a, b] H`
-/

/-- If `f` is an `AddConstMap`, then so is `(c +ᵥ f ·)`. -/
instance {K : Type*} [VAdd K H] [VAddAssocClass K H H] : VAdd K (G →+c[a, b] H) :=
  ⟨fun c f ↦ ⟨c +ᵥ ⇑f, fun x ↦ by simp [vadd_add_assoc]⟩⟩

/--
@isnad1 id=eq.0h7v.s7.b795f190aeaa from=seed src=0 shape=655d2d21 vocab=31fd64ae
-/
@[simp, norm_cast]
theorem coe_vadd {K : Type*} [VAdd K H] [VAddAssocClass K H H] (c : K) (f : G →+c[a, b] H) :
    ⇑(c +ᵥ f) = c +ᵥ ⇑f :=
  rfl

instance {K : Type*} [AddMonoid K] [AddAction K H] [VAddAssocClass K H H] :
    AddAction K (G →+c[a, b] H) :=
  DFunLike.coe_injective.addAction _ coe_vadd

/-!
### Monoid structure on endomorphisms `G →+c[a, a] G`
-/

instance : Mul (G →+c[a, a] G) := ⟨comp⟩
instance : One (G →+c[a, a] G) := ⟨.id⟩

instance : Pow (G →+c[a, a] G) ℕ where
  pow f n := ⟨f^[n], Commute.iterate_left (AddConstMapClass.semiconj f) _⟩

instance : Monoid (G →+c[a, a] G) :=
  DFunLike.coe_injective.monoid (M₂ := Function.End G) _ rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/--
@isnad1 id=eq.0h4v.s6.da6e6686579a from=seed src=0 shape=4443cf00 vocab=a6430e66
-/
theorem mul_def (f g : G →+c[a, a] G) : f * g = f.comp g := rfl
/--
@isnad1 id=eq.0h4v.s6.b72bbb072e14 from=seed src=0 shape=f3e0ea1f vocab=cdb18557
-/
@[simp, push_cast] theorem coe_mul (f g : G →+c[a, a] G) : ⇑(f * g) = f ∘ g := rfl

/--
@isnad1 id=eq.0h2v.s5.4063973e6f6b from=seed src=0 shape=0ea8b436 vocab=eedeabff
-/
theorem one_def : (1 : G →+c[a, a] G) = .id := rfl
/--
@isnad1 id=eq.0h2v.s5.bc18e07489b4 from=seed src=0 shape=7d80a93f vocab=15bd6658
-/
@[simp, push_cast] theorem coe_one : ⇑(1 : G →+c[a, a] G) = id := rfl

/--
@isnad1 id=eq.0h4v.s6.2a14d50eb8d0 from=seed src=0 shape=8f7dea27 vocab=3569342a
-/
@[simp, push_cast] theorem coe_pow (f : G →+c[a, a] G) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

/--
@isnad1 id=eq.0h5v.s6.adfb6b36346e from=seed src=0 shape=f6dce976 vocab=3569342a
-/
theorem pow_apply (f : G →+c[a, a] G) (n : ℕ) (x : G) : (f ^ n) x = f^[n] x := rfl

/-- Coercion to functions as a monoid homomorphism to `Function.End G`. -/
@[simps -fullyApplied]
def toEnd : (G →+c[a, a] G) →* Function.End G where
  toFun := DFunLike.coe
  map_mul' _ _ := rfl
  map_one' := rfl

end Add

section AddZeroClass

variable {G H K : Type*} [Add G] [AddZeroClass H] {a : G} {b : H}

/-!
### Multiplicative action on `(b : H) × (G →+c[a, b] H)`

If `K` acts distributively on `H`, then for each `f : G →+c[a, b] H`
we define `(AddConstMap.smul c f : G →+c[a, c • b] H)`.

One can show that this defines a multiplicative action of `K` on `(b : H) × (G →+c[a, b] H)`
but we don't do this at the moment because we don't need this.
-/

/-- Pointwise scalar multiplication of `f : G →+c[a, b] H` as a map `G →+c[a, c • b] H`. -/
@[simps -fullyApplied]
def smul [DistribSMul K H] (c : K) (f : G →+c[a, b] H) : G →+c[a, c • b] H where
  toFun := c • ⇑f
  map_add_const' x := by simp [smul_add]

end AddZeroClass

section AddMonoid

variable {G : Type*} [AddMonoid G] {a : G}

/-- The map that sends `c` to a translation by `c`
as a monoid homomorphism from `Multiplicative G` to `G →+c[a, a] G`. -/
@[simps! -fullyApplied]
def addLeftHom : Multiplicative G →* (G →+c[a, a] G) where
  toFun c := c.toAdd +ᵥ .id
  map_one' := by ext; apply zero_add
  map_mul' _ _ := by ext; apply add_assoc

end AddMonoid

section AddCommGroup

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {a : G} {b : H}

/-- If `f : G → H` is an `AddConstMap`, then so is `fun x ↦ -f (-x)`. -/
@[simps! apply_coe]
def conjNeg : (G →+c[a, b] H) ≃ (G →+c[a, b] H) :=
  Involutive.toPerm (fun f ↦ ⟨fun x ↦ - f (-x), fun _ ↦ by simp [neg_add_eq_sub]⟩) fun _ ↦
    AddConstMap.ext fun _ ↦ by simp

/--
@isnad1 id=eq.0h4v.s6.f0f4d010c88a from=seed src=0 shape=b4b73d03 vocab=ccc1a7a7
-/
@[simp] theorem conjNeg_symm : (conjNeg (a := a) (b := b)).symm = conjNeg := rfl

end AddCommGroup

section FloorRing

variable {R G : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] [AddGroup G]
  (a : G)

/-- A map `f : R →+c[1, a] G` is defined by its values on `Set.Ico 0 1`. -/
def mkFract : (Ico (0 : R) 1 → G) ≃ (R →+c[1, a] G) where
  toFun f := ⟨fun x ↦ f ⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩ + ⌊x⌋ • a, fun x ↦ by
    simp [add_one_zsmul, add_assoc]⟩
  invFun f x := f x
  left_inv _ := by ext x; simp [Int.fract_eq_self.2 x.2, Int.floor_eq_zero_iff.2 x.2]
  right_inv f := by ext x; simp [map_fract]

end FloorRing

end AddConstMap
