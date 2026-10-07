/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
public import Tengoku.Seed.Data.ZMod.Basic

/-!
# Congruence modulo natural and integer numbers for big operators

In this file we prove various versions of the following theorem:
if `f i ≡ g i [MOD n]` for all `i ∈ s`, then `∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD n]`,
and similarly for sums.

We prove it for lists, multisets, and finsets, as well as for natural and integer numbers.
-/

public section

namespace Nat

variable {α : Type*} {n : ℕ} {l : List α} {f g : α → ℕ}

namespace ModEq

/--
@isnad1 id=modeq.1h5v.s5.d41790878ba3 from=seed src=0 shape=6dc551b1 vocab=9bb9e6dd
-/
theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

/--
@isnad1 id=modeq.1h4v.s5.d202fddfbc0b from=seed src=0 shape=b944b737 vocab=9bb9e6dd
-/
theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] :=
  (listProd_map h).trans <| by simp [ModEq.refl]

/--
@isnad1 id=modeq.1h2v.s5.afa2b1b419e3 from=seed src=0 shape=e9914ad8 vocab=eb02cc64
-/
theorem listProd_one {l : List ℕ} (h : ∀ x ∈ l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using listProd_map_one h

/--
@isnad1 id=modeq.1h5v.s5.aa17f56c659e from=seed src=0 shape=6dc551b1 vocab=44285d33
-/
theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

/--
@isnad1 id=modeq.1h4v.s5.97f348ffb1a8 from=seed src=0 shape=b944b737 vocab=44285d33
-/
theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

/--
@isnad1 id=modeq.1h2v.s5.0079cdd1b780 from=seed src=0 shape=e9914ad8 vocab=15691411
-/
theorem listSum_zero {l : List ℕ} (h : ∀ x ∈ l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

/--
@isnad1 id=modeq.1h5v.s5.73367451431e from=seed src=0 shape=517a379f vocab=0189d33e
-/
theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

/--
@isnad1 id=modeq.1h4v.s5.2be1a0c2a778 from=seed src=0 shape=20dd0437 vocab=0189d33e
-/
theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map h

/--
@isnad1 id=modeq.1h2v.s5.9165f9e3f315 from=seed src=0 shape=e9914ad8 vocab=ce835dbc
-/
theorem multisetProd_one {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map_one h

/--
@isnad1 id=modeq.1h5v.s5.d3c1f8cecd9f from=seed src=0 shape=517a379f vocab=3a3bce61
-/
theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

/--
@isnad1 id=modeq.1h4v.s5.0846e52ce179 from=seed src=0 shape=20dd0437 vocab=3a3bce61
-/
theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

/--
@isnad1 id=modeq.1h2v.s5.53181181f171 from=seed src=0 shape=e9914ad8 vocab=ac36b04f
-/
theorem multisetSum_zero {s : Multiset ℕ} (h : ∀ x ∈ s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

/--
@isnad1 id=modeq.1h5v.s5.42089dc2836e from=seed src=0 shape=fd08eb72 vocab=6b47c1b6
-/
@[gcongr]
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [MOD n] :=
  .multisetProd_map (s := s.1) h

/--
@isnad1 id=modeq.1h4v.s5.6494cac2a81c from=seed src=0 shape=ba998a66 vocab=6b47c1b6
-/
theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [MOD n]) : ∏ x ∈ s, f x ≡ 1 [MOD n] := by
  simpa using ModEq.prod h

/--
@isnad1 id=modeq.1h5v.s5.0915cbcac0db from=seed src=0 shape=fd08eb72 vocab=88d146c4
-/
@[gcongr]
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [MOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [MOD n] :=
  .multisetSum_map (s := s.1) h

/--
@isnad1 id=modeq.1h4v.s5.240c4173d49a from=seed src=0 shape=ba998a66 vocab=88d146c4
-/
theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [MOD n]) : ∑ x ∈ s, f x ≡ 0 [MOD n] := by
  simpa using ModEq.sum h

end ModEq

/--
@isnad1 id=modeq.1h5v.s6.ac13e9d4df3c from=seed src=0 shape=f37f019f vocab=c3a81445
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

/--
@isnad1 id=modeq.2h5v.s6.a4ab85bd01aa from=seed src=0 shape=423b774f vocab=6b47c1b6
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [MOD n]) :
    (∏ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

/--
@isnad1 id=modeq.1h5v.s6.ec17eac9c226 from=seed src=0 shape=f37f019f vocab=e5698f1d
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

/--
@isnad1 id=modeq.2h5v.s6.e483087fffa2 from=seed src=0 shape=423b774f vocab=88d146c4
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [MOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [MOD n]) :
    (∑ x ∈ s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Nat

namespace Int

variable {α : Type*} {n : ℤ} {l : List α} {f g : α → ℤ}

namespace ModEq

/--
@isnad1 id=modeq.1h5v.s6.f60c8588d7f1 from=seed src=0 shape=6dc551b1 vocab=b54137f0
-/
theorem listProd_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) :
    (l.map f).prod ≡ (l.map g).prod [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

/--
@isnad1 id=modeq.1h4v.s5.ffefdf37a9ba from=seed src=0 shape=b944b737 vocab=b54137f0
-/
theorem listProd_map_one (h : ∀ x ∈ l, f x ≡ 1 [ZMOD n]) : (l.map f).prod ≡ 1 [ZMOD n] :=
  (listProd_map h).trans <| by simp

/--
@isnad1 id=modeq.1h2v.s5.3c8cbe02f694 from=seed src=0 shape=e9914ad8 vocab=bf93513a
-/
theorem listProd_one {l : List ℤ} (h : ∀ x ∈ l, x ≡ 1 [ZMOD n]) : l.prod ≡ 1 [ZMOD n] := by
  simpa using listProd_map_one h

/--
@isnad1 id=modeq.1h5v.s5.d147e84bb4c5 from=seed src=0 shape=6dc551b1 vocab=751d09b6
-/
theorem listSum_map (h : ∀ x ∈ l, f x ≡ g x [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

/--
@isnad1 id=modeq.1h4v.s5.707f5347c1d7 from=seed src=0 shape=b944b737 vocab=751d09b6
-/
theorem listSum_map_zero (h : ∀ x ∈ l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map h

/--
@isnad1 id=modeq.1h2v.s5.c04752ff8221 from=seed src=0 shape=e9914ad8 vocab=ffc7b22c
-/
theorem listSum_zero {l : List ℤ} (h : ∀ x ∈ l, x ≡ 0 [ZMOD n]) : l.sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map_zero h

/--
@isnad1 id=modeq.1h5v.s5.6c1194507c22 from=seed src=0 shape=517a379f vocab=1e5b60f5
-/
theorem multisetProd_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).prod ≡ (s.map g).prod [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

/--
@isnad1 id=modeq.1h4v.s5.28b46f315ead from=seed src=0 shape=20dd0437 vocab=1e5b60f5
-/
theorem multisetProd_map_one {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) :
    (s.map f).prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map h

/--
@isnad1 id=modeq.1h2v.s5.ec715ce016a0 from=seed src=0 shape=e9914ad8 vocab=178468ce
-/
theorem multisetProd_one {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 1 [ZMOD n]) : s.prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map_one h

/--
@isnad1 id=modeq.1h5v.s5.a7f6c09827f2 from=seed src=0 shape=517a379f vocab=b6b1ab29
-/
theorem multisetSum_map {s : Multiset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (s.map f).sum ≡ (s.map g).sum [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

/--
@isnad1 id=modeq.1h4v.s5.63e1ec570965 from=seed src=0 shape=20dd0437 vocab=b6b1ab29
-/
theorem multisetSum_map_zero {s : Multiset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (s.map f).sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map h

/--
@isnad1 id=modeq.1h2v.s5.4697f09e8575 from=seed src=0 shape=e9914ad8 vocab=192b8e68
-/
theorem multisetSum_zero {s : Multiset ℤ} (h : ∀ x ∈ s, x ≡ 0 [ZMOD n]) : s.sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map_zero h

/--
@isnad1 id=modeq.1h5v.s5.de5c54c9b904 from=seed src=0 shape=fd08eb72 vocab=51193109
-/
@[gcongr]
protected theorem prod {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ ∏ x ∈ s, g x [ZMOD n] :=
  .multisetProd_map (s := s.1) h

/--
@isnad1 id=modeq.1h4v.s5.7e28a5d07ea0 from=seed src=0 shape=ba998a66 vocab=51193109
-/
theorem prod_one {s : Finset α} (h : ∀ x ∈ s, f x ≡ 1 [ZMOD n]) : ∏ x ∈ s, f x ≡ 1 [ZMOD n] := by
  simpa using ModEq.prod h

/--
@isnad1 id=modeq.1h5v.s5.f5d79b5beb93 from=seed src=0 shape=fd08eb72 vocab=b28bc1f9
-/
@[gcongr]
protected theorem sum {s : Finset α} (h : ∀ x ∈ s, f x ≡ g x [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ ∑ x ∈ s, g x [ZMOD n] :=
  .multisetSum_map (s := s.1) h

/--
@isnad1 id=modeq.1h4v.s5.7abd2b8090ef from=seed src=0 shape=ba998a66 vocab=b28bc1f9
-/
protected theorem sum_zero {s : Finset α} (h : ∀ x ∈ s, f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ 0 [ZMOD n] :=
  .multisetSum_map_zero (s := s.1) h

end ModEq

/--
@isnad1 id=modeq.1h5v.s6.e15c33137e51 from=seed src=0 shape=f37f019f vocab=d5565b8a
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ if a ∈ s then f a else 1 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf

/--
@isnad1 id=modeq.2h5v.s6.fdbe377ab338 from=seed src=0 shape=423b774f vocab=51193109
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 1 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 1 [ZMOD n]) :
    (∏ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

/--
@isnad1 id=modeq.1h5v.s6.906d15982446 from=seed src=0 shape=f37f019f vocab=f603f78d
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ if a ∈ s then f a else 0 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

/--
@isnad1 id=modeq.2h5v.s6.7d946d3caf13 from=seed src=0 shape=423b774f vocab=b28bc1f9
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s → f a ≡ 0 [ZMOD n]) (hf : ∀ x ∈ s, x ≠ a → f x ≡ 0 [ZMOD n]) :
    (∑ x ∈ s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Int
