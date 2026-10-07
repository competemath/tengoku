/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.SuccPred
public import Tengoku.Seed.Order.Interval.Set.SuccPred

/-!
# Set intervals in an additive successor-predecessor order

This file proves relations between the various set intervals in an additive successor/predecessor
order.

## Notes

Please keep in sync with:
* `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Finset/SuccPred.lean`
* `Mathlib/Order/Interval/Set/SuccPred.lean`

## TODO

Copy over `insert` lemmas from `Mathlib/Order/Interval/Finset/Nat.lean`.
-/

public section

open Order

variable {α : Type*}

namespace Set
variable [LinearOrder α] [One α]

/-! ### Two-sided intervals -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a b : α}

/-!
#### Orders possibly with maximal elements

##### Equalities of intervals
-/

/--
@isnad1 id=eq.0h3v.s6.05e4493e5408 from=seed src=0 shape=90a24bd8 vocab=1514ded0
-/
lemma Ico_add_one_left_eq_Ioo (a b : α) : Ico (a + 1) b = Ioo a b := by
  simpa [succ_eq_add_one] using Ico_succ_left_eq_Ioo a b

/--
@isnad1 id=eq.1h3v.s6.2202e9e23968 from=seed src=0 shape=0e7169bf vocab=5824056d
-/
lemma Icc_add_one_left_eq_Ioc_of_not_isMax (ha : ¬ IsMax a) (b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc_of_not_isMax ha b

/--
@isnad1 id=eq.1h3v.s6.f5fd784d2b0f from=seed src=0 shape=638b08c2 vocab=ac5b0f12
-/
lemma Ico_add_one_right_eq_Icc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc_of_not_isMax hb a

/--
@isnad1 id=eq.1h3v.s6.72531fde3ca4 from=seed src=0 shape=638b08c2 vocab=26f0e656
-/
lemma Ioo_add_one_right_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc_of_not_isMax hb a

/--
@isnad1 id=eq.1h3v.s6.ce9f7db1a201 from=seed src=0 shape=4a1ec4c7 vocab=f4ef9afe
-/
lemma Ico_add_one_add_one_eq_Ioc_of_not_isMax (hb : ¬ IsMax b) (a : α) :
    Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc_of_not_isMax hb a

/-! ##### Inserting into intervals -/

/--
@isnad1 id=eq.1h3v.s6.ca401eceebe2 from=seed src=0 shape=12d87c4b vocab=26ae3eef
-/
lemma insert_Icc_add_one_left_eq_Icc (h : a ≤ b) : insert a (Icc (a + 1) b) = Icc a b := by
  simpa [succ_eq_add_one] using insert_Icc_succ_left_eq_Icc h

/--
@isnad1 id=eq.1h3v.s7.cb2321478baa from=seed src=0 shape=1af3decf vocab=26ae3eef
-/
lemma insert_Icc_right_eq_Icc_add_one (h : a ≤ b + 1) :
    insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  simpa [← succ_eq_add_one] using insert_Icc_right_eq_Icc_succ (succ_eq_add_one b ▸ h)

/--
@isnad1 id=eq.2h3v.s6.ccd855fcb770 from=seed src=0 shape=d3ceffb5 vocab=c28207d0
-/
lemma insert_Ico_right_eq_Ico_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ_of_not_isMax h hb

/--
@isnad1 id=eq.1h3v.s6.a17d46aa59cf from=seed src=0 shape=12d87c4b vocab=2828bd26
-/
lemma insert_Ico_add_one_left_eq_Ico (h : a < b) : insert a (Ico (a + 1) b) = Ico a b := by
  simpa [succ_eq_add_one] using insert_Ico_succ_left_eq_Ico h

/--
@isnad1 id=eq.2h3v.s7.5d80a8babc86 from=seed src=0 shape=272da8ee vocab=a76c935f
-/
lemma insert_Ioc_right_eq_Ioc_add_one_of_not_isMax (h : a ≤ b) (hb : ¬ IsMax b) :
    insert (b + 1) (Ioc a b) = Ioc a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ioc_right_eq_Ioc_succ_of_not_isMax h hb

/--
@isnad1 id=eq.1h3v.s6.79208c5e0ff0 from=seed src=0 shape=3755ef7c vocab=2fc9d53d
-/
lemma insert_Ioc_add_one_left_eq_Ioc (h : a < b) : insert (a + 1) (Ioc (a + 1) b) = Ioc a b := by
  simpa [succ_eq_add_one] using insert_Ioc_succ_left_eq_Ioc h

/-!
#### Orders with no maximal elements

##### Equalities of intervals
-/

variable [NoMaxOrder α]

/--
@isnad1 id=eq.0h3v.s6.a6090f487ba8 from=seed src=0 shape=d78ccae1 vocab=57c06bbd
-/
lemma Icc_add_one_left_eq_Ioc (a b : α) : Icc (a + 1) b = Ioc a b := by
  simpa [succ_eq_add_one] using Icc_succ_left_eq_Ioc a b

/--
@isnad1 id=eq.0h3v.s6.b455ac0e910d from=seed src=0 shape=676e440f vocab=a2cfced1
-/
lemma Ico_add_one_right_eq_Icc (a b : α) : Ico a (b + 1) = Icc a b := by
  simpa [succ_eq_add_one] using Ico_succ_right_eq_Icc a b

/--
@isnad1 id=eq.0h3v.s6.c85474d2bf9e from=seed src=0 shape=676e440f vocab=5dc55c31
-/
lemma Ioo_add_one_right_eq_Ioc (a b : α) : Ioo a (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ioo_succ_right_eq_Ioc a b

/--
@isnad1 id=eq.0h3v.s6.b90e5db80b60 from=seed src=0 shape=cfa6032e vocab=3f3d9794
-/
lemma Ico_add_one_add_one_eq_Ioc (a b : α) : Ico (a + 1) (b + 1) = Ioc a b := by
  simpa [succ_eq_add_one] using Ico_succ_succ_eq_Ioc a b

/-! ##### Inserting into intervals -/

/--
@isnad1 id=eq.1h3v.s6.17adaffda94e from=seed src=0 shape=c3734c7f vocab=d4cc09af
-/
lemma insert_Ico_right_eq_Ico_add_one (h : a ≤ b) : insert b (Ico a b) = Ico a (b + 1) := by
  simpa [succ_eq_add_one] using insert_Ico_right_eq_Ico_succ h

/--
@isnad1 id=eq.1h3v.s7.0f9928d37414 from=seed src=0 shape=6feec4d4 vocab=57a5a9a5
-/
lemma insert_Ioc_right_eq_Ioc_add_one (h : a ≤ b) : insert (b + 1) (Ioc a b) = Ioc a (b + 1) :=
  insert_Ioc_right_eq_Ioc_add_one_of_not_isMax h (not_isMax _)

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a b : α}

/-!
#### Orders possibly with minimal elements

##### Equalities of intervals
-/

/--
@isnad1 id=eq.0h3v.s6.77e63068531d from=seed src=0 shape=7ee72f33 vocab=034ccf5d
-/
lemma Ioc_sub_one_right_eq_Ioo (a b : α) : Ioc a (b - 1) = Ioo a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_right_eq_Ioo a b

/--
@isnad1 id=eq.1h3v.s6.b25c79906c8a from=seed src=0 shape=638b08c2 vocab=52b1a330
-/
lemma Icc_sub_one_right_eq_Ico_of_not_isMin (hb : ¬ IsMin b) (a : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico_of_not_isMin hb a

/--
@isnad1 id=eq.1h3v.s6.eafcb52f02ce from=seed src=0 shape=0e7169bf vocab=a126a44c
-/
lemma Ioc_sub_one_left_eq_Icc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc_of_not_isMin ha b

/--
@isnad1 id=eq.1h3v.s6.d3f7015dd02f from=seed src=0 shape=0e7169bf vocab=de0e7962
-/
lemma Ioo_sub_one_left_eq_Ioc_of_not_isMin (ha : ¬ IsMin a) (b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc_of_not_isMin ha b

/--
@isnad1 id=eq.1h3v.s6.d536809d96a0 from=seed src=0 shape=55c3d917 vocab=958d1023
-/
lemma Ioc_sub_one_sub_one_eq_Ico_of_not_isMin (ha : ¬ IsMin a) (b : α) :
    Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico_of_not_isMin ha b

/-! ##### Inserting into intervals -/

/--
@isnad1 id=eq.1h3v.s6.1abb62dff186 from=seed src=0 shape=13668f80 vocab=aab3e56c
-/
lemma insert_Icc_sub_one_right_eq_Icc (h : a ≤ b) : insert b (Icc a (b - 1)) = Icc a b := by
  simpa [pred_eq_sub_one] using insert_Icc_pred_right_eq_Icc h

/--
@isnad1 id=eq.1h3v.s7.718c9c9c22f7 from=seed src=0 shape=16331d7f vocab=aab3e56c
-/
lemma insert_Icc_left_eq_Icc_sub_one (h : a - 1 ≤ b) :
    insert (a - 1) (Icc a b) = Icc (a - 1) b := by
  simpa [← pred_eq_sub_one] using insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)

/--
@isnad1 id=eq.2h3v.s6.1bd7f77f4c8a from=seed src=0 shape=e944afcc vocab=f0bf87b7
-/
lemma insert_Ioc_left_eq_Ioc_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred_of_not_isMin h ha

/--
@isnad1 id=eq.1h3v.s6.526a3f15f95f from=seed src=0 shape=13668f80 vocab=f7c5eac6
-/
lemma insert_Ioc_sub_one_right_eq_Ioc (h : a < b) : insert b (Ioc a (b - 1)) = Ioc a b := by
  simpa [pred_eq_sub_one] using insert_Ioc_pred_right_eq_Ioc h

/--
@isnad1 id=eq.2h3v.s7.05f5c310eab8 from=seed src=0 shape=d16999f2 vocab=32b6123d
-/
lemma insert_Ico_left_eq_Ico_sub_one_of_not_isMin (h : a ≤ b) (ha : ¬ IsMin a) :
    insert (a - 1) (Ico a b) = Ico (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ico_left_eq_Ico_pred_of_not_isMin h ha

/--
@isnad1 id=eq.1h3v.s6.14c01b081ae0 from=seed src=0 shape=92115765 vocab=cdc000d2
-/
lemma insert_Ico_sub_one_right_eq_Ico (h : a < b) : insert (b - 1) (Ico a (b - 1)) = Ico a b := by
  simpa [pred_eq_sub_one] using insert_Ico_pred_right_eq_Ico h

/-!
#### Orders with no minimal elements

##### Equalities of intervals
-/

variable [NoMinOrder α]

/--
@isnad1 id=eq.0h3v.s6.c1732847b732 from=seed src=0 shape=676e440f vocab=40301615
-/
lemma Icc_sub_one_right_eq_Ico (a b : α) : Icc a (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Icc_pred_right_eq_Ico a b

/--
@isnad1 id=eq.0h3v.s6.c972105fec77 from=seed src=0 shape=d78ccae1 vocab=cf10b0ff
-/
lemma Ioc_sub_one_left_eq_Icc (a b : α) : Ioc (a - 1) b = Icc a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_left_eq_Icc a b

/--
@isnad1 id=eq.0h3v.s6.c3f41f09e17d from=seed src=0 shape=d78ccae1 vocab=1eb9adb1
-/
lemma Ioo_sub_one_left_eq_Ioc (a b : α) : Ioo (a - 1) b = Ico a b := by
  simpa [pred_eq_sub_one] using Ioo_pred_left_eq_Ioc a b

/--
@isnad1 id=eq.0h3v.s6.eca94002921b from=seed src=0 shape=cfa6032e vocab=fe9fdcad
-/
lemma Ioc_sub_one_sub_one_eq_Ico (a b : α) : Ioc (a - 1) (b - 1) = Ico a b := by
  simpa [pred_eq_sub_one] using Ioc_pred_pred_eq_Ico a b

/-! ##### Inserting into intervals -/

/--
@isnad1 id=eq.1h3v.s6.86e0e4d43ed7 from=seed src=0 shape=94920909 vocab=47451059
-/
lemma insert_Ioc_left_eq_Ioc_sub_one (h : a ≤ b) : insert a (Ioc a b) = Ioc (a - 1) b := by
  simpa [pred_eq_sub_one] using insert_Ioc_left_eq_Ioc_pred h

/--
@isnad1 id=eq.1h3v.s7.fca107db8cc6 from=seed src=0 shape=9d3dc47b vocab=2b6c639b
-/
lemma insert_Ico_left_eq_Ico_sub_one (h : a ≤ b) : insert (a - 1) (Ico a b) = Ico (a - 1) b :=
  insert_Ico_left_eq_Ico_sub_one_of_not_isMin h (not_isMin _)

end PredSubOrder

section SuccAddPredSubOrder
variable [Add α] [Sub α] [SuccAddOrder α] [PredSubOrder α] [Nontrivial α]

/--
@isnad1 id=eq.0h3v.s6.2d7ed2858f91 from=seed src=0 shape=19f779eb vocab=a68ab82f
-/
lemma Icc_add_one_sub_one_eq_Ioo (a b : α) : Icc (a + 1) (b - 1) = Ioo a b := by
  simpa [succ_eq_add_one, pred_eq_sub_one] using Icc_succ_pred_eq_Ioo a b

end SuccAddPredSubOrder

/-! ### One-sided interval towards `⊥` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {b : α}

/--
@isnad1 id=eq.1h2v.s6.84c90b40c434 from=seed src=0 shape=f1e43560 vocab=349c1e9f
-/
lemma Iio_add_one_eq_Iic_of_not_isMax (hb : ¬ IsMax b) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic_of_not_isMax hb

variable [NoMaxOrder α]

/--
@isnad1 id=eq.0h2v.s6.8c5f4e89af32 from=seed src=0 shape=de1132eb vocab=2b193727
-/
lemma Iio_add_one_eq_Iic (b : α) : Iio (b + 1) = Iic b := by
  simpa [succ_eq_add_one] using Iio_succ_eq_Iic b

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {b : α}

/--
@isnad1 id=eq.1h2v.s6.67dbd8df9d6e from=seed src=0 shape=f1e43560 vocab=d52fd97c
-/
lemma Iic_sub_one_eq_Iio_of_not_isMin (hb : ¬ IsMin b) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio_of_not_isMin hb

variable [NoMinOrder α]

/--
@isnad1 id=eq.0h2v.s6.0623c0bb2694 from=seed src=0 shape=de1132eb vocab=f3b20278
-/
lemma Iic_sub_one_eq_Iio (b : α) : Iic (b - 1) = Iio b := by
  simpa [pred_eq_sub_one] using Iic_pred_eq_Iio b

end PredSubOrder

/-! ### One-sided interval towards `⊤` -/

section SuccAddOrder
variable [Add α] [SuccAddOrder α] {a : α}

/--
@isnad1 id=eq.1h2v.s6.b84d8b27989f from=seed src=0 shape=f1e43560 vocab=433ec0ce
-/
lemma Ici_add_one_eq_Ioi_of_not_isMax (ha : ¬ IsMax a) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi_of_not_isMax ha

variable [NoMaxOrder α]

/--
@isnad1 id=eq.0h2v.s6.d31d9c20ed84 from=seed src=0 shape=de1132eb vocab=29305b08
-/
lemma Ici_add_one_eq_Ioi (a : α) : Ici (a + 1) = Ioi a := by
  simpa [succ_eq_add_one] using Ici_succ_eq_Ioi a

end SuccAddOrder

section PredSubOrder
variable [Sub α] [PredSubOrder α] {a a : α}

/--
@isnad1 id=eq.1h2v.s6.aa8abce47d80 from=seed src=0 shape=f1e43560 vocab=b5fa413b
-/
lemma Ioi_sub_one_eq_Ici_of_not_isMin (ha : ¬ IsMin a) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici_of_not_isMin ha

variable [NoMinOrder α]

/--
@isnad1 id=eq.0h2v.s6.7145ea17db7f from=seed src=0 shape=de1132eb vocab=e60dd97a
-/
lemma Ioi_sub_one_eq_Ici (a : α) : Ioi (a - 1) = Ici a := by
  simpa [pred_eq_sub_one] using Ioi_pred_eq_Ici a

end PredSubOrder
end Set
