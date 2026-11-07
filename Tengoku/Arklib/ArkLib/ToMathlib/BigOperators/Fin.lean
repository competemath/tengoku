/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# More lemmas about `Fin` and big operators
-/

@[expose] public section

namespace Fin

section Interval

open Finset

variable {M : Type*} [CommMonoid M] {n : ℕ} {v : Fin (n + 1) → M}

-- @[to_additive]
-- theorem prod_Ioi_zero : ∏ i ∈ Ioi 0, v i = ∏ j : Fin n, v j.succ := by simp
--   -- rw [Ioi_zero_eq_map, Finset.prod_map, val_succEmb]

-- @[to_additive]
-- theorem prod_Ioi_succ (i : Fin n) : ∏ j ∈ Ioi i.succ, v j = ∏ j ∈ Ioi i, v j.succ := by
--   rw [Ioi_succ, Finset.prod_map, val_succEmb]

-- @[to_additive]
-- theorem prod_Ici_succ (i : Fin n) :
--     ∏ j ∈ Ici i.succ, v j = ∏ j ∈ Ici i, v j.succ := by
--   rw [Ici_succ, Finset.prod_map, val_succEmb]

/--
@isnad1 id=eq.0h4v.s7.cd5db5bdb256 from=translated src=- shape=98b9eedb vocab=d8aef9a6
-/
@[to_additive]
theorem prod_Iio_succ (i : Fin n) :
    ∏ j ∈ Iio i.succ, v j = (∏ j ∈ Iio i.castSucc, v j) * v i.castSucc := by
  calc
    _ = ∏ j ∈ Ico 0 i.succ, v j :=
      prod_congr (by rw [← bot_eq_zero, Ico_bot]) (fun _ _ => rfl)
    _ = ∏ j ∈ Icc 0 i.castSucc, v j :=
      prod_congr rfl (fun _ _ => rfl)
    _ = ∏ j ∈ insert i.castSucc (Ico 0 i.castSucc), v j :=
      prod_congr (by simp only [zero_le, Ico_insert_right]) (fun _ _ => rfl)
    _ = v i.castSucc * ∏ j ∈ Iio i.castSucc, v j :=
      prod_insert (by simp only [mem_Ico, zero_le, lt_self_iff_false, and_false, not_false_eq_true])
    _ = (∏ j ∈ Iio i.castSucc, v j) * v i.castSucc := mul_comm _ _

/--
@isnad1 id=eq.0h4v.s7.baa0524aa56a from=translated src=- shape=95162c6e vocab=c95cc169
-/
@[to_additive]
theorem prod_Iio_eq_univ (i : Fin (n + 1)) :
    ∏ j ∈ Iio i, v j = ∏ j : Fin i, v (Fin.castLE i.isLt.le j) := by
  induction i using Fin.induction with
  | zero =>
    conv_lhs => rw [← bot_eq_zero]
    rw [Iio_bot, prod_empty]
    exact (Fin.prod_univ_zero fun j : Fin 0 => v (Fin.castLE (by omega) j)).symm
  | succ i hi =>
    rw [prod_Iio_succ, hi]
    change (∏ j : Fin ↑i, v (castLE _ j)) * v i.castSucc = ∏ j : Fin (↑i + 1), v (castLE _ j)
    rw [Fin.prod_univ_castSucc]; congr 1

/--
@isnad1 id=eq.0h3v.s7.0ab694f8c493 from=translated src=- shape=b5e62de2 vocab=96ecbc8c
-/
@[to_additive (attr := simp)]
theorem prod_Iic_zero : ∏ j ∈ Iic 0, v j = v 0 := by
  rw [← bot_eq_zero, Iic_bot, prod_singleton]

/--
@isnad1 id=eq.0h4v.s7.488500005736 from=translated src=- shape=50ac6838 vocab=7e50bf83
-/
@[to_additive]
theorem prod_Iic_succ (i : Fin n) :
    ∏ j ∈ Iic i.succ, v j = (∏ j ∈ Iic i.castSucc, v j) * v i.succ := by
  calc
    _ = ∏ j ∈ Icc 0 i.succ, v j :=
      prod_congr (by rw [← bot_eq_zero, Icc_bot]) (fun _ _ => rfl)
    _ = ∏ j ∈ insert i.succ (Ico 0 i.succ), v j :=
      prod_congr (by simp only [zero_le, Ico_insert_right]) (fun _ _ => rfl)
    _ = v i.succ * ∏ j ∈ Iic i.castSucc, v j :=
      prod_insert (by simp only [mem_Ico, zero_le, lt_self_iff_false, and_false, not_false_eq_true])
    _ = (∏ j ∈ Iic i.castSucc, v j) * v i.succ := mul_comm _ _

/--
@isnad1 id=eq.0h4v.s8.7fbbbd8cfb88 from=translated src=- shape=67ccee01 vocab=ebe103ce
-/
@[to_additive]
theorem prod_Iic_eq_univ (i : Fin (n + 1)) :
    ∏ j ∈ Iic i, v j = ∏ j : Fin (i + 1), v (Fin.castLE i.isLt j) := by
  induction i using Fin.induction with
  | zero =>
    rw [prod_Iic_zero]
    calc
      v 0 = v (Fin.castLE (by omega) 0) := congrArg v (Fin.ext rfl)
      _ = ∏ j : Fin 1, v (Fin.castLE (by omega) j) :=
        (Fin.prod_univ_one fun j : Fin 1 => v (Fin.castLE (by omega) j)).symm
  | succ i hi =>
    rw [prod_Iic_succ, hi]
    change (∏ j : Fin (↑i + 1), v (castLE _ j)) * v i.succ =
      ∏ j : Fin (↑i + 1 + 1), v (castLE _ j)
    conv_rhs => rw [Fin.prod_univ_castSucc]
    congr 1

/--
@isnad1 id=eq.0h1v.s7.a0098858ac84 from=translated src=- shape=c2b20618 vocab=79054386
-/
@[simp]
theorem Ici_zero : Ici (0 : Fin (n + 1)) = univ := by rw [← bot_eq_zero, Ici_bot]

/--
@isnad1 id=eq.0h1v.s7.85d85a9eedb2 from=translated src=- shape=06b60e84 vocab=03c0be96
-/
@[simp]
theorem Iio_zero : Iio (0 : Fin (n + 1)) = ∅ := by rw [← bot_eq_zero, Iio_bot]

/--
@isnad1 id=eq.0h1v.s7.d1489541a428 from=translated src=- shape=36089dac vocab=758a151d
-/
@[simp]
theorem Iic_zero : Iic (0 : Fin (n + 1)) = {0} := by rw [← bot_eq_zero, Iic_bot]

/--
@isnad1 id=eq.0h2v.s6.a0f1f901cc5e from=translated src=- shape=5083e339 vocab=07dd4f7b
-/
theorem Iic_castSucc (i : Fin n) : Iic (castSucc i) = (Iic i).map Fin.castSuccEmb := by
  rw [Iic_eq_cons_Iio, Iic_eq_cons_Iio, map_cons]
  simp only [Iio_castSucc, cons_eq_insert, castSuccEmb_apply]

/--
@isnad1 id=eq.0h2v.s6.fbe568a0d6b1 from=translated src=- shape=5083e339 vocab=c6ca7059
-/
@[simp]
theorem Ici_succ (i : Fin n) : Ici i.succ = (Ici i).map (Fin.succEmb _) := by
  rw [Ici_eq_cons_Ioi, Ici_eq_cons_Ioi, map_cons]
  simp only [Ioi_succ, cons_eq_insert, coe_succEmb]

end Interval

end Fin
