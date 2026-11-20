/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DRoot
import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=ne.0h2v.s6.914f7d64bec0 from=translated src=- shape=3f8b0218 vocab=0dd67219
-/
theorem DRoot.j_ne_zero {n : ℕ} (r : DRoot (n + 1)) : r.j ≠ 0 := by
  intro hj
  have h := r.lt
  simp [hj] at h

def DRoot.zeroCoordinateEquiv (n : ℕ) :
    {r : DRoot (n + 1) // r.i = 0} ≃ Fin n × (Bool × Bool) where
  toFun r := (r.1.j.pred r.1.j_ne_zero, (r.1.si, r.1.sj))
  invFun t := ⟨⟨0, t.1.succ, by simp, t.2.1, t.2.2⟩, rfl⟩
  left_inv r := by
    rcases r with ⟨⟨i, j, hij, si, sj⟩, hi⟩
    change i = 0 at hi
    subst i
    apply Subtype.ext
    simp only [Fin.succ_pred]
  right_inv t := by
    rcases t with ⟨j, si, sj⟩
    simp only [Fin.pred_succ]

/--
@isnad1 id=eq.0h2v.s7.281a2098004d from=translated src=- shape=6bca5394 vocab=6bfe4e08
-/
theorem DRoot.coordinate_zero_sq {n : ℕ} (r : DRoot (n + 1)) :
    (r.vector 0) ^ 2 = if r.i = 0 then 1 else 0 := by
  by_cases hi : r.i = 0
  · simp [DRoot.vector, hi, pow_two]
  · simp [DRoot.vector, Ne.symm hi, Ne.symm r.j_ne_zero, hi]

/--
@isnad1 id=eq.0h1v.s7.e9fabb80a6cc from=translated src=- shape=fcf8450e vocab=a0a807d6
-/
theorem dRoot_coordinate_zero_secondMoment (n : ℕ) :
    (∑ r : DRoot (n + 1), (r.vector 0) ^ 2) = 4 * (n : ℤ) := by
  calc
    _ = (Fintype.card {r : DRoot (n + 1) // r.i = 0} : ℤ) := by
      simp only [DRoot.coordinate_zero_sq, Finset.sum_boole, Fintype.card_subtype]
    _ = 4 * (n : ℤ) := by
      rw [Fintype.card_congr (DRoot.zeroCoordinateEquiv n)]
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
        Nat.cast_ofNat]
      omega

end SRG266.Lattice
