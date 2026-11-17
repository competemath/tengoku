import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Forms.Calculus.Shuffle
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Forms.Calculus.Representation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identities of the shuffle product

The unit laws, associativity and graded commutativity of the shuffle product of scalar
alternating maps, and the expression of `alternatizeUncurryFin (φ.smulRight θ)` as the shuffle
product of the `1`-form `φ` with `θ`. Each identity is evaluated at a tuple `v`; pulling back
along `tupleMap v` reduces it to an identity between alternatizations on `Fin N → R`. No factorial
is inverted, so the identities hold over every commutative ring.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l m : ℕ}

/-- The pullback of the constant `0`-form `1` is `1`.-/
theorem constOfIsEmpty_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (g : M' →ₗ[R] M) :
    (AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R)).compLinearMap g =
      AlternatingMap.constOfIsEmpty R M' (Fin 0) (1 : R) := by
  ext v
  simp

/-- The pullback of a `1`-form is the `1`-form of the composite.-/
theorem ofSubsingleton_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (φ : M →ₗ[R] R) (g : M' →ₗ[R] M) :
    (AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ).compLinearMap g =
      AlternatingMap.ofSubsingleton R M' R (0 : Fin 1) (φ ∘ₗ g) := by
  ext v
  simp

/-- A `1`-ary multilinear map is its own alternatization.-/
theorem alternatization_ofSubsingleton (φ : M →ₗ[R] R) :
    MultilinearMap.alternatization (MultilinearMap.ofSubsingleton R M R (0 : Fin 1) φ) =
      AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ := by
  ext v
  simp [MultilinearMap.alternatization_apply]

/-- The `m`-th power of `finRotate n` adds `m` modulo `n`.-/
theorem val_finRotate_pow (n m : ℕ) (i : Fin n) : (((finRotate n) ^ m) i : ℕ) = (i + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    cases n with
    | zero => exact i.elim0
    | succ n =>
      rw [pow_succ', Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
        ← Nat.add_mod, Nat.add_assoc]

/-- The block swap `Fin (k + l) → Fin (l + k) = Fin (k + l)` has sign `(-1)^(k l)`.-/
theorem sign_finAddFlip_trans_finCongr (k l : ℕ) :
    Perm.sign (finAddFlip.trans (finCongr (Nat.add_comm l k)) : Perm (Fin (k + l))) =
      (-1) ^ (k * l) := by
  have hπ : (finAddFlip.trans (finCongr (Nat.add_comm l k)) : Perm (Fin (k + l))) =
      finRotate (k + l) ^ l := by
    ext i
    rw [val_finRotate_pow]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_castAdd]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_castAdd]
      rw [show k + j + l = j + (k + l) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self l
  have hexp : (k + l - 1) * l = k * l + (t + t) := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp at ht ⊢
      omega
    · rw [show k + l - 1 = k + (l - 1) by omega, add_mul, ← ht, mul_comm (l - 1) l]
  rw [hπ, map_pow, sign_finRotate, ← pow_mul, hexp, pow_add, Even.neg_one_pow ⟨t, rfl⟩, mul_one]

section Uncurry

end Uncurry

end AlternatingAnalytic.Forms
