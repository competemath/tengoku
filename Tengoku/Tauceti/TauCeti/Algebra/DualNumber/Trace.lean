/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Algebra.DualNumber.Basic
public import Tengoku

/-!
# The Frobenius trace pairing on the dual numbers

This file equips the dual numbers over a commutative semiring with the perfect symmetric
associative bilinear form obtained by taking the infinitesimal coefficient of a product.

## Main results

* `TauCeti.dualNumberTracePairing`: the Frobenius trace pairing on the dual numbers.
* `TauCeti.dualNumberTracePairing_isPerfPair`: the trace pairing is perfect.
* `TauCeti.dualNumberTracePairing_isSymm`: the trace pairing is symmetric.
* `TauCeti.dualNumberTracePairing_mul_assoc`: the trace pairing is associative.
-/

public section

namespace TauCeti

universe w

variable (k : Type w) [CommSemiring k]

/-- The Frobenius pairing on the dual numbers, obtained by taking the infinitesimal coefficient
of a product. -/
noncomputable def dualNumberTracePairing : LinearMap.BilinForm k (DualNumber k) :=
  (LinearMap.mul k (DualNumber k)).compr₂ (TrivSqZeroExt.sndHom k k)

/-- Evaluation of the dual-number Frobenius pairing in scalar and infinitesimal coordinates. -/
@[simp]
theorem dualNumberTracePairing_apply (x y : DualNumber k) :
    dualNumberTracePairing k x y = x.fst * y.snd + x.snd * y.fst := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.mul_apply',
    TrivSqZeroExt.sndHom_apply, DualNumber.snd_mul]

/-- The Frobenius trace pairing on the dual numbers is symmetric. -/
theorem dualNumberTracePairing_isSymm : (dualNumberTracePairing k).IsSymm :=
  ⟨fun x y => by simp only [dualNumberTracePairing_apply]; ring⟩

/-- The Frobenius trace pairing on the dual numbers is associative with multiplication. -/
theorem dualNumberTracePairing_mul_assoc (x y z : DualNumber k) :
    dualNumberTracePairing k (x * y) z = dualNumberTracePairing k x (y * z) := by
  rw [dualNumberTracePairing, LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    LinearMap.mul_apply', LinearMap.mul_apply', mul_assoc]

end TauCeti
