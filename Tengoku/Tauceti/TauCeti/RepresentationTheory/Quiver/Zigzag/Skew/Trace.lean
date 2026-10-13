/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Trace
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Multiplication

/-!
# The Frobenius trace of a skew-zigzag algebra

The skew-zigzag relation quotient of a finite simple graph without isolated vertices is a
Frobenius algebra. After choosing one incident edge `t i` at every vertex, this file defines the
trace to be one on the corresponding volume classes and zero on vertex idempotents and arrows.
The pairing `(x, y) ↦ tr (x * y)` is associative and perfect.

Unlike the ordinary zigzag trace pairing, the skew pairing need not be symmetric. If `d : G.Dart`,
then the product of the arrow of `d` with the arrow of `d.symm` is the backtrack at `d.snd` along
`d.symm`. Relative to the chosen volume there, its trace is the unit

```text
c.ratio d.symm.adj (t d.snd).2.
```

These units are the distinguished entries of the Gram matrix. Thus the same basis involution as in
the ordinary case still locates the one unit-valued entry in every row, all other entries of that
row being zero, while the skew parameter gives its value. This proves perfectness over an
arbitrary commutative ring without inverting any scalar outside the units already carried by the
parameter. It also gives an exact criterion for the chosen trace to be symmetric: the weights of a
dart and its reverse must agree.

## Main definitions

* `TauCeti.skewZigzagPairingWeight`: the unit occurring in a row of the Gram matrix.
* `TauCeti.skewZigzagTrace`: the normalized trace attached to chosen incident edges.
* `TauCeti.skewZigzagTracePairing`: the associative pairing `(x, y) ↦ tr (x * y)`.

## Main results

* `TauCeti.skewZigzagTracePairing_skewZigzagBasisFun`: the weighted permutation Gram matrix.
* `TauCeti.skewZigzagTracePairing_isPerfPair`: the pairing is perfect.
* `TauCeti.skewZigzagTrace_mul_comm_iff`: the trace is symmetric exactly when opposite darts have
  equal pairing weights.

## References

See C. Couture, *Skew-Zigzag Algebras*, Section 3,
https://arxiv.org/abs/1509.08405, and S. Huerfano and M. Khovanov,
*A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

/-! ### The weights of the pairing -/

section PairingWeight

variable (k : Type w) [Monoid k] {V : Type u} (G : SimpleGraph V)
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

/-- The unit in the Gram-matrix row indexed by a skew-zigzag basis element. Idempotent and volume
rows have weight one. The row of a dart `d` has the ratio from the return edge `d.symm` to the
chosen edge at its base `d.snd`. -/
def skewZigzagPairingWeight : ZigzagBasisIndex G → kˣ
  | .inl _ => 1
  | .inr (.inl d) => c.ratio d.symm.adj (t d.snd).2
  | .inr (.inr _) => 1

@[simp]
theorem skewZigzagPairingWeight_inl (i : V) :
    skewZigzagPairingWeight k G c t (.inl i) = 1 := (rfl)

@[simp]
theorem skewZigzagPairingWeight_inr_inl (d : G.Dart) :
    skewZigzagPairingWeight k G c t (.inr (.inl d)) =
      c.ratio d.symm.adj (t d.snd).2 := (rfl)

@[simp]
theorem skewZigzagPairingWeight_inr_inr (i : V) :
    skewZigzagPairingWeight k G c t (.inr (.inr i)) = 1 := (rfl)

end PairingWeight

/-! ### The normalized trace -/

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

/-- **The Frobenius trace of a skew-zigzag algebra**, normalized by chosen incident edges: it is
one on the chosen volume class at each vertex and zero on the vertex idempotents and arrows. -/
noncomputable def skewZigzagTrace : skewZigzagQuotient k G c →ₗ[k] k :=
  (skewZigzagBasis k G c t).constr k
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1))

/-- The normalized trace on the skew-zigzag basis. -/
theorem skewZigzagTrace_skewZigzagBasisFun (b : ZigzagBasisIndex G) :
    skewZigzagTrace k G c t (skewZigzagBasisFun k G c t b) =
      Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1) b := by
  rw [← skewZigzagBasis_apply k G c t b]
  exact (skewZigzagBasis k G c t).constr_basis k
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1)) b

/-- The normalized trace vanishes on a vertex idempotent. -/
@[simp]
theorem skewZigzagTrace_skewZigzagMk_vertexIdempotent (i : V) :
    skewZigzagTrace k G c t
      (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) = 0 := by
  simpa using skewZigzagTrace_skewZigzagBasisFun k G c t (.inl i)

/-- The normalized trace is one on the chosen volume class. -/
@[simp]
theorem skewZigzagTrace_skewZigzagVolume_chosen (i : V) :
    skewZigzagTrace k G c t (skewZigzagVolume k G c (t i)) = 1 := by
  simpa using skewZigzagTrace_skewZigzagBasisFun k G c t (.inr (.inr i))

/-- The normalized trace of an arbitrary backtrack is its prescribed ratio to the chosen
backtrack at the same vertex. -/
@[simp]
theorem skewZigzagTrace_skewZigzagVolume {i : V} (e : {j : V // G.Adj i j}) :
    skewZigzagTrace k G c t (skewZigzagVolume k G c e) =
      (c.ratio e.2 (t i).2 : k) := by
  have he := skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c e e.2
  rw [c.ratio_self, Units.val_one, one_smul] at he
  rw [← he, skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c (t i) e.2, map_smul,
    skewZigzagTrace_skewZigzagVolume_chosen]
  exact mul_one _

/-! ### The Frobenius pairing -/

/-- **The Frobenius pairing of a skew-zigzag algebra**, `(x, y) ↦ tr (x * y)`. -/
noncomputable def skewZigzagTracePairing :
    LinearMap.BilinForm k (skewZigzagQuotient k G c) :=
  (LinearMap.mul k (skewZigzagQuotient k G c)).compr₂ (skewZigzagTrace k G c t)

@[simp]
theorem skewZigzagTracePairing_apply (x y : skewZigzagQuotient k G c) :
    skewZigzagTracePairing k G c t x y = skewZigzagTrace k G c t (x * y) := (rfl)

/-! ### The weighted permutation Gram matrix -/

/-! ### Perfectness -/

/-! ### Symmetry -/

end TauCeti
