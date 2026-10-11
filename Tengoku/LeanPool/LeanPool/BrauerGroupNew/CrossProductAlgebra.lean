/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, contributors
-/
module

public import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.Algebra.Algebra.Equiv
public import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic
public import Tengoku
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.Data.DFinsupp.Submonoid
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.LinearAlgebra.LinearIndependent.Defs
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Tengoku.LeanPool.LeanPool.BrauerGroupNew.TwoSidedIdeal

/-!
# Cross product algebra

This file constructs the cross product algebra associated to a 2-cocycle of a field extension
`K / F` and shows that it is a central simple `F`-algebra of dimension `dim(K / F) ^ 2`.

## References

* [*Advanced Algebra*]
-/

@[expose] public section

open groupCohomology Function Module

suppress_compilation

variable {R S F K : Type*} [Field F] [Field K] [Algebra F K] {f : Gal(K, F) × Gal(K, F) → Kˣ}

/-- The cross product algebra attached to a multiplicative two-cocycle on `Gal(K, F)`. -/
@[ext]
structure CrossProductAlgebra (f : Gal(K, F) × Gal(K, F) → Kˣ) where
  /-- The finitely supported coefficient function on the Galois group. -/
  val : Gal(K, F) →₀ K

namespace CrossProductAlgebra

variable {x y : CrossProductAlgebra f}

lemma val_injective : Injective (val (f := f)) := fun _ _ ↦ CrossProductAlgebra.ext

@[simp] lemma val_inj : x.val = y.val ↔ x = y := val_injective.eq_iff

instance : Zero (CrossProductAlgebra f) where
  zero := ⟨0⟩

instance : Add (CrossProductAlgebra f) where
  add x y := ⟨x.val + y.val⟩

instance : Neg (CrossProductAlgebra f) where
  neg x := ⟨-x.val⟩

instance : Sub (CrossProductAlgebra f) where
  sub x y := ⟨x.val - y.val⟩

instance [Semiring R] [Module R K] : SMul R (CrossProductAlgebra f) where
  smul r x := ⟨r • x.val⟩

@[simp] lemma val_zero : (0 : CrossProductAlgebra f).val = 0 := rfl

@[simp] lemma val_add (x y : CrossProductAlgebra f) : (x + y).val = x.val + y.val := rfl

@[simp] lemma val_smul [Semiring R] [Module R K] (r : R) (x : CrossProductAlgebra f) :
    (r • x).val = r • x.val := rfl

@[simp] lemma val_neg (x : CrossProductAlgebra f) : (-x).val = -x.val := rfl

@[simp] lemma val_sub (x y : CrossProductAlgebra f) : (x - y).val = x.val - y.val := rfl

@[simp] lemma mk_zero : (mk 0 : CrossProductAlgebra f) = 0 := rfl

@[simp] lemma mk_add_mk (x y : Gal(K, F) →₀ K) :
    (mk x + mk y : CrossProductAlgebra f) = mk (x + y) := rfl

@[simp] lemma smul_mk [Semiring R] [Module R K] (r : R) (x : Gal(K, F) →₀ K) :
    (r • mk x : CrossProductAlgebra f) = mk (r • x) := rfl

@[simp] lemma neg_mk (x : Gal(K, F) →₀ K) : (- mk x : CrossProductAlgebra f) = mk (-x) := rfl

@[simp] lemma mk_sub_mk (x y : Gal(K, F) →₀ K) :
    (mk x - mk y : CrossProductAlgebra f) = mk (x - y) := rfl

instance addCommGroup : AddCommGroup (CrossProductAlgebra f) :=
  val_injective.addCommGroup val val_zero val_add val_neg val_sub (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The additive equivalence with finitely supported functions on the Galois group. -/
@[simps]
def valAddEquiv : CrossProductAlgebra f ≃+ (Gal(K, F) →₀ K) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' := val_add

@[simp]
lemma val_finsuppSum {α M : Type*} [AddCommMonoid M] (g : α →₀ M)
    (h : α → M → CrossProductAlgebra f) :
    (g.sum h).val = g.sum (fun a m ↦ (h a m).val) :=
  map_finsuppSum (valAddEquiv (f := f)).toAddMonoidHom g h

instance [Semiring R] [Module R K] : Module R (CrossProductAlgebra f) :=
  val_injective.module _ valAddEquiv.toAddMonoidHom val_smul

/-- The linear equivalence with finitely supported functions on the Galois group. -/
@[simps]
def valLinearEquiv [Semiring R] [Module R K] :
    CrossProductAlgebra f ≃ₗ[R] (Gal(K, F) →₀ K) where
  __ := valAddEquiv
  map_smul' := val_smul

/-- The standard basis of the cross product algebra over `K`. -/
@[simps]
def basis : Basis Gal(K, F) K (CrossProductAlgebra f) where
  repr := valLinearEquiv

instance : One (CrossProductAlgebra f) where
  one := ⟨.single 1 (f (1, 1))⁻¹⟩

@[simp] lemma val_one : (1 : CrossProductAlgebra f).val = .single 1 (f (1, 1))⁻¹ := rfl

variable [Fact <| IsMulCocycle₂ f]

variable [Module.Finite F K] [IsGalois F K]

/-! ### Finite dimensionality -/

/-! ### Centrality -/

/-! ### Simplicity -/

variable {I : TwoSidedIdeal (CrossProductAlgebra f)}

/-! ### The cross product algebra as a central simple algebra -/

end CrossProductAlgebra
