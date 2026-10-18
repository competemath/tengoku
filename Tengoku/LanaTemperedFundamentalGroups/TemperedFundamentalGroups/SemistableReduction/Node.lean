/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The local model of a node

For a commutative ring `O` and `a : O`, `SemistableReduction.Node O a` is the `O`-algebra
`O[u, v] ⧸ (u v - a)`, the local model of a node of thickness `a` (Blueprint §9.2, the local
tame lemma). We show:

* `Node.span_eq_top`: as an `O`-module, `Node O a` is spanned by the monomials `u ^ i` and
  `v ^ (j + 1)` (the normal form of an element).
* `Node.laurent O a k`: for a domain `O` with fraction field `K`, the `O`-algebra map
  `Node O a → K[T;T⁻¹]`, `u ↦ T ^ k`, `v ↦ a T ^ (-k)`; it is injective when `a ≠ 0` and
  `0 < k` (`Node.laurent_injective`).
* `Node.isDomain`: `Node O a` is a domain if `O` is and `a ≠ 0`.
* `Node.kummer O c m`: the `O`-algebra map `Node O (c ^ m) → Node O c`, `u ↦ u ^ m`, `v ↦ v ^ m`,
  injective for `c ≠ 0`, `0 < m` (`Node.kummer_injective`), and making `Node O c` a finite
  (`Node.kummer_finite`), hence integral, algebra over `Node O (c ^ m)`.
-/

open LaurentPolynomial

namespace SemistableReduction

variable (O : Type*) [CommRing O]

/-- The local model `O[u, v] ⧸ (u v - a)` of a node of thickness `a`. -/
abbrev Node (a : O) : Type _ :=
  MvPolynomial (Fin 2) O ⧸ Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a}

namespace Node

variable {O} (a : O)

/-- The first coordinate `u` of the node `O[u, v] ⧸ (u v - a)`. -/
noncomputable def u : Node O a := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The second coordinate `v` of the node `O[u, v] ⧸ (u v - a)`. -/
noncomputable def v : Node O a := Ideal.Quotient.mk _ (MvPolynomial.X 1)

lemma u_mul_v : u a * v a = algebraMap O (Node O a) a := by
  rw [u, v, ← map_mul, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

variable {a}

/-- The `O`-algebra map out of the node sending `u ↦ x` and `v ↦ y`, for `x y = a`. -/
noncomputable def lift {S : Type*} [CommRing S] [Algebra O S] (x y : S)
    (h : x * y = algebraMap O S a) : Node O a →ₐ[O] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval ![x, y]) fun p hp ↦ by
    induction hp using Submodule.span_induction with
    | mem q hq =>
      rw [Set.mem_singleton_iff.mp hq]
      simp [h]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul r _ _ h₁ => simp [h₁]

/-- Two `O`-algebra maps out of the node agreeing on `u` and `v` are equal. -/
lemma algHom_ext {S : Type*} [CommRing S] [Algebra O S] {f g : Node O a →ₐ[O] S}
    (hu : f (u a) = g (u a)) (hv : f (v a) = g (v a)) : f = g := by
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
  fin_cases i
  · exact hu
  · exact hv

variable (a)

/-- The monomials `u ^ i` (`i : ℕ`) and `v ^ (j + 1)` (`j : ℕ`) of the node. -/
noncomputable def monomial : ℕ ⊕ ℕ → Node O a :=
  Sum.elim (fun i ↦ u a ^ i) (fun j ↦ v a ^ (j + 1))

section Laurent

local notation "K" => FractionRing O

/-- The `O`-algebra map `Node O a → K[T;T⁻¹]`, `u ↦ T ^ k`, `v ↦ a T ^ (-k)`, where `K` is the
fraction field of `O`. -/
noncomputable def laurent (k : ℕ) : Node O a →ₐ[O] K[T;T⁻¹] :=
  lift (T k) (C (algebraMap O K a) * T (-k)) (by
    rw [mul_left_comm, ← T_add, add_neg_cancel, T_zero, mul_one,
      LaurentPolynomial.algebraMap_apply])

/-- The exponent of the image of a monomial under `laurent a k`. -/
def laurentExp (k : ℕ) : ℕ ⊕ ℕ → ℤ :=
  Sum.elim (fun i ↦ k * i) (fun j ↦ -(k * (j + 1)))

/-- The coefficient of the image of a monomial under `laurent a k`. -/
noncomputable def laurentCoeff : ℕ ⊕ ℕ → K :=
  Sum.elim (fun _ ↦ 1) (fun j ↦ algebraMap O K a ^ (j + 1))

variable [IsDomain O]

variable {a}

end Laurent

section Kummer

variable (c : O) (m : ℕ)

/-- The Kummer map `O[u, v] ⧸ (u v - c ^ m) → O[w, z] ⧸ (w z - c)`, `u ↦ w ^ m`, `v ↦ z ^ m`. -/
noncomputable def kummer : Node O (c ^ m) →ₐ[O] Node O c :=
  lift (u c ^ m) (v c ^ m) (by rw [← mul_pow, u_mul_v, map_pow])

variable {c m}

variable (c m)

/-- `O[w, z] ⧸ (w z - c)` as an algebra over `O[u, v] ⧸ (u v - c ^ m)` via the Kummer map
`u ↦ w ^ m`, `v ↦ z ^ m`. Not an instance. -/
noncomputable abbrev kummerAlgebra : Algebra (Node O (c ^ m)) (Node O c) :=
  (kummer c m).toAlgebra

variable {m}

end Kummer

end Node

end SemistableReduction
