/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# Tsupport Product

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

namespace CKN

/-- The topological support of a separated product ψ(x) θ(y) on a product space is the product
of the two topological supports.
@isnad1 id=eq.0h5v.s6.70cd607d920e from=translated src=- shape=e979fec6 vocab=cf1a681c
-/
theorem tsupport_mul_prod_eq {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MulZeroClass M] [NoZeroDivisors M] (ψ : X → M) (θ : Y → M) :
    tsupport (fun z : X × Y => ψ z.1 * θ z.2) = tsupport ψ ×ˢ tsupport θ := by
  have hsupp : Function.support (fun z : X × Y => ψ z.1 * θ z.2)
      = Function.support ψ ×ˢ Function.support θ := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, mul_ne_zero_iff]
  rw [tsupport, tsupport, tsupport, hsupp, closure_prod_eq]

end CKN
