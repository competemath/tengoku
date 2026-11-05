/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.FiniteEtaleQuotientProductLift
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.IdempotentFactorProduct
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Purity.Local.FiniteEtaleQuotientLift
import Tengoku.Seed.RingTheory.Etale.Pi
import Tengoku.Seed.RingTheory.TensorProduct.Pi
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite étale algebras over quotients of complete local rings

A finite étale algebra over a quotient of a complete Noetherian local ring
splits into finitely many local factors.  Lifting those factors separately and
taking their product gives a finite étale algebra over the original ring whose
base change is the given algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u

/-- A finite family of finite étale lifts can be assembled into a single lift
by taking the product of the lifted algebras.-/
theorem exists_finiteEtale_product_lift
    {R B J : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Finite J]
    (D : J → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra B (D j)]
    (hlift : ∀ j, ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (B ⊗[R] C ≃ₐ[B] D j)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (B ⊗[R] C ≃ₐ[B] ∀ j, D j) := by
  classical
  let := Fintype.ofFinite J
  choose C hCcomm hCalgebra hCfinite hCetale hCequiv using hlift
  let (j : J) : CommRing (C j) := hCcomm j
  let (j : J) : Algebra R (C j) := hCalgebra j
  let (j : J) : Module.Finite R (C j) := hCfinite j
  let (j : J) : Algebra.Etale R (C j) := hCetale j
  refine ⟨∀ j, C j, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R B B C).trans
    (AlgEquiv.piCongrRight fun j ↦ Classical.choice (hCequiv j))

end EtaleFundamentalGroups

end
