/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactor
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates on a complete-local chosen factor

The residue-lift classification identifies a chosen finite étale factor
`D / B` with `B ⊗[A] C`, where `C / A` is the explicit finite étale lift
of the actual residue extension.  This file reads that same equivalence in the
other direction: it equips `D` with the induced `C`-algebra structure and
identifies `D / C` with the iterated radical obtained from `B / A` by base
change.

The induced algebra structure is a named definition, not a global instance.
Consumers install it locally once, avoiding duplicate tensor-product tower
searches.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u

/-- The `C`-algebra structure on a chosen tensor factor transported by its
`B`-algebra equivalence.  This is deliberately not a global instance.-/
@[reducible]
noncomputable def tensorChosenFactorRightAlgebra
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) : Algebra C D :=
  ((e.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom).toAlgebra)

/-- Swapping the tensor factors turns the chosen-factor equivalence into a
`C`-algebra equivalence for the transported right-factor action.-/
noncomputable def tensorChosenFactorCommAlgEquiv
    {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra B D]
    (e : (B ⊗[A] C) ≃ₐ[B] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra e
    (C ⊗[A] B) ≃ₐ[C] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra e
  refine
    { toRingEquiv :=
        (Algebra.TensorProduct.comm A C B).toRingEquiv.trans e.toRingEquiv
      commutes' := ?_ }
  intro c
  rfl

namespace Kummer

/-- A tensor-trivialized chosen factor of an iterated radical is itself the
corresponding iterated radical over the finite residue lift.-/
noncomputable def iteratedRadicalChosenFactorAlgEquiv
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    [Algebra (iteratedRadical A r n a) D]
    (e : (iteratedRadical A r n a ⊗[A] C) ≃ₐ[iteratedRadical A r n a] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra e
    iteratedRadical C r n (fun i ↦ algebraMap A C (a i)) ≃ₐ[C] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra e
  exact
    (iteratedRadicalBaseChangeAlgEquiv n a).symm.trans
      (tensorChosenFactorCommAlgEquiv e)

end Kummer

end EtaleFundamentalGroups

end
