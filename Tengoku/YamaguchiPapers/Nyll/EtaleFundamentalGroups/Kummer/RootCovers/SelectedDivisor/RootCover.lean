/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularity
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.BaseChange
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.Kummer.Obstructions.LocalDerivative
import Tengoku.Seed.RingTheory.DiscreteValuationRing.TFAE
import Tengoku.Seed.RingTheory.Filtration
import Tengoku.Seed.RingTheory.TensorProduct.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A selected divisor under a one-root Kummer cover

Let `[x, y]` be a regular parameter pair generating the maximal ideal of a
Noetherian local domain.  After adjoining a positive-degree root of `x`, this
file proves that the cover is a regular local domain, that the image of `y`
remains prime, and that its quotient is again both a domain and a regular
local ring.

The proof does not assume primality of `y`.  It first produces the domain
structure on `R ⧸ (y)` from regularity of the residual parameter `x`; the
cover quotient is then identified with the corresponding base-changed root
cover.  Finally, faithful flatness preserves regularity of `y`, and Krull
intersection upgrades the regular local cover to a domain.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped Pointwise
open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

/-- Modding out the second member of a regular parameter pair leaves the first
member regular and generating the quotient maximal ideal.-/
theorem regular_quotient_parameter_of_regular_pair
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let I : Ideal R := Ideal.span {y}
    let S := R ⧸ I
    IsRegular S [Ideal.Quotient.mk I x] ∧
      Ideal.ofList [Ideal.Quotient.mk I x] =
        (maximalIdeal R).map (Ideal.Quotient.mk I) := by
  dsimp only
  let I : Ideal R := Ideal.span {y}
  let S := R ⧸ I
  have hyMem : y ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span (List.mem_cons_of_mem x List.mem_cons_self)
  have hIle : I ≤ maximalIdeal R := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    change y ∈ maximalIdeal R
    exact hyMem
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hregYX : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hspan_smul : y • (⊤ : Submodule R R) = (I : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul]
    change I • (⊤ : Submodule R R) = (I : Submodule R R)
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hxregQ : IsSMulRegular (QuotSMulTop y R) x :=
    ((isRegular_cons_iff (QuotSMulTop y R) x []).mp
      ((isRegular_cons_iff R y [x]).mp hregYX).2).1
  have hxregS : IsSMulRegular S (Ideal.Quotient.mk I x) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro z hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hxmemI : x * r ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, smul_eq_mul] using hz
    have hxmem : x • r ∈ y • (⊤ : Submodule R R) := by
      rw [hspan_smul]
      simpa only [smul_eq_mul] using hxmemI
    have hrmem : r ∈ y • (⊤ : Submodule R R) :=
      (isSMulRegular_quotient_iff_mem_of_smul_mem
        (y • (⊤ : Submodule R R)) x).mp hxregQ r hxmem
    rw [hspan_smul] at hrmem
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hrmem
  have hregS : IsRegular S [Ideal.Quotient.mk I x] := by
    have hxmem : Ideal.Quotient.mk I x ∈ maximalIdeal S := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
        ← hgen, Ideal.map_ofList]
      apply Ideal.subset_span
      simp only [List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl rfl
    exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      (L := S) (by
        intro z hz
        simp only [List.mem_singleton] at hz
        subst z
        exact hxmem)
      ((isWeaklyRegular_singleton_iff S (Ideal.Quotient.mk I x)).mpr hxregS)
  have hgenS : Ideal.ofList [Ideal.Quotient.mk I x] =
      (maximalIdeal R).map (Ideal.Quotient.mk I) := by
    rw [← hgen, Ideal.map_ofList]
    simp [I]
  exact ⟨hregS, hgenS⟩

end EtaleFundamentalGroups.Kummer

end
