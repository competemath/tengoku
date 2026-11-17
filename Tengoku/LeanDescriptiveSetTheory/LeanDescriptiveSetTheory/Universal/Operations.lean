/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Open
import Tengoku.Seed.Topology.Instances.CantorSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operations on universal relations

Cantor space is homeomorphic to a countable product of copies of itself. This file uses that
homeomorphism to unpack one parameter into a sequence of parameters. Taking the union of the
corresponding vertical sections turns a universal `Pi0 (n + 1)` relation into a universal
`Sigma0 (n + 2)` relation. Complementation supplies the other half of the finite recursion.
-/

open Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

/-- Unpack one Cantor-space parameter into its `n`th Cantor-space component.-/
def cantorUnpack (p : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  cantorSpaceHomeomorphNatToCantorSpace p n

/-- Pack a sequence of Cantor-space parameters into one Cantor-space parameter.-/
def cantorPack (p : ℕ → ℕ → Bool) : ℕ → Bool :=
  cantorSpaceHomeomorphNatToCantorSpace.symm p

/-- Unpacking a packed sequence recovers every component.-/
@[simp] theorem cantorUnpack_pack (p : ℕ → ℕ → Bool) (n : ℕ) :
    cantorUnpack (cantorPack p) n = p n := by
  simp [cantorUnpack, cantorPack]

/-- Packing the components of one parameter recovers that parameter.-/
@[simp] theorem cantorPack_unpack (p : ℕ → Bool) :
    cantorPack (fun n => cantorUnpack p n) = p := by
  simp [cantorUnpack, cantorPack]

/-- Each component of the Cantor-space unpacking map is continuous.-/
theorem continuous_cantorUnpack (n : ℕ) : Continuous (fun p => cantorUnpack p n) :=
  (continuous_apply n).comp cantorSpaceHomeomorphNatToCantorSpace.continuous

/-- The Cantor-space packing map is continuous.-/
theorem continuous_cantorPack : Continuous cantorPack :=
  cantorSpaceHomeomorphNatToCantorSpace.symm.continuous

/-- Unpack the parameter coordinate of a parameter-object pair.-/
def cantorUnpackProd (n : ℕ) (q : (ℕ → Bool) × X) : (ℕ → Bool) × X :=
  (cantorUnpack q.1 n, q.2)

/-- Unpacking the parameter coordinate of a product is continuous.-/
theorem continuous_cantorUnpackProd [TopologicalSpace X] (n : ℕ) :
    Continuous (cantorUnpackProd (X := X) n) :=
  ((continuous_cantorUnpack n).comp continuous_fst).prodMk continuous_snd

/-- The relation whose section at `p` is the union of the sections at all components of `p`.-/
def cantorIUnion (U : Set ((ℕ → Bool) × X)) : Set ((ℕ → Bool) × X) :=
  {q | ∃ n, cantorUnpackProd n q ∈ U}

/-- `cantorIUnion` is a countable union of continuous preimages.-/
theorem cantorIUnion_eq_iUnion_preimage (U : Set ((ℕ → Bool) × X)) :
    cantorIUnion U = ⋃ n, cantorUnpackProd n ⁻¹' U := by
  ext q
  simp [cantorIUnion]

/-- A vertical section of `cantorIUnion U` is the union of the selected sections of `U`.-/
theorem verticalSection_cantorIUnion (U : Set ((ℕ → Bool) × X)) (p : ℕ → Bool) :
    verticalSection (cantorIUnion U) p = ⋃ n, verticalSection U (cantorUnpack p n) := by
  ext x
  simp [verticalSection, cantorIUnion, cantorUnpackProd]

/-- Complementing a universal additive relation produces a universal multiplicative relation.-/
theorem IsUniversalFor.compl_sigma0 [TopologicalSpace X] {n : ℕ}
    {U : Set ((ℕ → Bool) × X)} (hU : IsUniversalFor (Sigma0 n) U) :
    IsUniversalFor (Pi0 n) Uᶜ := by
  intro s
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := (hU sᶜ).1 ((sigma0_compl_iff_pi0 n s).2 hs)
    refine ⟨p, ?_⟩
    rw [verticalSection_compl, hp]
    simp
  · rintro ⟨p, hp⟩
    have hsection : Sigma0 n (verticalSection U p) := (hU _).2 ⟨p, rfl⟩
    have hcompl := hsection.compl
    rw [← verticalSection_compl U p, hp] at hcompl
    exact hcompl

/-- Countable section union raises a multiplicative universal relation by one additive level.-/
theorem Pi0.cantorIUnion [TopologicalSpace X] {n : ℕ} {U : Set ((ℕ → Bool) × X)}
    (hU : Pi0 (n + 1) U) : Sigma0 (n + 2) (cantorIUnion U) := by
  refine sigma0_succ_succ.2
    ⟨fun i => cantorUnpackProd i ⁻¹' U,
      fun i => hU.preimage (continuous_cantorUnpackProd i), ?_⟩
  exact cantorIUnion_eq_iUnion_preimage U

/-- Countable section union preserves completeness while raising the finite Borel level.-/
theorem IsUniversalFor.cantorIUnion [TopologicalSpace X] {n : ℕ}
    {U : Set ((ℕ → Bool) × X)} (hU : IsUniversalFor (Pi0 (n + 1)) U) :
    IsUniversalFor (Sigma0 (n + 2)) (cantorIUnion U) := by
  intro s
  constructor
  · intro hs
    obtain ⟨f, hf, rfl⟩ := sigma0_succ_succ.1 hs
    choose p hp using fun i => (hU (f i)).1 (hf i)
    refine ⟨cantorPack p, ?_⟩
    rw [verticalSection_cantorIUnion]
    simp_rw [cantorUnpack_pack, hp]
  · rintro ⟨p, rfl⟩
    refine sigma0_succ_succ.2
      ⟨fun i => verticalSection U (cantorUnpack p i), ?_, verticalSection_cantorIUnion U p⟩
    intro i
    exact (hU _).2 ⟨cantorUnpack p i, rfl⟩

end DescriptiveSetTheory
