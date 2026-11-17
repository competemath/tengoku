/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Open
import Tengoku.Seed.Topology.Instances.CantorSet

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Baire-space parameters for universal relations

Finite universal relations only need a sequence of binary choices, so Cantor parameters suffice.
At a countable limit level, a parameter must additionally select arbitrary natural-number codes for
lower ordinal levels. Baire space is the appropriate parameter space.

This file packages a homeomorphism between Baire space and a countable product of copies of itself,
head-tail coding for each component, an indexed section-union operation, and a universal open
relation with Baire parameters. Ordinal-level complexity theorems are kept in a later module.
-/

open Set TopologicalSpace

universe u

namespace DescriptiveSetTheory

variable {X : Type u}

/-- Baire space is homeomorphic to a countable product of copies of itself.-/
def baireSpaceHomeomorphNatToBaireSpace : (ℕ → ℕ) ≃ₜ (ℕ → ℕ → ℕ) :=
  (Homeomorph.piCongrLeft Nat.pairEquiv.symm).trans Homeomorph.piCurry

/-- Unpack one Baire parameter into its `n`th Baire component.-/
def baireUnpack (p : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
  baireSpaceHomeomorphNatToBaireSpace p n

/-- Pack a sequence of Baire parameters into one parameter.-/
def bairePack (p : ℕ → ℕ → ℕ) : ℕ → ℕ :=
  baireSpaceHomeomorphNatToBaireSpace.symm p

/-- Unpacking a packed sequence recovers every component.
@isnad1 id=eq.0h2v.s4.7c40de20f694 from=translated src=- shape=76dfb138 vocab=3e350e4a
-/
@[simp] theorem baireUnpack_pack (p : ℕ → ℕ → ℕ) (n : ℕ) :
    baireUnpack (bairePack p) n = p n := by
  simp [baireUnpack, bairePack]

/-- Packing the components of a parameter recovers that parameter.
@isnad1 id=eq.0h1v.s3.073a86a4cd90 from=translated src=- shape=708477eb vocab=3e350e4a
-/
@[simp] theorem bairePack_unpack (p : ℕ → ℕ) :
    bairePack (fun n => baireUnpack p n) = p := by
  simp [baireUnpack, bairePack]

/-- Prefix a natural-number selector to a Baire parameter.-/
def baireCons (k : ℕ) (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => p n

/-- The selector stored at the head of a Baire component.-/
def baireHead (p : ℕ → ℕ) : ℕ :=
  p 0

/-- The parameter payload following the head selector.-/
def baireTail (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  p (n + 1)

/-- The head of a prefixed Baire parameter is its selector.
@isnad1 id=eq.0h2v.s3.d14a51c7633b from=translated src=- shape=38780f62 vocab=e824dc2c
-/
@[simp] theorem baireHead_cons (k : ℕ) (p : ℕ → ℕ) : baireHead (baireCons k p) = k :=
  rfl

/-- The tail of a prefixed Baire parameter is its payload.
@isnad1 id=eq.0h2v.s3.77c0118fdbc2 from=translated src=- shape=3f5e293d vocab=6da0da8a
-/
@[simp] theorem baireTail_cons (k : ℕ) (p : ℕ → ℕ) : baireTail (baireCons k p) = p := by
  ext n
  rfl

/-- Each component of Baire-space unpacking is continuous.
@isnad1 id=continuo.0h1v.s5.9cc4a2f0c1a6 from=translated src=- shape=c976cbf0 vocab=4a39d54e
-/
theorem continuous_baireUnpack (n : ℕ) : Continuous (fun p => baireUnpack p n) :=
  (continuous_apply n).comp baireSpaceHomeomorphNatToBaireSpace.continuous

/-- The head selector is continuous.
@isnad1 id=continuo.0h0v.s3.b16393539214 from=translated src=- shape=88687477 vocab=d662d12c
-/
theorem continuous_baireHead : Continuous baireHead :=
  continuous_apply 0

/-- Removing the head selector is continuous.
@isnad1 id=continuo.0h0v.s4.b9051096d256 from=translated src=- shape=3b95f885 vocab=4396124a
-/
theorem continuous_baireTail : Continuous baireTail :=
  continuous_pi fun n => continuous_apply (n + 1)

/-- Prefixing a fixed selector is continuous in the payload.
@isnad1 id=continuo.0h1v.s4.833761f6b3ad from=translated src=- shape=56c8a417 vocab=877d211c
-/
theorem continuous_baireCons (k : ℕ) : Continuous (baireCons k) := by
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply n

/-- Extract the payload of component `n` from the parameter coordinate of a product.-/
def baireUnpackProd (n : ℕ) (q : (ℕ → ℕ) × X) : (ℕ → ℕ) × X :=
  (baireTail (baireUnpack q.1 n), q.2)

/-- Payload extraction from a parameter-object product is continuous.
@isnad1 id=continuo.0h2v.s5.9f0b131cc4a0 from=translated src=- shape=6c7f37f2 vocab=f4d1a996
-/
theorem continuous_baireUnpackProd [TopologicalSpace X] (n : ℕ) :
    Continuous (baireUnpackProd (X := X) n) :=
  (continuous_baireTail.comp ((continuous_baireUnpack n).comp continuous_fst)).prodMk
    continuous_snd

/-- The clopen product cylinder where component `n` carries selector `k`.-/
def baireSelector (n k : ℕ) : Set ((ℕ → ℕ) × X) :=
  {q | baireHead (baireUnpack q.1 n) = k}

/-- Selector cylinders are open.
@isnad1 id=isopen.0h3v.s5.705cd0796f68 from=translated src=- shape=d7c0615b vocab=77370114
-/
theorem isOpen_baireSelector [TopologicalSpace X] (n k : ℕ) :
    IsOpen (baireSelector (X := X) n k) := by
  change IsOpen ((fun q : (ℕ → ℕ) × X => baireHead (baireUnpack q.1 n)) ⁻¹' {k})
  exact (isOpen_discrete {k}).preimage
    (continuous_baireHead.comp ((continuous_baireUnpack n).comp continuous_fst))

/-- Selector cylinders are closed.
@isnad1 id=isclosed.0h3v.s5.db6e2ee9acb3 from=translated src=- shape=d7c0615b vocab=1539b902
-/
theorem isClosed_baireSelector [TopologicalSpace X] (n k : ℕ) :
    IsClosed (baireSelector (X := X) n k) := by
  change IsClosed ((fun q : (ℕ → ℕ) × X => baireHead (baireUnpack q.1 n)) ⁻¹' {k})
  exact (isClosed_discrete {k}).preimage
    (continuous_baireHead.comp ((continuous_baireUnpack n).comp continuous_fst))

/-- Union sections selected by the heads of countably many unpacked Baire components.-/
def baireIndexedIUnion (U : ℕ → Set ((ℕ → ℕ) × X)) : Set ((ℕ → ℕ) × X) :=
  {q | ∃ n, baireUnpackProd n q ∈ U (baireHead (baireUnpack q.1 n))}

/-- The indexed relation is a countable union over component and selector indices.
@isnad1 id=eq.0h2v.s6.e19360048082 from=translated src=- shape=5b8a35e2 vocab=dc2e6a63
-/
theorem baireIndexedIUnion_eq_iUnion (U : ℕ → Set ((ℕ → ℕ) × X)) :
    baireIndexedIUnion U =
      ⋃ n, ⋃ k, baireSelector n k ∩ baireUnpackProd n ⁻¹' U k := by
  ext q
  simp [baireIndexedIUnion, baireSelector]

/-- A section of the indexed relation is the union of the selected payload sections.
@isnad1 id=eq.0h3v.s5.80926ef2e4da from=translated src=- shape=864fc025 vocab=7639d741
-/
theorem verticalSection_baireIndexedIUnion (U : ℕ → Set ((ℕ → ℕ) × X)) (p : ℕ → ℕ) :
    verticalSection (baireIndexedIUnion U) p =
      ⋃ n, verticalSection (U (baireHead (baireUnpack p n))) (baireTail (baireUnpack p n)) := by
  ext x
  simp [verticalSection, baireIndexedIUnion, baireUnpackProd]

/-- The open relation induced by a basis sequence, now using Baire parameters.-/
def baireParameterUniversalOpen (b : ℕ → Set X) : Set ((ℕ → ℕ) × X) :=
  {q | ∃ n, q.1 n = 1 ∧ q.2 ∈ b n}

/-- A sequence of open sets produces an open relation with Baire parameters.
@isnad1 id=isopen.1h2v.s5.11dfd61ca632 from=translated src=- shape=7bf19150 vocab=4af30c6c
-/
theorem isOpen_baireParameterUniversalOpen [TopologicalSpace X] {b : ℕ → Set X}
    (hb : ∀ n, IsOpen (b n)) : IsOpen (baireParameterUniversalOpen b) := by
  rw [show baireParameterUniversalOpen b = ⋃ n, {p : ℕ → ℕ | p n = 1} ×ˢ b n by
    ext q
    simp [baireParameterUniversalOpen]]
  apply isOpen_iUnion
  intro n
  exact ((isOpen_discrete {1}).preimage (continuous_apply n)).prod (hb n)

/-- The canonical Baire parameter selecting all basis sets contained in `s`.-/
noncomputable def baireParameterUniversalOpenCode (b : ℕ → Set X) (s : Set X) : ℕ → ℕ :=
  by
    classical
    exact fun n => if b n ⊆ s then 1 else 0

/-- The canonical parameter selects exactly the basis sets contained in `s`.
@isnad1 id=iff.0h4v.s5.ac212e660bc8 from=translated src=- shape=a482bcc9 vocab=8a4a2eb3
-/
theorem baireParameterUniversalOpenCode_apply_iff (b : ℕ → Set X) (s : Set X) (n : ℕ) :
    baireParameterUniversalOpenCode b s n = 1 ↔ b n ⊆ s := by
  classical
  simp [baireParameterUniversalOpenCode]

/-- A natural-number-indexed basis produces a universal open relation with Baire parameters.
@isnad1 id=isuniver.1h2v.s4.b95b9a67d5c6 from=translated src=- shape=b2bcecd1 vocab=9d637f92
-/
theorem isUniversalFor_baireParameterUniversalOpen [TopologicalSpace X] {b : ℕ → Set X}
    (hb : IsTopologicalBasis (Set.range b)) :
    IsUniversalFor IsOpen (baireParameterUniversalOpen b) := by
  intro s
  constructor
  · intro hs
    refine ⟨baireParameterUniversalOpenCode b s, Set.Subset.antisymm ?_ ?_⟩
    · rintro x ⟨n, hn, hxn⟩
      exact (baireParameterUniversalOpenCode_apply_iff b s n).1 hn hxn
    · intro x hx
      obtain ⟨u, hu, hxu, hus⟩ := hb.exists_subset_of_mem_open hx hs
      obtain ⟨n, rfl⟩ := hu
      exact ⟨n, (baireParameterUniversalOpenCode_apply_iff b s n).2 hus, hxu⟩
  · rintro ⟨p, rfl⟩
    have hbo : ∀ n, IsOpen (b n) := fun n => hb.isOpen (Set.mem_range_self n)
    exact (isOpen_baireParameterUniversalOpen hbo).preimage
      (continuous_const.prodMk continuous_id)

end DescriptiveSetTheory
