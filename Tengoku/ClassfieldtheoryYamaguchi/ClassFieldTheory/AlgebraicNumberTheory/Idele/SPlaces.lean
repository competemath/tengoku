/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Topology
import Tengoku.Seed.RingTheory.DedekindDomain.SInteger

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.ClassfieldtheoryYamaguchi end Tengoku.ClassfieldtheoryYamaguchi open Tengoku.ClassfieldtheoryYamaguchi
set_option autoImplicit false

/-!
# Ideles and units with finite support

This file formalizes finite-support objects for ideles and units. Since every
archimedean place is always included, a finite set
`S` below records only its finite places.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroup

/-- The finite ideles that are integral units away from `S`.-/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, v ∉ S →
    a v ∈ (v.adicCompletionIntegers K).units}
  one_mem' _ _ := Submonoid.one_mem _
  mul_mem' ha hb v hv := Submonoid.mul_mem _
    (ha v hv) (hb v hv)
  inv_mem' ha v hv := Subgroup.inv_mem _
    (ha v hv)

/--
@isnad1 id=iff.0h3v.s12.040ed7211cb0 from=translated src=- shape=da72d5d2 vocab=2d300e8a
-/
@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

/--
@isnad1 id=le.1h3v.s11.3b04a56f9815 from=translated src=- shape=9fbe3fda vocab=c2802b28
-/
theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T := by
  intro a ha v hv
  exact ha v (fun h => hv (hST h))

/--
@isnad1 id=mem.0h2v.s12.e063624002af from=translated src=- shape=cb7bb7a2 vocab=26c58eb1
-/
theorem mem_supportedAt_nonLocalUnits
    (a : FiniteIdeleGroup K) :
    a ∈ supportedAt (K := K)
      {v | a v ∉ (v.adicCompletionIntegers K).units} := by
  intro v hv
  simpa using hv

/-- Every finite idele is supported at some finite set of finite places.
@isnad1 id=ex.0h2v.s11.e1c00b96d15c from=translated src=- shape=d3474a53 vocab=91b05dcf
-/
theorem exists_finset_supportedAt (a : FiniteIdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) := by
  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | a v ∉ (v.adicCompletionIntegers K).units}
  have hT : T.Finite := Filter.eventually_cofinite.mp a.2
  exact ⟨hT.toFinset, by
    rw [Set.Finite.coe_toFinset]
    exact mem_supportedAt_nonLocalUnits a⟩

/-- The union of the finite-support subgroups is the full finite idele
group.
@isnad1 id=eq.0h1v.s13.8ba79b1f1002 from=translated src=- shape=92ba2d3b vocab=469f7f12
-/
theorem iSup_finset_supportedAt :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 K)),
      supportedAt (K := K) (S : Set _) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨S, ha⟩ := exists_finset_supportedAt a
  exact Subgroup.mem_iSup_of_mem S ha

/-- The everywhere-integral subgroup is the subgroup supported at the empty
set.
@isnad1 id=eq.0h1v.s9.52cb6e6c5040 from=translated src=- shape=f9b15631 vocab=abdfb2b0
-/
theorem supportedAt_empty :
    supportedAt (K := K)
      (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      integralSubgroup (K := K) :=
  by
    ext a
    simp only [mem_supportedAt_iff, Set.mem_empty_iff_false,
      not_false_eq_true, forall_const, mem_integralSubgroup_iff]

/-- For a finite set `S`, the `S`-finite-ideles form an open subgroup.
@isnad1 id=isopen.0h2v.s11.a5a3ec93f3f1 from=translated src=- shape=9abac219 vocab=ec16ed54
-/
theorem isOpen_supportedAt (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (FiniteIdeleGroup K)) : Set (FiniteIdeleGroup K)) := by
  change IsOpen {a : FiniteIdeleGroup K | ∀ v, v ∉ (S : Set _) →
    a v ∈ (v.adicCompletionIntegers K).units}
  exact RestrictedProduct.isOpen_forall_imp_mem
    (fun v => isOpen_finiteLocalUnits K v)

end Tengoku.ClassfieldtheoryYamaguchi.FiniteIdeleGroup

namespace Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup

/-- The group `I_K^S`, with all infinite places included and finite
components integral away from `S`.-/
def supportedAt (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.supportedAt S)

/--
@isnad1 id=iff.0h3v.s12.b42aec063cfb from=translated src=- shape=e492bda4 vocab=a0d7495d
-/
@[simp]
theorem mem_supportedAt_iff
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (a : IdeleGroup K) :
    a ∈ supportedAt (K := K) S ↔
      ∀ v, v ∉ S →
        a.2 v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

/--
@isnad1 id=le.1h3v.s11.9ff1e6566b04 from=translated src=- shape=9fbe3fda vocab=69552f50
-/
theorem supportedAt_mono {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hST : S ⊆ T) :
    supportedAt (K := K) S ≤ supportedAt (K := K) T :=
  Subgroup.comap_mono
    (FiniteIdeleGroup.supportedAt_mono hST)

/-- Every idele lies in `I_K^S` for some finite set `S`.
@isnad1 id=ex.0h2v.s11.f41ee3295fb8 from=translated src=- shape=d3474a53 vocab=a4a5a031
-/
theorem exists_finset_supportedAt (a : IdeleGroup K) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      a ∈ supportedAt (K := K) (S : Set _) :=
  FiniteIdeleGroup.exists_finset_supportedAt a.2

/--
@isnad1 id=eq.0h1v.s13.d4b55997fd10 from=translated src=- shape=92ba2d3b vocab=412c24f2
-/
theorem iSup_finset_supportedAt :
    ⨆ S : Finset (HeightOneSpectrum (𝓞 K)),
      supportedAt (K := K) (S : Set _) = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨S, ha⟩ := exists_finset_supportedAt a
  exact Subgroup.mem_iSup_of_mem S ha

/--
@isnad1 id=eq.0h1v.s9.d487086a3bb2 from=translated src=- shape=f9b15631 vocab=00c96c64
-/
theorem supportedAt_empty :
    supportedAt (K := K)
      (∅ : Set (HeightOneSpectrum (𝓞 K))) =
      integralAtFinitePlaces (K := K) :=
  by
    ext a
    simp only [mem_supportedAt_iff, Set.mem_empty_iff_false,
      not_false_eq_true, forall_const]
    rfl

/--
@isnad1 id=isopen.0h2v.s11.fc0998319d00 from=translated src=- shape=9abac219 vocab=05537a29
-/
theorem isOpen_supportedAt
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsOpen
      ((supportedAt (K := K) (S : Set _) :
        Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) :=
  (FiniteIdeleGroup.isOpen_supportedAt S).preimage continuous_snd

end Tengoku.ClassfieldtheoryYamaguchi.IdeleGroup

/-- The group of `S`-units of `K`, for a finite set of finite places.
All infinite places are understood to lie in `S`.-/
abbrev _root_.Tengoku.ClassfieldtheoryYamaguchi.SUnitGroup
    (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (S : Set (HeightOneSpectrum (𝓞 K))).unit K

/--
@isnad1 id=iff.0h3v.s8.fbe5f26134bc from=translated src=- shape=7cc6aa33 vocab=bc08d15a
-/
@[simp]
theorem _root_.Tengoku.ClassfieldtheoryYamaguchi.mem_SUnitGroup_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    x ∈ SUnitGroup (K := K) S ↔
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        v.valuation K x = 1 :=
  Iff.rfl
-- Tengoku: root names of this library moved to Tengoku.ClassfieldtheoryYamaguchi so they do not collide with other libraries (generated)
