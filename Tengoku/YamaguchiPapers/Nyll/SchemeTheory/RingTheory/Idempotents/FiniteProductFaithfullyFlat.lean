/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Algebra
import Tengoku.Seed.RingTheory.Flat.TorsionFree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Faithfully flat products over a Dedekind domain

A finite family of domain algebras over a Dedekind domain gives a faithfully
flat product when the structure maps are injective and their spectra cover
the base. This applies to finite affine covers of arithmetic schemes: the
prime over a given base point is pulled back along one product projection.
-/

namespace Module.FaithfullyFlat

universe u v w

/-- A finite family of domain algebras with injective structure maps and
jointly surjective spectra has faithfully flat product over a Dedekind domain.
@isnad1 id=faithful.2h3v.s8.4f30a8c4c778 from=translated src=- shape=b4af8ce3 vocab=0779a956
-/
theorem pi_of_dedekind_spectrum_cover
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    {ι : Type v} [Finite ι] (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)] [∀ i, Algebra R (A i)]
    (hinj : ∀ i, Function.Injective (algebraMap R (A i)))
    (hcover : ∀ p : PrimeSpectrum R,
      ∃ (i : ι) (q : PrimeSpectrum (A i)),
        PrimeSpectrum.comap (algebraMap R (A i)) q = p) :
    Module.FaithfullyFlat R (∀ i, A i) := by
  let : ∀ i, Module.IsTorsionFree R (A i) := fun i ↦
    Module.isTorsionFree_iff_algebraMap_injective.mpr (hinj i)
  apply Module.FaithfullyFlat.of_comap_surjective
  intro p
  obtain ⟨i, q, hq⟩ := hcover p
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) q, ?_⟩
  change PrimeSpectrum.comap (algebraMap R (A i)) q = p
  exact hq

end Module.FaithfullyFlat
