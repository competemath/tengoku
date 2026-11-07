/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Data.Finset.Image
import Tengoku.Tnlean.TNLean.QCA.LocalAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-region translations for one-dimensional spin chains

For a finite region \(\Lambda \subset \mathbb Z\) and a lattice displacement \(a\), this file
defines the translated region \(\Lambda+a\), the induced equivalences of sites and configurations,
and the corresponding star-algebra equivalence from \(\mathcal A_\Lambda\) to
\(\mathcal A_{\Lambda+a}\). The finite-region translation commutes with the canonical inclusions
of local observable algebras.

This file concerns only finite regions. It does not define translations of algebraic-local or
quasi-local observables, finite propagation, or quantum cellular automata.

## Main definitions

* `SpinChain.translateRegion` — translation of a finite region of \(\mathbb Z\).
* `SpinChain.Config.translation` — the induced equivalence of spin configurations.
* `SpinChain.localTranslation` — translation of a finite-region local observable algebra.

## Main results

* `SpinChain.translateRegion_zero` — translation by zero fixes a region.
* `SpinChain.translateRegion_add` — successive region translations add their displacements.
* `SpinChain.localTranslation_norm` — finite-region translations preserve the operator norm.
* `SpinChain.localTranslation_isometry` — finite-region translations are operator-norm isometries.
* `SpinChain.localTranslation_localInclusion` — finite-region translations commute with canonical
  local inclusions.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2292--2298.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

namespace SpinChain

/-- The translated region \(\Lambda+a\) for a finite lattice region \(\Lambda\subset\mathbb Z\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.-/
abbrev translateRegion (a : ℤ) (Λ : Finset ℤ) : Finset ℤ :=
  Λ.map (Equiv.addRight a).toEmbedding

/-- Membership in \(\Lambda+a\) is membership in \(\Lambda\) after subtracting \(a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=iff.0h3v.s5.afe944233a29 from=translated src=- shape=ce3f0ec7 vocab=9e1d3b35
-/
@[simp]
lemma mem_translateRegion (a : ℤ) (Λ : Finset ℤ) (i : ℤ) :
    i ∈ translateRegion a Λ ↔ i - a ∈ Λ := by
  simp only [translateRegion, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro hi
    exact ⟨i - a, hi, by simp⟩

/-- A site \(i+a\) lies in \(\Lambda+a\) exactly when \(i\) lies in \(\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=iff.0h3v.s5.effef2c6c9ec from=translated src=- shape=1656c4f1 vocab=72827849
-/
@[simp]
lemma mem_translateRegion_add (a : ℤ) (Λ : Finset ℤ) (i : ℤ) :
    i + a ∈ translateRegion a Λ ↔ i ∈ Λ := by
  simp

/-- Translation by zero fixes every finite lattice region.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h1v.s3.689131a3d96a from=translated src=- shape=14b1f50a vocab=70efdf9f
-/
@[simp]
lemma translateRegion_zero (Λ : Finset ℤ) : translateRegion 0 Λ = Λ := by
  change Λ.map (Equiv.addRight 0).toEmbedding = Λ
  rw [show (Equiv.addRight 0).toEmbedding = Function.Embedding.refl ℤ by
    ext i
    simp]
  exact Finset.map_refl

/-- Successive finite-region translations add their lattice displacements.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h3v.s4.75d34fa060e8 from=translated src=- shape=59b6b5c3 vocab=7d3ee66e
-/
lemma translateRegion_add (a b : ℤ) (Λ : Finset ℤ) :
    translateRegion b (translateRegion a Λ) = translateRegion (a + b) Λ := by
  ext i
  simp only [mem_translateRegion]
  ring_nf

/-- Translation preserves inclusion of finite lattice regions.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=le.1h3v.s5.e301010b7863 from=translated src=- shape=0b1fbad5 vocab=95542bfa
-/
lemma translateRegion_mono (a : ℤ) {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    translateRegion a Λ ⊆ translateRegion a Γ := by
  intro i hi
  simpa only [mem_translateRegion] using h (by simpa only [mem_translateRegion] using hi)

/-- The site equivalence sends \(i\) to \(i+a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h3v.s8.95cb7814c7c8 from=translated src=- shape=baa99c41 vocab=66888846
-/
@[simp]
lemma siteTranslation_apply_val (a : ℤ) (Λ : Finset ℤ) (i : Λ) :
    (Finset.equivMap (Equiv.addRight a).toEmbedding Λ i : ℤ) = i + a := by
  exact Finset.equivMap_apply_coe (Equiv.addRight a).toEmbedding Λ i

/-- The inverse site equivalence sends \(i\) to \(i-a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h3v.s8.41ac00108742 from=translated src=- shape=1a4ebc76 vocab=e7df1665
-/
@[simp]
lemma siteTranslation_symm_apply_val (a : ℤ) (Λ : Finset ℤ)
    (i : translateRegion a Λ) :
    ((Finset.equivMap (Equiv.addRight a).toEmbedding Λ).symm i : ℤ) = i - a := by
  have h := congrArg Subtype.val
    ((Finset.equivMap (Equiv.addRight a).toEmbedding Λ).apply_symm_apply i)
  change ((Finset.equivMap (Equiv.addRight a).toEmbedding Λ).symm i : ℤ) + a = i at h
  omega

/-- Translation by zero fixes the underlying value of every site.

This value-level formulation avoids transporting between propositionally equal subtype indices.
Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h2v.s8.60e8ea1488d6 from=translated src=- shape=9405e530 vocab=1eb4fc5f
-/
@[simp]
lemma siteTranslation_zero (Λ : Finset ℤ) (i : Λ) :
    (Finset.equivMap (Equiv.addRight 0).toEmbedding Λ i : ℤ) = i := by
  simp

/-- Successive site translations agree with translation by the sum after coercion to \(\mathbb Z\).

This value-level formulation avoids transporting between propositionally equal subtype indices.
Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h4v.s9.6f9706e63814 from=translated src=- shape=d2bebbba vocab=2bebe205
-/
lemma siteTranslation_add (a b : ℤ) (Λ : Finset ℤ) (i : Λ) :
    (Finset.equivMap (Equiv.addRight b).toEmbedding (translateRegion a Λ)
        (Finset.equivMap (Equiv.addRight a).toEmbedding Λ i) : ℤ) =
      (Finset.equivMap (Equiv.addRight (a + b)).toEmbedding Λ i : ℤ) := by
  change (i : ℤ) + a + b = (i : ℤ) + (a + b)
  exact add_assoc (i : ℤ) a b

namespace Config

/-- Relabelling configurations by the lattice translation \(i\mapsto i+a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.-/
noncomputable def translation (d : ℕ) (a : ℤ) (Λ : Finset ℤ) :
    Config d Λ ≃ Config d (translateRegion a Λ) :=
  (Finset.equivMap (Equiv.addRight a).toEmbedding Λ).arrowCongr (Equiv.refl (Fin d))

/-- Evaluation of a translated configuration at a site of \(\Lambda+a\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h5v.s8.841640613360 from=translated src=- shape=d679d0bb vocab=1780cdb0
-/
@[simp]
lemma translation_apply (d : ℕ) (a : ℤ) (Λ : Finset ℤ)
    (x : Config d Λ) (i : translateRegion a Λ) :
    translation d a Λ x i =
      x ((Finset.equivMap (Equiv.addRight a).toEmbedding Λ).symm i) := rfl

/-- Evaluation of the inverse-translated configuration at a site of \(\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h5v.s8.8e5eb1cf99ca from=translated src=- shape=13cdb815 vocab=1780cdb0
-/
@[simp]
lemma translation_symm_apply (d : ℕ) (a : ℤ) (Λ : Finset ℤ)
    (x : Config d (translateRegion a Λ)) (i : Λ) :
    (translation d a Λ).symm x i =
      x (Finset.equivMap (Equiv.addRight a).toEmbedding Λ i) := rfl

/-- A translated configuration evaluated at the corresponding translated site has its original
value.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h5v.s8.85c47a0f5159 from=translated src=- shape=7ce912e6 vocab=e62bd40e
-/
@[simp]
lemma translation_apply_siteTranslation (d : ℕ) (a : ℤ) (Λ : Finset ℤ)
    (x : Config d Λ) (i : Λ) :
    translation d a Λ x (Finset.equivMap (Equiv.addRight a).toEmbedding Λ i) = x i := by
  rw [translation_apply, Equiv.symm_apply_apply]

/-- Translation by zero fixes every configuration when evaluated at corresponding sites.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h4v.s8.4242333ce377 from=translated src=- shape=087eeef6 vocab=e62bd40e
-/
@[simp]
lemma translation_zero (d : ℕ) (Λ : Finset ℤ) (x : Config d Λ) (i : Λ) :
    translation d 0 Λ x (Finset.equivMap (Equiv.addRight 0).toEmbedding Λ i) = x i := by
  simp

/-- Successive configuration translations agree pointwise with translation by the sum.

The two sides are evaluated at the sites obtained by their respective site translations, avoiding
transport between propositionally equal configuration types.
Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h6v.s10.4b327db64de7 from=translated src=- shape=c89ac0d8 vocab=786d9cc4
-/
lemma translation_add (d : ℕ) (a b : ℤ) (Λ : Finset ℤ) (x : Config d Λ) (i : Λ) :
    translation d b (translateRegion a Λ) (translation d a Λ x)
        (Finset.equivMap (Equiv.addRight b).toEmbedding (translateRegion a Λ)
          (Finset.equivMap (Equiv.addRight a).toEmbedding Λ i)) =
      translation d (a + b) Λ x
        (Finset.equivMap (Equiv.addRight (a + b)).toEmbedding Λ i) := by
  simp only [translation_apply, Equiv.symm_apply_apply]

end Config

/-- The finite-region translation
\(\mathcal A_\Lambda\simeq\mathcal A_{\Lambda+a}\), obtained by reindexing configurations.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.-/
noncomputable def localTranslation (d : ℕ) (a : ℤ) (Λ : Finset ℤ) :
    LocalAlgebra d Λ ≃⋆ₐ[ℂ] LocalAlgebra d (translateRegion a Λ) :=
  CStarMatrix.reindexₐ ℂ ℂ (Config.translation d a Λ)

/-- Entrywise evaluation of the finite-region translation of a local observable.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h6v.s8.34da3f9e1b4b from=translated src=- shape=17a35717 vocab=ebcadcf6
-/
@[simp]
lemma localTranslation_apply (d : ℕ) (a : ℤ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) (x y : Config d (translateRegion a Λ)) :
    localTranslation d a Λ A x y =
      A ((Config.translation d a Λ).symm x) ((Config.translation d a Λ).symm y) := rfl

open scoped ComplexOrder in
/-- Finite-region translation preserves the C⋆ operator norm.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the quasi-local algebra
and its lattice translation.
@isnad1 id=eq.0h4v.s8.15f06fc97835 from=translated src=- shape=2a269290 vocab=e6384936
-/
lemma localTranslation_norm (d : ℕ) (a : ℤ) (Λ : Finset ℤ) (A : LocalAlgebra d Λ) :
    ‖localTranslation d a Λ A‖ = ‖A‖ := by
  exact StarAlgEquiv.norm_map (localTranslation d a Λ) A

open scoped ComplexOrder in
/-- Finite-region translation is an operator-norm isometry.

Context: arXiv:1703.09188, Appendix, lines 2292--2298, which introduce the quasi-local algebra
and its lattice translation.
@isnad1 id=isometry.0h3v.s8.7adf535ff057 from=translated src=- shape=8526beed vocab=43772f0d
-/
lemma localTranslation_isometry (d : ℕ) (a : ℤ) (Λ : Finset ℤ) :
    Isometry (localTranslation d a Λ) := by
  exact StarAlgEquiv.isometry (localTranslation d a Λ)

/-- A translated local observable evaluated on translated configurations has its original matrix
entry.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h6v.s8.d379ea9f1010 from=translated src=- shape=01312abd vocab=1818fe64
-/
@[simp]
lemma localTranslation_apply_translation (d : ℕ) (a : ℤ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) (x y : Config d Λ) :
    localTranslation d a Λ A (Config.translation d a Λ x) (Config.translation d a Λ y) =
      A x y := by
  simp

/-- Translation by zero fixes every local observable entry on corresponding configurations.

Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h5v.s9.5c8504cc5cfc from=translated src=- shape=f59ccdea vocab=1818fe64
-/
@[simp]
lemma localTranslation_zero (d : ℕ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) (x y : Config d Λ) :
    localTranslation d 0 Λ A (Config.translation d 0 Λ x) (Config.translation d 0 Λ y) =
      A x y := by
  simp

/-- Successive finite-region local translations agree entrywise with translation by the sum.

The two sides are evaluated on configurations obtained by their respective configuration
translations, avoiding transport between propositionally equal matrix types.
Source: arXiv:1703.09188, Appendix, lines 2292--2298.
@isnad1 id=eq.0h7v.s10.c595ca2b6ba1 from=translated src=- shape=93c84f9c vocab=5a5a5579
-/
lemma localTranslation_add (d : ℕ) (a b : ℤ) (Λ : Finset ℤ)
    (A : LocalAlgebra d Λ) (x y : Config d Λ) :
    localTranslation d b (translateRegion a Λ) (localTranslation d a Λ A)
        (Config.translation d b (translateRegion a Λ) (Config.translation d a Λ x))
        (Config.translation d b (translateRegion a Λ) (Config.translation d a Λ y)) =
      localTranslation d (a + b) Λ A
        (Config.translation d (a + b) Λ x) (Config.translation d (a + b) Λ y) := by
  simp

end SpinChain
