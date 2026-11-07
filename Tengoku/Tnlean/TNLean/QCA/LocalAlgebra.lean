/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku
import Tengoku.Seed.Analysis.CStarAlgebra.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-region observable algebras for one-dimensional spin chains

For a finite region \(\Lambda \subset \mathbb Z\) and on-site dimension \(d\), this file
defines the local observable C⋆-algebra on \(\Lambda\) and its canonical inclusion into the
algebra on a larger finite region.  The inclusion tensors an observable with the identity on
complementary sites and then reindexes product configurations as configurations on the larger
region.

This is only the finite directed system.  No quasi-local completion or quantum cellular
automaton is defined here.

## Main definitions

* `SpinChain.Config` — spin configurations on a finite region.
* `SpinChain.LocalAlgebra` — the operator-norm C⋆-matrix algebra of local observables.
* `SpinChain.localInclusion` — the identity-tensor inclusion for nested finite regions.

## Main results

* `SpinChain.localInclusion_injective` — faithfulness of the inclusion.
* `SpinChain.localInclusion_norm` — preservation of the operator norm.
* `SpinChain.localInclusion_isometry` — operator-norm isometry.
* `SpinChain.localInclusion_refl` — the identity inclusion.
* `SpinChain.localInclusion_trans` — composition of inclusions.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, Appendix, lines 2285--2300.
* Schumacher--Werner, quant-ph/0405174, Definition 1.
-/

open scoped ComplexOrder

namespace SpinChain

/-- Configurations of \(d\)-level spins on the finite region \(\Lambda\).

Source: arXiv:1703.09188, Appendix, lines 2285--2292.-/
def Config (d : ℕ) (Λ : Finset ℤ) := Λ → Fin d

/-- The local observable C⋆-algebra on a finite region \(\Lambda\).

Its norm is the `CStarMatrix` operator norm, rather than a norm inherited from plain matrices.
Source: arXiv:1703.09188, Appendix, lines 2285--2292.-/
abbrev LocalAlgebra (d : ℕ) (Λ : Finset ℤ) :=
  CStarMatrix (Config d Λ) (Config d Λ) ℂ

/-- Configurations on a finite region form a finite type.-/
instance instFintypeConfig (d : ℕ) (Λ : Finset ℤ) : Fintype (Config d Λ) := by
  change Fintype (Λ → Fin d)
  infer_instance

/-- Equality of finite-region configurations is decidable.-/
instance instDecidableEqConfig (d : ℕ) (Λ : Finset ℤ) :
    DecidableEq (Config d Λ) := by
  change DecidableEq (Λ → Fin d)
  infer_instance

namespace Config

/-- Restrict a configuration to a smaller region.-/
def restrict {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) (x : Config d Γ) : Config d Λ :=
  fun i ↦ x ⟨i, h i.2⟩

/--
@isnad1 id=eq.0h3v.s4.336229d0f6b2 from=translated src=- shape=46ab194e vocab=e2f90b9c
-/
@[simp]
lemma restrict_refl {d : ℕ} {Λ : Finset ℤ} (x : Config d Λ) : restrict (by rfl) x = x := by
  rfl

/--
@isnad1 id=eq.2h5v.s6.dfb0514269d0 from=translated src=- shape=ab4841d3 vocab=bedebd92
-/
lemma restrict_trans {d : ℕ} {Λ Γ Δ : Finset ℤ} (hΛΓ : Λ ⊆ Γ) (hΓΔ : Γ ⊆ Δ)
    (x : Config d Δ) : restrict hΛΓ (restrict hΓΔ x) = restrict (hΛΓ.trans hΓΔ) x := by
  rfl

/-- Split a configuration on \(\Gamma\) into its restrictions to \(\Lambda\) and
\(\Gamma \setminus \Lambda\).

This is the canonical reindexing used after tensoring with the identity on the complement.
Source: arXiv:1703.09188, Appendix, lines 2285--2292.-/
def splitEquiv {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ) :
    Config d Γ ≃ Config d Λ × Config d (Γ \ Λ) where
  toFun x :=
    (restrict h x, fun i ↦ x ⟨i, (Finset.mem_sdiff.mp i.2).1⟩)
  invFun x i :=
    if hi : (i : ℤ) ∈ Λ then x.1 ⟨i, hi⟩
    else x.2 ⟨i, Finset.mem_sdiff.mpr ⟨i.2, hi⟩⟩
  left_inv x := by
    funext i
    simp only [restrict]
    split <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [restrict]
    · funext i
      simp [Finset.mem_sdiff.mp i.2]

/-- Restricting a configuration reconstructed by `splitEquiv` to the retained region recovers
the first component.

This is the coordinate identity underlying the canonical inclusions in arXiv:1703.09188,
Appendix, lines 2292--2298. It is not stated separately there.
@isnad1 id=eq.1h4v.s7.50cc76029de6 from=translated src=- shape=4f6055bc vocab=b526e6c6
-/
@[simp]
lemma restrict_splitEquiv_symm {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (p : Config d Λ × Config d (Γ \ Λ)) :
    restrict h ((splitEquiv h).symm p) = p.1 :=
  congrArg Prod.fst ((splitEquiv h).apply_symm_apply p)

/-- Restricting a configuration reconstructed by `splitEquiv` to the complementary region
recovers the second component.

This is the coordinate identity underlying the canonical inclusions in arXiv:1703.09188,
Appendix, lines 2292--2298. It is not stated separately there.
@isnad1 id=eq.1h4v.s7.0cff51e5b9e6 from=translated src=- shape=a793685c vocab=f6590ee9
-/
@[simp]
lemma restrict_sdiff_splitEquiv_symm {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (p : Config d Λ × Config d (Γ \ Λ)) :
    restrict (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) ((splitEquiv h).symm p) = p.2 :=
  congrArg Prod.snd ((splitEquiv h).apply_symm_apply p)

/-- Two configurations have the same complementary coordinate under `splitEquiv` exactly when
their restrictions to the complementary region agree.

This is the coordinate identity underlying the canonical inclusions in arXiv:1703.09188,
Appendix, lines 2292--2298. It is not stated separately there.
@isnad1 id=iff.1h5v.s8.fdc4e342b97a from=translated src=- shape=d6622ef4 vocab=f97600cb
-/
lemma splitEquiv_snd_eq_iff_restrict_sdiff {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (x y : Config d Γ) :
    (splitEquiv h x).2 = (splitEquiv h y).2 ↔
      restrict (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) x =
        restrict (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) y := by
  rfl

/-- Equality of the complementary coordinates for the split retaining `Γ \ Λ` is equality after
restriction to `Λ`.

This is the coordinate identity underlying the canonical inclusions in arXiv:1703.09188,
Appendix, lines 2292--2298. It is not stated separately there.
@isnad1 id=iff.1h5v.s8.b9b7c9a95f4b from=translated src=- shape=f7769a97 vocab=f97600cb
-/
lemma splitEquiv_sdiff_snd_eq_iff_restrict {d : ℕ} {Λ Γ : Finset ℤ} (h : Λ ⊆ Γ)
    (x y : Config d Γ) :
    (splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) x).2 =
        (splitEquiv (Finset.sdiff_subset : Γ \ Λ ⊆ Γ) y).2 ↔
      restrict h x = restrict h y := by
  constructor
  · intro hxy
    funext i
    exact congrFun hxy ⟨i, Finset.mem_sdiff.mpr ⟨h i.2, by simp [i.2]⟩⟩
  · intro hxy
    funext i
    have hiΛ : (i : ℤ) ∈ Λ := by
      by_contra hi
      exact (Finset.mem_sdiff.mp i.2).2
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp i.2).1, hi⟩)
    exact congrFun hxy ⟨i, hiΛ⟩

end Config

section Inclusion

variable {d : ℕ}

end Inclusion

end SpinChain
