/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.AclGeom.AclGeom.Correspondence.Moebius
import Tengoku.AclGeom.AclGeom.Curves.Rational

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Automorphisms of genus-zero function fields

Once `F = k(t)`, every `k`-automorphism sends `t` to another generator.
The two generators have degree one over one another, so the existing
bidegree-`(1,1)` correspondence theorem makes the new generator a
fractional-linear expression in `t`.  Transcendence forces the
coefficient determinant to be nonzero.

This is the genus-zero Möbius checkpoint in blueprint Lemma 8.4.

**Status:** proved for a supplied rational generator or genus-zero one-variable field.
`FixedPlaceAffine` uses the fractional-linear expression at a fixed pole; the actual
regular-affine scheme consumer derives its rationality inputs in `SchemeCurveGenus`.
The full source action classification remains open (#21).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A fractional-linear relation with transcendental output has
nonzero determinant.
@isnad1 id=ne.3h8v.s9.8fa7455fd52f from=translated src=- shape=47cb82d9 vocab=f6581cf6
-/
theorem moebius_det_ne_zero_of_transcendental {z w : F}
    (hw : Transcendental k w) {a b c d : k}
    (hden : algebraMap k F c * z + algebraMap k F d ≠ 0)
    (hrel : w * (algebraMap k F c * z + algebraMap k F d) =
      algebraMap k F a * z + algebraMap k F b) :
    a * d - b * c ≠ 0 := by
  intro hdet
  rcases eq_or_ne c 0 with hc | hc
  · have hd : d ≠ 0 := by
      intro hd
      apply hden
      rw [hc, hd, map_zero, zero_mul, add_zero]
    have ha : a = 0 := by
      rw [hc, mul_zero, sub_zero] at hdet
      exact (mul_eq_zero.1 hdet).resolve_right hd
    have hmapd : algebraMap k F d ≠ 0 := (map_ne_zero _).2 hd
    have hwconst : w = algebraMap k F (b / d) := by
      apply mul_right_cancel₀ hmapd
      calc
        w * algebraMap k F d = algebraMap k F b := by
          simpa [hc, ha] using hrel
        _ = algebraMap k F (b / d) * algebraMap k F d := by
          rw [← map_mul, div_mul_cancel₀ b hd]
    apply hw
    rw [hwconst]
    exact isAlgebraic_algebraMap _
  · have hb : b = a * d / c := by
      apply (eq_div_iff hc).2
      linear_combination -hdet
    have hmapc : algebraMap k F c ≠ 0 := (map_ne_zero _).2 hc
    have hnum : algebraMap k F a * z + algebraMap k F b =
        algebraMap k F (a / c) *
          (algebraMap k F c * z + algebraMap k F d) := by
      rw [hb, map_div₀, map_div₀, map_mul]
      field_simp
    have hwconst : w = algebraMap k F (a / c) := by
      apply mul_right_cancel₀ hden
      calc
        w * (algebraMap k F c * z + algebraMap k F d) =
            algebraMap k F a * z + algebraMap k F b := hrel
        _ = algebraMap k F (a / c) *
            (algebraMap k F c * z + algebraMap k F d) := hnum
    apply hw
    rw [hwconst]
    exact isAlgebraic_algebraMap _

/-- An algebra automorphism carries a field generator to another
field generator.
@isnad1 id=eq.1h4v.s8.dfe101eed124 from=translated src=- shape=d8f8795f vocab=5cea7671
-/
theorem adjoin_image_eq_top_of_adjoin_eq_top {t : F}
    (htop : adjoin k ({t} : Set F) = ⊤) (σ : F ≃ₐ[k] F) :
    adjoin k ({σ t} : Set F) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := σ.surjective x
  have hy : y ∈ adjoin k ({t} : Set F) := by
    rw [htop]
    trivial
  have hmap : σ y ∈ (adjoin k ({t} : Set F)).map σ.toAlgHom :=
    (IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at hmap
  exact hmap

/-- Algebra automorphisms preserve transcendence over the base.
@isnad1 id=transcen.1h4v.s7.51b0bf1ce6c2 from=translated src=- shape=7bca32a3 vocab=76d418cf
-/
theorem transcendental_map_algEquiv {t : F} (ht : Transcendental k t)
    (σ : F ≃ₐ[k] F) : Transcendental k (σ t) := by
  intro halg
  apply ht
  obtain ⟨p, hp0, hp⟩ := halg
  refine ⟨p, hp0, ?_⟩
  apply σ.injective
  rw [map_zero]
  have hcomp : σ.toRingEquiv.toRingHom.comp (algebraMap k F) =
      algebraMap k F := by
    ext c
    exact σ.commutes c
  calc
    σ (Polynomial.aeval t p) = Polynomial.aeval (σ t) p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def]
      calc
        σ (Polynomial.eval₂ (algebraMap k F) t p) =
            Polynomial.eval₂
              (σ.toRingEquiv.toRingHom.comp (algebraMap k F))
              (σ t) p :=
          Polynomial.hom_eval₂ p (algebraMap k F)
            σ.toRingEquiv.toRingHom t
        _ = Polynomial.eval₂ (algebraMap k F) (σ t) p := by
          rw [hcomp]
    _ = 0 := hp

end

end AclGeom
