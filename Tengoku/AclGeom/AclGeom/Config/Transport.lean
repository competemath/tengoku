/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Multiplication
import Tengoku.AclGeom.AclGeom.Geometry.Transport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of the configuration relations along lattice isomorphisms

An order isomorphism `e : ClosedIF k K ≃o ClosedIF l L` of closed-subfield lattices acts on points
by `Point.map e`.  It preserves every relation of the configuration layer, because each one is
built from joins, meets, the order, finite rank, injectivity and quantifiers over points.  This is
the configuration part of the naturality of the interpretation (blueprint
Prop `interpreted-reconstruction`, checklist I6).

* `IsPartialQuadrangle.map`: partial quadrangles go to partial quadrangles.
* `QWitness.map`: the twenty-one witness points are mapped pointwise.  The rank-two joins are
  computed by `QWitness.map_A`, `QWitness.map_B` and `QWitness.map_C`.
* `QWitness.Psi.map`: all twenty-four clauses of `Ψ` are preserved.
* `MulDiagram.map`: multiplication diagrams are preserved.
* `qGeom_map_iff`, `q'Geom_map_iff`, `jGeom_map_iff`: the geometric relations `Q`, `Q′` and `J`
  are invariant.  The reverse directions apply the forward ones to `e.symm`.

The arguments are purely order-theoretic.  No semantics, completeness, rank hypothesis or fresh
element is used.  The bases and ambient fields are arbitrary and may live in different universes.

**Status:** geometric configuration transport is complete (#23/#8, I6b1).
Conditional class/carrier and graph transport, the same geometric map bundled as a RingEquiv,
and its composition with both decodings are proved in `Naturality` under explicit carrier inputs.
Canonical image-base existence and conditional field-isomorphism existence are also proved there;
the source pair and target rank are derived inline from source rank five and the lattice map.
Both perfections, separate exponential characteristics and both ACF-completeness inputs remain
explicit. Corrected base/scalar recovery and original-field inducing existence are proved in
`Reconstruct` with both perfected completeness inputs explicit. `Main` supplies them through
`jCompletenessACF` and proves the public lattice-form target under the blueprint hypotheses.
The point, automorphism, literal/quotient functorial and perfection-choice variants are proved.
Original literal construction and provenance obligations remain on #8 and #23.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

noncomputable section

variable {k K l L : Type*} [Field k] [Field K] [Algebra k K]
  [Field l] [Field L] [Algebra l L]

/-- An order isomorphism of closed lattices carries partial quadrangles to partial quadrangles.-/
theorem IsPartialQuadrangle.map (e : ClosedIF k K ≃o ClosedIF l L) {f : Fin 6 → Point k K}
    (h : IsPartialQuadrangle f) : IsPartialQuadrangle (Point.map e ∘ f) where
  injective := (Point.map e).injective.comp h.injective
  rank_dep s hs := by
    have h' := (rankEq_map_iff e 2 _).2 (h.rank_dep s hs)
    rw [map_finset_sup] at h'
    exact h'
  rank_free s hs hq := by
    have h' := (rankEq_map_iff e 3 _).2 (h.rank_free s hs hq)
    rw [map_finset_sup] at h'
    exact h'
  rank_total := by
    have h' := (rankEq_map_iff e 3 _).2 h.rank_total
    rw [map_finset_sup] at h'
    exact h'

/-- The image of a `Q`-witness under an order isomorphism of closed lattices: each of the
twenty-one points is mapped by `Point.map e`.-/
def QWitness.map (e : ClosedIF k K ≃o ClosedIF l L) (w : QWitness k K) : QWitness l L where
  A₁ := Point.map e w.A₁
  A₂ := Point.map e w.A₂
  B₁ := Point.map e w.B₁
  B₂ := Point.map e w.B₂
  C₁ := Point.map e w.C₁
  C₂ := Point.map e w.C₂
  D := Point.map e w.D
  E := Point.map e w.E
  F := Point.map e w.F
  G := Point.map e w.G
  H := Point.map e w.H
  I := Point.map e w.I
  P := Point.map e w.P
  Q := Point.map e w.Q
  R := Point.map e w.R
  S := Point.map e w.S
  T := Point.map e w.T
  U := Point.map e w.U
  X := Point.map e w.X
  Y := Point.map e w.Y
  Z := Point.map e w.Z

/-- The rank-two join `A = A₁ ∨ A₂` of the image witness is the image of `A`.-/
theorem QWitness.map_A (e : ClosedIF k K ≃o ClosedIF l L) (w : QWitness k K) :
    (w.map e).A = e w.A :=
  (map_sup e w.A₁.1 w.A₂.1).symm

/-- The rank-two join `B = B₁ ∨ B₂` of the image witness is the image of `B`.-/
theorem QWitness.map_B (e : ClosedIF k K ≃o ClosedIF l L) (w : QWitness k K) :
    (w.map e).B = e w.B :=
  (map_sup e w.B₁.1 w.B₂.1).symm

/-- The rank-two join `C = C₁ ∨ C₂` of the image witness is the image of `C`.-/
theorem QWitness.map_C (e : ClosedIF k K ≃o ClosedIF l L) (w : QWitness k K) :
    (w.map e).C = e w.C :=
  (map_sup e w.C₁.1 w.C₂.1).symm

/-- **An order isomorphism preserves `Ψ`**: all twenty-four clauses (i)–(vii) of the
`Q`-configuration hold for the image witness.-/
theorem QWitness.Psi.map (e : ClosedIF k K ≃o ClosedIF l L) {w : QWitness k K} (h : w.Psi) :
    (w.map e).Psi where
  rank_ABC := by
    rw [QWitness.map_A, QWitness.map_B, QWitness.map_C]
    simpa only [← map_sup, rankEq_map_iff] using h.rank_ABC
  rank_AB := by
    rw [QWitness.map_A, QWitness.map_B]
    simpa only [← map_sup, rankEq_map_iff] using h.rank_AB
  rank_BC := by
    rw [QWitness.map_B, QWitness.map_C]
    simpa only [← map_sup, rankEq_map_iff] using h.rank_BC
  rank_AC := by
    rw [QWitness.map_A, QWitness.map_C]
    simpa only [← map_sup, rankEq_map_iff] using h.rank_AC
  X_le := by
    rw [QWitness.map_A]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] using h.X_le
  Z_le := by
    rw [QWitness.map_B, QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf, e.le_iff_le] using h.Z_le
  X_notLe := by
    rw [QWitness.map_A, QWitness.map_B, QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] using h.X_notLe
  Y_notLe := by
    rw [QWitness.map_A, QWitness.map_B, QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] using h.Y_notLe
  Z_notLe := by
    rw [QWitness.map_A, QWitness.map_B, QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] using h.Z_notLe
  X_free := by
    intro A' hA' hX
    obtain ⟨A'', rfl⟩ := (Point.map e).surjective A'
    rw [QWitness.map_A] at hA'
    simp only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] at hA' hX
    exact h.X_free A'' hA' hX
  Z_freeB := by
    intro B' hB' hZ
    obtain ⟨B'', rfl⟩ := (Point.map e).surjective B'
    rw [QWitness.map_B] at hB'
    simp only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] at hB' hZ
    exact h.Z_freeB B'' hB' hZ
  Z_freeC := by
    intro C' hC' hZ
    obtain ⟨C'', rfl⟩ := (Point.map e).surjective C'
    rw [QWitness.map_C] at hC'
    simp only [QWitness.map, Point.map_coe, ← map_sup, e.le_iff_le] at hC' hZ
    exact h.Z_freeC C'' hC' hZ
  S_le := by
    rw [QWitness.map_A]
    simpa only [QWitness.map, Point.map_coe, e.le_iff_le] using h.S_le
  T_le := by
    rw [QWitness.map_B]
    simpa only [QWitness.map, Point.map_coe, e.le_iff_le] using h.T_le
  U_le := by
    rw [QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, e.le_iff_le] using h.U_le
  rank_STU := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, rankEq_map_iff] using h.rank_STU
  quad := by
    obtain ⟨S', T', U', hq⟩ := h.quad
    refine ⟨Point.map e S', Point.map e T', Point.map e U', ?_⟩
    convert hq.map e using 1
    funext i
    fin_cases i <;> rfl
  meet_D := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_D
  meet_E := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_E
  meet_F := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_F
  meet_G := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_G
  meet_I := by
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_I
  meet_H := by
    rw [QWitness.map_A]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_H
  meet_R := by
    rw [QWitness.map_C]
    simpa only [QWitness.map, Point.map_coe, ← map_sup, ← map_inf,
      EmbeddingLike.apply_eq_iff_eq] using h.meet_R

/-- **`Q` is invariant under order isomorphisms of closed lattices**: the geometric relation `Q`
holds for the images of four points exactly when it holds for the points.-/
theorem qGeom_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {P D Y I : Point k K} :
    QGeom (Point.map e P) (Point.map e D) (Point.map e Y) (Point.map e I) ↔ QGeom P D Y I := by
  constructor
  · rintro ⟨w, hw, hP, hD, hY, hI⟩
    have hinv : ∀ Q : Point k K, Point.map e.symm (Point.map e Q) = Q :=
      fun Q ↦ Subtype.ext (e.symm_apply_apply Q.1)
    exact ⟨w.map e.symm, hw.map e.symm, (congrArg (Point.map e.symm) hP).trans (hinv P),
      (congrArg (Point.map e.symm) hD).trans (hinv D),
      (congrArg (Point.map e.symm) hY).trans (hinv Y),
      (congrArg (Point.map e.symm) hI).trans (hinv I)⟩
  · rintro ⟨w, hw, rfl, rfl, rfl, rfl⟩
    exact ⟨w.map e, hw.map e, rfl, rfl, rfl, rfl⟩

/-- An order isomorphism of closed lattices carries multiplication diagrams to multiplication
diagrams.-/
theorem MulDiagram.map (e : ClosedIF k K ≃o ClosedIF l L) {X Y V E A₀ B₀ C₀ D₀ : Point k K}
    (h : MulDiagram X Y V E A₀ B₀ C₀ D₀) :
    MulDiagram (Point.map e X) (Point.map e Y) (Point.map e V) (Point.map e E) (Point.map e A₀)
      (Point.map e B₀) (Point.map e C₀) (Point.map e D₀) where
  distinct := by
    convert (Point.map e).injective.comp h.distinct using 1
    funext i
    fin_cases i <;> rfl
  line_XAB := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_XAB
  line_AYC := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_AYC
  line_AED := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_AED
  line_BYD := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_BYD
  line_XCD := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_XCD
  line_BCV := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_BCV
  line_XYEV := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.line_XYEV
  rank_XYA := by simpa only [Point.map_coe, ← map_sup, rankEq_map_iff] using h.rank_XYA

/-- **`Q′` is invariant under order isomorphisms of closed lattices**: the geometric relation `Q′`
holds for the images of four points exactly when it holds for the points.-/
theorem q'Geom_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {X Y S E : Point k K} :
    Q'Geom (Point.map e X) (Point.map e Y) (Point.map e S) (Point.map e E) ↔ Q'Geom X Y S E := by
  constructor
  · rintro ⟨V, A₀, B₀, C₀, D₀, hQ, hM⟩
    obtain ⟨V', rfl⟩ := (Point.map e).surjective V
    obtain ⟨A₀', rfl⟩ := (Point.map e).surjective A₀
    obtain ⟨B₀', rfl⟩ := (Point.map e).surjective B₀
    obtain ⟨C₀', rfl⟩ := (Point.map e).surjective C₀
    obtain ⟨D₀', rfl⟩ := (Point.map e).surjective D₀
    have hinv : ∀ Q : Point k K, Point.map e.symm (Point.map e Q) = Q :=
      fun Q ↦ Subtype.ext (e.symm_apply_apply Q.1)
    have hM' := hM.map e.symm
    simp only [hinv] at hM'
    exact ⟨V', A₀', B₀', C₀', D₀', (qGeom_map_iff e).1 hQ, hM'⟩
  · rintro ⟨V, A₀, B₀, C₀, D₀, hQ, hM⟩
    exact ⟨Point.map e V, Point.map e A₀, Point.map e B₀, Point.map e C₀, Point.map e D₀,
      (qGeom_map_iff e).2 hQ, hM.map e⟩

/-- **`J` is invariant under order isomorphisms of closed lattices**: the geometric relation `J`
holds for the images of five points exactly when it holds for the points.-/
theorem jGeom_map_iff (e : ClosedIF k K ≃o ClosedIF l L) {X P Q R A : Point k K} :
    JGeom (Point.map e X) (Point.map e P) (Point.map e Q) (Point.map e R) (Point.map e A) ↔
      JGeom X P Q R A := by
  simp only [JGeom, qGeom_map_iff, q'Geom_map_iff]

end

end AclGeom
