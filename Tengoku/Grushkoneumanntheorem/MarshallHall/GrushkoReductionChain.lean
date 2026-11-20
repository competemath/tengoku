import Tengoku.Grushkoneumanntheorem.MarshallHall.GrushkoInvariant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1000000

/-!
## Auxiliary safe-fold interface

The graph files prove the local semantics of a fold and the invariant file
proves the Euler inequality that is preserved by it.  This file supplies the
global induction that those local facts support.  In the selected theorem,
`GrushkoFull.lean` performs the complete reduction as a source unfold, then a
safe fold, and then the monochromatic-vertex contraction.
-/

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u v

variable {G H : Type u} [Group G] [Group H]

/-! ### The safe-path hypothesis -/

/-- A graph-level formulation of the one point still missing from the fold
argument.  The graph is assumed to be generating, connected, reverse-free,
and to satisfy the Euler bound.  At least one non-base vertex must admit a
null path whose first edge can be folded without reusing either orientation
in the complementary path.-/
def HasSafeNullFold : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
    [hV : HasInvolutiveReverse V]
    [hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
    ReverseFree (V := V) → M.IsGenerating → M.WeaklyConnected →
      Fintype.card (AllArrow (V := V)) ≤
        2 * (n + Fintype.card V - 1) →
      1 < Fintype.card V →
      ∃ v : V, v ≠ M.base ∧
        ∃ p : @Quiver.Path (Symmetrify V)
            (@Quiver.symmetrifyQuiver V qV)
            (show Symmetrify V from M.base) (show Symmetrify V from v),
          M.labeling.symmPathRead p = 1 ∧
          ∃ c : Symmetrify V,
            ∃ e : @Quiver.Hom (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV)
              (show Symmetrify V from M.base) c,
            ∃ q : @Quiver.Path (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV) c
              (show Symmetrify V from v),
              p = e.toPath.comp q ∧
                foldSymmPathAvoid (symmOrientedArrow e) q

/-- An auxiliary geometric condition used to derive `HasSafeNullFold`.  This
is weaker than `HasSafeNullFold`: it asks only for a geometrically simple null
path, from which the first edge is safe by
`foldSymmPathAvoid_of_geometricallySimple`.  It is not an alternative branch
of the selected global reduction, whose certified sequence is source unfold,
safe fold, and monochromatic-vertex contraction.-/
def HasGeometricallySimpleNullPath : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
    [hV : HasInvolutiveReverse V]
    [hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
    M.IsGenerating → M.WeaklyConnected →
      1 < Fintype.card V →
      ∃ v : V, v ≠ M.base ∧
        ∃ p : @Quiver.Path (Symmetrify V)
            (@Quiver.symmetrifyQuiver V qV)
            (show Symmetrify V from M.base) (show Symmetrify V from v),
          M.labeling.symmPathRead p = 1 ∧
          GeometricallySimple (qV := qV) p

theorem hasSafeNullFold_of_hasGeometricallySimpleNullPath
    (hsimple : HasGeometricallySimpleNullPath (G := G) (H := H)) :
    HasSafeNullFold (G := G) (H := H) := by
  intro n V hF qV hV hHom M hfree hgen hconn hEuler hcard
  obtain ⟨v, hv, p, hp, hsimple⟩ :=
    hsimple n V M hgen hconn hcard
  have hp_len : p.length ≠ 0 := by
    intro hzero
    apply hv
    exact (@Path.eq_of_length_zero (Symmetrify V)
      (@Quiver.symmetrifyQuiver V qV) M.base v p hzero).symm
  obtain ⟨c, e, q, hpq⟩ :=
    BinaryLabelling.exists_first_edge_comp (V := V) p hp_len
  have hq : foldSymmPathAvoid (symmOrientedArrow e) q := by
    apply foldSymmPathAvoid_of_geometricallySimple e q
    rw [← hpq]
    exact hsimple
  exact ⟨v, hv, p, hp, c, e, q, hpq, hq⟩

/-! ### One safe step transports all induction data -/

/-! ### Strong induction on the number of vertices -/

end GeneralGrushko
end MarshallHall
