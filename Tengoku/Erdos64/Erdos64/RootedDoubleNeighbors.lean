import Tengoku.Erdos64.Erdos64.RootedDouble

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The neighbors of the shared root are two tagged copies of the original
root neighborhood.-/
noncomputable def rootedDouble_root_neighborEquiv
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V} :
    (rootedDoubleGraph G r).neighborSet none ≃ Bool × G.neighborSet r where
  toFun := fun w =>
    match w with
    | ⟨none, h⟩ =>
        (rootedDoubleGraph G r).irrefl
          (show (rootedDoubleGraph G r).Adj none none from h) |>.elim
    | ⟨some (b, v), h⟩ =>
        (b, ⟨v.1, h.1⟩)
  invFun := fun w =>
    ⟨some (w.1, ⟨w.2.1, by
      intro h
      exact G.irrefl (h ▸ w.2.2)⟩), by
      show (rootedDoubleGraph G r).Adj none
        (some (w.1, ⟨w.2.1, by
          intro h
          exact G.irrefl (h ▸ w.2.2)⟩))
      exact ⟨w.2.2, trivial⟩⟩
  left_inv := by
    rintro ⟨z, hz⟩
    cases z with
    | none =>
        exact (rootedDoubleGraph G r).irrefl
          (show (rootedDoubleGraph G r).Adj none none from hz) |>.elim
    | some zv =>
        rcases zv with ⟨b, v⟩
        apply Subtype.ext
        simp only [Option.some.injEq]
  right_inv := by
    rintro ⟨b, v⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- The shared root has twice the original root degree.-/
theorem rootedDouble_root_degree_doubling
    {V : Type u} {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {r : V} :
    (rootedDoubleGraph G r).degree none = 2 * G.degree r :=
  rootedDouble_root_degree_doubling_of_neighborEquiv
    (rootedDouble_root_neighborEquiv (G := G) (r := r))

end Erdos64
