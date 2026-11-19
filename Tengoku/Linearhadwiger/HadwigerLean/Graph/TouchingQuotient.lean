import Tengoku.Linearhadwiger.HadwigerLean.Graph.Minor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Touching quotients of connected partitions

The quotient has one vertex per connected block. Two distinct blocks are
adjacent precisely when an edge of the original graph joins them. In
particular, every quotient edge has a witness in the original graph; extra
edges are not discarded.
-/

namespace HadwigerLean

universe u v

/-- A partition of the vertices of `G` into nonempty connected blocks.
Finiteness is required only for the numerical minor-bound theorem below.-/
structure ConnectedPartition {V : Type v} (G : SimpleGraph V) (I : Type u) where
  block : I → Set V
  connected : ∀ i, (G.induce (block i)).Connected
  disjoint : Pairwise fun i j => Disjoint (block i) (block j)
  cover : ∀ x, ∃ i, x ∈ block i

namespace ConnectedPartition

variable {V : Type v} {I : Type u} {G : SimpleGraph V}

/-- A connected block is nonempty.
@isnad1 id=nonempty.0h5v.s4.3434660ad439 from=translated src=- shape=a327bbe7 vocab=a89f2b20
-/
theorem block_nonempty (P : ConnectedPartition G I) (i : I) :
    (P.block i).Nonempty := by
  obtain ⟨x⟩ := (P.connected i).nonempty
  exact ⟨x.val, x.property⟩

/-- Every vertex lies in exactly one block.
@isnad1 id=existsun.0h5v.s4.7d8dbe0e4771 from=translated src=- shape=8931c68f vocab=d5ee92ee
-/
theorem existsUnique_block (P : ConnectedPartition G I) (x : V) :
    ∃! i, x ∈ P.block i := by
  obtain ⟨i, hi⟩ := P.cover x
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact (Set.disjoint_left.mp (P.disjoint hji)) hj hi

/-- Two blocks touch exactly when an original edge joins them.-/
def touchingQuotient (P : ConnectedPartition G I) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ x ∈ P.block i, ∃ y ∈ P.block j, G.Adj x y
  symm := ⟨by
    intro i j hij
    obtain ⟨hne, x, hx, y, hy, hxy⟩ := hij
    exact ⟨hne.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by
    intro i hii
    exact hii.1 rfl⟩

/--
@isnad1 id=iff.0h6v.s6.4458c9da542e from=translated src=- shape=6682d5aa vocab=d34128b9
-/
theorem touchingQuotient_adj_iff (P : ConnectedPartition G I) (i j : I) :
    P.touchingQuotient.Adj i j ↔
      i ≠ j ∧ ∃ x ∈ P.block i, ∃ y ∈ P.block j, G.Adj x y :=
  Iff.rfl

/-- The blocks themselves model the touching quotient as a minor.-/
def toMinorModel (P : ConnectedPartition G I) : MinorModel P.touchingQuotient G where
  branch := P.block
  connected := P.connected
  disjoint := P.disjoint
  adjacent := by
    intro i j hij
    exact (P.touchingQuotient_adj_iff i j).mp hij |>.2

/--
@isnad1 id=isminor.0h4v.s4.414086536a7d from=translated src=- shape=be0665ee vocab=6e438a25
-/
theorem isMinor (P : ConnectedPartition G I) : IsMinor P.touchingQuotient G :=
  ⟨P.toMinorModel⟩

/-- A connected touching quotient has no larger complete minor.
@isnad1 id=le.0h4v.s5.c54fa5d2a139 from=translated src=- shape=acfcea30 vocab=f5b4c2d1
-/
theorem cliqueMinorNumber_touchingQuotient_le [Fintype V] [Fintype I]
    (P : ConnectedPartition G I) :
    cliqueMinorNumber P.touchingQuotient ≤ cliqueMinorNumber G :=
  cliqueMinorNumber_mono_minor P.isMinor

end ConnectedPartition

end HadwigerLean
