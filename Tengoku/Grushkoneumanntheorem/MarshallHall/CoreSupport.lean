import Tengoku.Grushkoneumanntheorem.MarshallHall.GraphBasis
import Tengoku.Grushkoneumanntheorem.MarshallHall.FreeFactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section

namespace MarshallHall

universe u

variable {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]

/-!
## Core-supported words in a spanning-tree basis

The finite-core argument produces paths whose labelled edges belong to a fixed
finite set of generator edges.  The lemmas below make that geometric fact
visible in the free basis supplied by a spanning tree.
-/

def basisSupport {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    (P : Set (Quiver.Total (IsFreeGroupoid.Generators G))) :
    Set ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ :
      Set (Quiver.Total (IsFreeGroupoid.Generators G))) :=
  {e | e.1 ∈ P}

def forgetSubquiverPath {V : Type u} [Quiver V] {P : WideSubquiver V}
    {a b : P} : @Path P P.quiver a b → @Path V inferInstance (a : V) (b : V)
  | Path.nil => Path.nil
  | Path.cons p e => Path.cons (forgetSubquiverPath p) e.1

/--
@isnad1 id=eq.0h3v.s5.d581b548ca27 from=translated src=- shape=d5bba13a vocab=b153440f
-/
@[simp] theorem forgetSubquiverPath_nil {V : Type u} [Quiver V]
    {P : WideSubquiver V} {a : P} :
    forgetSubquiverPath (Path.nil : @Path P P.quiver a a) = Path.nil := rfl

/--
@isnad1 id=eq.0h7v.s7.c0d30a3eadb8 from=translated src=- shape=f9af6854 vocab=1d45f437
-/
@[simp] theorem forgetSubquiverPath_cons {V : Type u} [Quiver V]
    {P : WideSubquiver V} {a b c : P}
    (p : @Path P P.quiver a b) (e : b ⟶ c) :
    forgetSubquiverPath (p.cons e) = (forgetSubquiverPath p).cons e.1 := rfl

def positiveEdgeOfSym {a b : Symmetrify (IsFreeGroupoid.Generators G)}
    (e : a ⟶ b) : Quiver.Total (IsFreeGroupoid.Generators G) :=
  match e with
  | Sum.inl f => ⟨a, b, f⟩
  | Sum.inr f => ⟨b, a, f⟩

def retractBasisElement {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z : K) : K :=
  subsetBasisHom B Y (basisRetraction Y (B.repr z))

/--
@isnad1 id=eq.0h4v.s5.39ddf4775a7c from=translated src=- shape=0e9cb03b vocab=991cdd3d
-/
theorem retractBasisElement_one {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) :
    retractBasisElement B Y (1 : K) = 1 := by
  unfold retractBasisElement
  rw [B.repr.map_one, (basisRetraction Y).map_one, (subsetBasisHom B Y).map_one]
  rfl

/--
@isnad1 id=eq.0h6v.s6.2ac55fcd9bb7 from=translated src=- shape=dd1f6a87 vocab=7d5aaa2c
-/
theorem retractBasisElement_mul {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z w : K) :
    retractBasisElement B Y (z * w) =
      retractBasisElement B Y z * retractBasisElement B Y w := by
  unfold retractBasisElement
  rw [B.repr.map_mul, (basisRetraction Y).map_mul,
    (subsetBasisHom B Y).map_mul]
  rfl

/--
@isnad1 id=eq.0h5v.s5.a58506b7bffb from=translated src=- shape=9c44bf31 vocab=6e79119f
-/
theorem retractBasisElement_inv {X K : Type u} [Group K]
    (B : FreeGroupBasis X K) (Y : Set X) (z : K) :
    retractBasisElement B Y z⁻¹ = (retractBasisElement B Y z)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).2
  rw [← retractBasisElement_mul]
  rw [inv_mul_cancel, retractBasisElement_one]

/--
@isnad1 id=eq.0h7v.s7.b84986fb2eb8 from=translated src=- shape=7fdb09f1 vocab=f7071cdc
-/
theorem loopOfHom_comp {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T] {a b c : G} (p : a ⟶ b) (q : b ⟶ c) :
    IsFreeGroupoid.SpanningTree.loopOfHom T (p ≫ q) =
      IsFreeGroupoid.SpanningTree.loopOfHom T q *
        IsFreeGroupoid.SpanningTree.loopOfHom T p := by
  simp [IsFreeGroupoid.SpanningTree.loopOfHom, Category.assoc]

/--
@isnad1 id=eq.0h5v.s7.24586ea7dfe9 from=translated src=- shape=52493d61 vocab=898e0fc2
-/
theorem loopOfHom_inv {T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators G))}
    [Arborescence T] {a b : G} (p : a ⟶ b) :
      IsFreeGroupoid.SpanningTree.loopOfHom T (inv p) =
      (IsFreeGroupoid.SpanningTree.loopOfHom T p)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one).2
  simp [IsFreeGroupoid.SpanningTree.loopOfHom, CategoryTheory.End.mul_def,
    Category.assoc]

end MarshallHall
