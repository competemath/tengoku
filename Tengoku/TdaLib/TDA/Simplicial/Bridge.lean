import Tengoku.TdaLib.TDA.Filtration.Basic
import Tengoku.Seed.Algebra.Homology.ShortComplex.ModuleCat
import Tengoku.Seed.Algebra.Homology.ShortComplex.HomologicalComplex
import Tengoku.Seed.Algebra.Homology.HomologicalComplex
import Tengoku.Seed.LinearAlgebra.Finsupp.VectorSpace
import Tengoku.Seed.LinearAlgebra.Finsupp.Pi
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Face chains and homology

The basis uses precisely the faces of a preabstract simplicial complex. This module defines
face inclusions, the induced maps of free modules, and the kernel/image presentation of
homology, together with small chain fixtures.
-/

universe u

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]

/-- Nonempty `(n+1)`-vertex faces, with no ambient singleton completion.-/
abbrev Face (K : PreAbstractSimplicialComplex V) (n : ℕ) :=
  {s : Finset V // s ∈ K ∧ s.card = n + 1}

/-- A finite total face set is a separate hypothesis from each face being a `Finset`.-/
abbrev TotalFace (K : PreAbstractSimplicialComplex V) := {s : Finset V // s ∈ K}

/--
@isnad1 id=finite.0h3v.s4.a7cc5d4520c0 from=translated src=- shape=a7d7b709 vocab=cc20b844
-/
instance faceFiniteOfTotalFinite (K : PreAbstractSimplicialComplex V) (n : ℕ)
    [Finite (TotalFace K)] : Finite (Face K n) :=
  Finite.of_injective (fun s => (⟨s.1, s.2.1⟩ : TotalFace K)) (by
    intro a b h
    have hv : a.1 = b.1 := congrArg (fun t : TotalFace K => t.1) h
    exact Subtype.ext hv)

/-- Free oriented chains on faces, with the orientation from the ambient order.-/
abbrev Chain (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (n : ℕ) :=
  Face K n →₀ R

/-- The canonical face basis; this does not require finite ambient vertices.-/
noncomputable def faceBasis (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] (n : ℕ) :
    Basis (Face K n) R (Chain K R n) := Finsupp.basisSingleOne

/-- A face inclusion keeps the same ordered vertex set and its orientation.-/
def faceIncl {K L : PreAbstractSimplicialComplex V} (h : K ≤ L) (n : ℕ) :
    Face K n → Face L n := fun s => ⟨s.1, h s.2.1, s.2.2⟩

/-- Inclusion of the corresponding free modules.-/
noncomputable def chainIncl {K L : PreAbstractSimplicialComplex V} (R : Type*) [Ring R]
    (h : K ≤ L) (n : ℕ) : Chain K R n →ₗ[R] Chain L R n :=
  Finsupp.lmapDomain R R (faceIncl h n)

omit [LinearOrder V] in
/--
@isnad1 id=eq.0h4v.s7.fe27d74b4b91 from=translated src=- shape=717272a0 vocab=086a9694
-/
theorem chainIncl_id (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R]
    (n : ℕ) : chainIncl R (le_refl K) n = LinearMap.id := by
  have he : faceIncl (le_refl K) n = (id : Face K n → Face K n) := by
    funext s
    rfl
  simp [chainIncl, he]

omit [LinearOrder V] in
/--
@isnad1 id=eq.2h6v.s8.6534f796cae5 from=translated src=- shape=637e3e46 vocab=b3e600a4
-/
theorem chainIncl_comp {K L M : PreAbstractSimplicialComplex V} (R : Type*) [Ring R]
    (h : K ≤ L) (g : L ≤ M) (n : ℕ) :
    chainIncl R (h.trans g) n = (chainIncl R g n).comp (chainIncl R h n) := by
  have he : faceIncl (h.trans g) n = faceIncl g n ∘ faceIncl h n := by
    funext s
    rfl
  simpa [chainIncl, he] using
    (Finsupp.lmapDomain_comp (M := R) (R := R) (faceIncl h n) (faceIncl g n))

/-- The existing ModuleCat kernel/image-inside-kernel quotient, for any supplied
chain complex. This identifies ordinary homology rather than defining a new quotient.-/
noncomputable def homologyKernelQuotient (R : Type*) [Ring R]
    (C : ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    C.homology n ≅ ModuleCat.of R
      (LinearMap.ker (C.sc n).g.hom ⧸ LinearMap.range (C.sc n).moduleCatToCycles) :=
  (C.sc n).moduleCatHomologyIso

/-- The degree-zero short complex for a fixture with no edges. Both maps are zero,
as required by ordinary, unaugmented homology.-/
noncomputable def zeroBoundaryH0 (K : PreAbstractSimplicialComplex V) (R : Type*) [Ring R] :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (0 : Chain K R 1 →ₗ[R] Chain K R 0)
    (0 : Chain K R 0 →ₗ[R] Chain K R 0) (by simp)

/-- Ordinary H₀ of a zero-boundary fixture equals its degree-zero chains.-/
noncomputable def zeroBoundaryH0Iso (K : PreAbstractSimplicialComplex V)
    (R : Type*) [Ring R] :
    (zeroBoundaryH0 K R).homology ≅ ModuleCat.of R (Chain K R 0) :=
  (ShortComplex.LeftHomologyData.ofZeros (zeroBoundaryH0 K R) rfl rfl).homologyIso

/--
@isnad1 id=isempty.0h2v.s3.594b1869cbad from=translated src=- shape=479abbef vocab=1be8096f
-/
instance emptyFaceIsEmpty (n : ℕ) : IsEmpty (Face (⊥ : PreAbstractSimplicialComplex V) n) :=
  ⟨fun s => (Filtration.mem_bot_iff s.1).mp s.2.1⟩

omit [LinearOrder V] in
/-- The empty precomplex has zero chains in every degree.
@isnad1 id=eq.0h4v.s6.904690684d9e from=translated src=- shape=b0b2208e vocab=e4ef7705
-/
theorem emptyChain_eq_zero (R : Type*) [Ring R] (n : ℕ)
    (c : Chain (⊥ : PreAbstractSimplicialComplex V) R n) : c = 0 :=
  Subsingleton.elim _ _

omit [LinearOrder V] in
/-- Its ordinary unaugmented H₀ is the zero module.
@isnad1 id=eq.0h3v.s8.98030f6a5344 from=translated src=- shape=0593eb1e vocab=e409dfef
-/
theorem emptyH0_eq_zero (R : Type*) [Ring R]
    (c : (zeroBoundaryH0 (⊥ : PreAbstractSimplicialComplex V) R).homology) : c = 0 := by
  apply (zeroBoundaryH0Iso (⊥ : PreAbstractSimplicialComplex V) R).toLinearEquiv.injective
  exact Subsingleton.elim _ _

/--
@isnad1 id=subsingl.0h2v.s3.eac40047f8b2 from=translated src=- shape=84533fe5 vocab=6f77f97b
-/
instance singletonFaceZeroSubsingleton (x : V) :
    Subsingleton (Face (Filtration.singletonFace x) 0) := by
  constructor
  intro a b
  apply Subtype.ext
  calc
    a.1 = {x} := (Filtration.mem_singletonFace_iff x a.1).mp a.2.1
    _ = b.1 := ((Filtration.mem_singletonFace_iff x b.1).mp b.2.1).symm

/-- The only degree-zero basis face of a singleton complex.-/
def singletonVertex (x : V) : Face (Filtration.singletonFace x) 0 :=
  ⟨{x}, (Filtration.mem_singletonFace_iff x {x}).mpr rfl, by simp⟩

/--
@isnad1 id=isempty.0h3v.s4.b351871d3aaf from=translated src=- shape=1f96a5b8 vocab=011d224b
-/
instance singletonFaceHigherIsEmpty (x : V) (n : ℕ) :
    IsEmpty (Face (Filtration.singletonFace x) (n + 1)) := by
  constructor
  intro s
  have hs := (Filtration.mem_singletonFace_iff x s.1).mp s.2.1
  have hc : 1 = n + 1 + 1 := by simpa [hs] using s.2.2
  omega

omit [LinearOrder V] in
/-- A singleton has no positive-degree chains.
@isnad1 id=eq.0h5v.s6.4744d44457ac from=translated src=- shape=29c59b71 vocab=8e4628d5
-/
theorem singletonHigherChain_eq_zero (x : V) (R : Type*) [Ring R] (n : ℕ)
    (c : Chain (Filtration.singletonFace x) R (n + 1)) : c = 0 :=
  Subsingleton.elim _ _

/-- The ordinary H₀ of an isolated vertex is exactly its coefficient module.-/
noncomputable def singletonH0Iso (x : V) (R : Type u) [Ring R] :
    (zeroBoundaryH0 (Filtration.singletonFace x) R).homology ≅ ModuleCat.of R R :=
  (zeroBoundaryH0Iso (Filtration.singletonFace x) R).trans
    ((Finsupp.uniqueLinearEquiv R R (singletonVertex x)).toModuleIso)

section Triangle

/-- The complete triangle on the three ambient vertices; each face below is a face.-/
private def triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private def vertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩

private def edge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def edge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def edge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private def triangle : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

/-- Oriented edge boundary, using the fixed order `0 < 1 < 2`.-/
private noncomputable def edgeBoundary (e : Face triangleK 1) : Chain triangleK ℤ 0 :=
  if e = edge01 then Finsupp.single (vertex 1) 1 - Finsupp.single (vertex 0) 1
  else if e = edge02 then Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 0) 1
  else Finsupp.single (vertex 2) 1 - Finsupp.single (vertex 1) 1

/-- The boundary on the finite edge basis, extended linearly.-/
private noncomputable def signedD1 : Chain triangleK ℤ 1 →ₗ[ℤ] Chain triangleK ℤ 0 :=
  Finsupp.linearCombination ℤ edgeBoundary

/-- `[1,2] - [0,2] + [0,1]` as an edge chain.-/
private noncomputable def triangleBoundary : Chain triangleK ℤ 1 :=
  Finsupp.single edge12 1 - Finsupp.single edge02 1 + Finsupp.single edge01 1

/-- The triangular 2-simplex has precisely the required signed edge boundary.-/
private noncomputable def signedD2 : Chain triangleK ℤ 2 →ₗ[ℤ] Chain triangleK ℤ 1 :=
  Finsupp.linearCombination ℤ (fun _ => triangleBoundary)

/-- A one-edge subcomplex in the same three-vertex ambient type.-/
private def edgeK : PreAbstractSimplicialComplex (Fin 3) where
  faces := {s | s.Nonempty ∧ s ⊆ {0, 1}}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩

private def edgeVertex (i : Fin 3) (hi : i ∈ ({0, 1} : Finset (Fin 3))) :
    Face edgeK 0 :=
  ⟨{i}, ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, by simp⟩

private def edgeFace : Face edgeK 1 :=
  ⟨{0, 1}, ⟨by decide, Finset.Subset.refl _⟩, by decide⟩

private noncomputable def edgeD1 : Chain edgeK ℤ 1 →ₗ[ℤ] Chain edgeK ℤ 0 :=
  Finsupp.linearCombination ℤ (fun _ =>
    Finsupp.single (edgeVertex 1 (by simp)) 1 -
    Finsupp.single (edgeVertex 0 (by simp)) 1)

end Triangle

end TDA.Simplicial
