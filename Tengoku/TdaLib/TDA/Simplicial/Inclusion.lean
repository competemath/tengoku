import Tengoku.TdaLib.TDA.Simplicial.ChainComplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Naturality of simplicial chain inclusions

For subcomplexes in one ordered ambient vertex type, the signed deletion
boundary commutes with the canonical face and chain inclusions. These maps form
chain maps between the ordinary unaugmented complexes.
-/

universe u v

namespace TDA.Simplicial

open CategoryTheory Module

variable {V : Type u} [LinearOrder V]
variable {K L M : PreAbstractSimplicialComplex V}

/-- Inclusion preserves the face obtained by deleting an ordered vertex.
@isnad1 id=eq.1h6v.s6.46e515198ed4 from=translated src=- shape=03233aeb vocab=faff2c5f
-/
theorem faceIncl_deletedFace (h : K ≤ L) (n : ℕ)
    (s : Face K (n + 1)) (i : Fin (n + 2)) :
    faceIncl h n (deletedFace K n s i) =
      deletedFace L n (faceIncl h (n + 1) s) i := by
  apply Subtype.ext
  rfl

variable (R : Type v) [Ring R]

omit [LinearOrder V] in
/-- Inclusion transports a singleton chain to the corresponding face.
@isnad1 id=eq.1h7v.s8.059b89db9792 from=translated src=- shape=d6a13a85 vocab=2eedc785
-/
theorem chainIncl_single (h : K ≤ L) (n : ℕ)
    (s : Face K n) (a : R) :
    chainIncl R h n (Finsupp.single s a) =
      Finsupp.single (faceIncl h n s) a := by
  simp [chainIncl]

/-- The signed deletion boundary is natural for every same-ambient
subcomplex inclusion. The proof checks the arbitrary-coefficient singleton
chains and then uses linear extensionality; the coefficient stays a left
scalar throughout, so no commutativity of `R` is needed.
@isnad1 id=eq.1h5v.s9.5b933b6bff43 from=translated src=- shape=c1761b97 vocab=0d888402
-/
theorem boundary_chainIncl (h : K ≤ L) (n : ℕ) :
    (boundary L R n).comp (chainIncl R h (n + 1)) =
      (chainIncl R h n).comp (boundary K R n) := by
  apply Finsupp.lhom_ext
  intro s a
  change boundary L R n
      (chainIncl R h (n + 1) (Finsupp.single s a)) =
    chainIncl R h n (boundary K R n (Finsupp.single s a))
  rw [chainIncl_single, boundary_single, boundary_single, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [chainIncl_single, faceIncl_deletedFace]

/-- The chain map induced by inclusion of faces.-/
noncomputable def simplicialChainIncl (h : K ≤ L) :
    simplicialChainComplex K R ⟶ simplicialChainComplex L R :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (chainIncl R h n)) (by
    intro n
    apply ModuleCat.hom_ext
    simp only [simplicialChainComplex_d]
    exact boundary_chainIncl R h n)

/-- The degree-`n` component is the existing linear face inclusion.
@isnad1 id=eq.1h5v.s8.ad87bf53e388 from=translated src=- shape=0e747cbe vocab=7f6d3612
-/
@[simp]
theorem simplicialChainIncl_f (h : K ≤ L) (n : ℕ) :
    (simplicialChainIncl R h).f n = ModuleCat.ofHom (chainIncl R h n) := rfl

/-- Inclusion along equality is the identity chain map.
@isnad1 id=eq.0h3v.s7.aeeecd72b53a from=translated src=- shape=85b24946 vocab=d3943c1f
-/
theorem simplicialChainIncl_id (K : PreAbstractSimplicialComplex V) :
    simplicialChainIncl R (le_refl K) = 𝟙 (simplicialChainComplex K R) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [simplicialChainIncl_f, chainIncl_id]

/-- Composable inclusions induce composable chain maps.
@isnad1 id=eq.2h5v.s8.fa55d6e9877a from=translated src=- shape=8eca4b34 vocab=25506de8
-/
theorem simplicialChainIncl_comp (h : K ≤ L) (g : L ≤ M) :
    simplicialChainIncl R (h.trans g) =
      simplicialChainIncl R h ≫ simplicialChainIncl R g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [simplicialChainIncl_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  change chainIncl R (h.trans g) n =
    (chainIncl R g n).comp (chainIncl R h n)
  exact chainIncl_comp R h g n

end TDA.Simplicial
