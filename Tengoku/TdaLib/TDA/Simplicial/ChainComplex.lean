import Tengoku.TdaLib.TDA.Simplicial.Boundary
import Tengoku.Seed.Data.Fin.Parity
import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordered face chain complex

The two ways to delete a pair of ordered vertices give the same face
with opposite coefficients. This proves that the signed boundary squares to zero.
-/

universe u v

namespace TDA.Simplicial

variable {V : Type u} [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

private def swapDeletion (n : ℕ) (x : Fin (n + 2) × Fin (n + 1)) :
    Fin (n + 2) × Fin (n + 1) :=
  (x.1.succAbove x.2, x.2.predAbove x.1)

private theorem swapDeletion_involutive (n : ℕ)
    (x : Fin (n + 2) × Fin (n + 1)) :
    swapDeletion n (swapDeletion n x) = x := by
  rcases x with ⟨i, j⟩
  simp [swapDeletion, Fin.succAbove_succAbove_predAbove,
    Fin.predAbove_predAbove_succAbove]

private theorem swapDeletion_ne (n : ℕ)
    (x : Fin (n + 2) × Fin (n + 1)) : swapDeletion n x ≠ x := by
  rcases x with ⟨i, j⟩
  intro h
  have hi : i.succAbove j = i := congrArg Prod.fst h
  exact (Fin.succAbove_ne i j) hi

private theorem deletedFace_twice (n : ℕ) (s : Face K (n + 2))
    (i : Fin (n + 3)) (j : Fin (n + 2)) :
    deletedFace K n (deletedFace K (n + 1) s i) j =
      deletedFace K n (deletedFace K (n + 1) s (i.succAbove j))
        (j.predAbove i) := by
  have hleft :
      (deletedFace K (n + 1) s i).1.orderEmbOfFin
          (deletedFace K (n + 1) s i).2.2 j =
        s.1.orderEmbOfFin s.2.2 (i.succAbove j) := by
    exact enumerationAfterDeletion K (n + 1) s i
      (deletedFace K (n + 1) s i).2.2 j
  have hright :
      (deletedFace K (n + 1) s (i.succAbove j)).1.orderEmbOfFin
          (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i) =
        s.1.orderEmbOfFin s.2.2 i := by
    calc
      _ = s.1.orderEmbOfFin s.2.2
          ((i.succAbove j).succAbove (j.predAbove i)) :=
        enumerationAfterDeletion K (n + 1) s (i.succAbove j)
          (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i)
      _ = _ := by rw [Fin.succAbove_succAbove_predAbove]
  apply Subtype.ext
  change ((deletedFace K (n + 1) s i).1.erase
      ((deletedFace K (n + 1) s i).1.orderEmbOfFin
        (deletedFace K (n + 1) s i).2.2 j)) =
    ((deletedFace K (n + 1) s (i.succAbove j)).1.erase
      ((deletedFace K (n + 1) s (i.succAbove j)).1.orderEmbOfFin
        (deletedFace K (n + 1) s (i.succAbove j)).2.2 (j.predAbove i)))
  rw [hleft, hright]
  change (s.1.erase (s.1.orderEmbOfFin s.2.2 i)).erase
      (s.1.orderEmbOfFin s.2.2 (i.succAbove j)) =
    (s.1.erase (s.1.orderEmbOfFin s.2.2 (i.succAbove j))).erase
      (s.1.orderEmbOfFin s.2.2 i)
  ext x
  simp only [Finset.mem_erase]
  tauto

variable (R : Type v) [Ring R]

private noncomputable def doubleTerm (n : ℕ) (s : Face K (n + 2))
    (x : Fin (n + 3) × Fin (n + 2)) : Chain K R n :=
  Finsupp.single
    (deletedFace K n (deletedFace K (n + 1) s x.1) x.2)
    ((-1 : R) ^ (x.1 : ℕ) * (-1 : R) ^ (x.2 : ℕ))

private theorem doubleTerm_pair (n : ℕ) (s : Face K (n + 2))
    (x : Fin (n + 3) × Fin (n + 2)) :
    doubleTerm K R n s x + doubleTerm K R n s (swapDeletion (n + 1) x) = 0 := by
  rcases x with ⟨i, j⟩
  have hface := deletedFace_twice K n s i j
  dsimp only [doubleTerm, swapDeletion, Prod.fst, Prod.snd]
  rw [← hface]
  rw [← pow_add, ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove]
  simp

private theorem boundary_on_signed_sum (n : ℕ) (s : Face K (n + 2)) :
    boundary K R n
      (∑ i : Fin (n + 3),
        Finsupp.single (deletedFace K (n + 1) s i) ((-1 : R) ^ (i : ℕ))) =
      ∑ x : Fin (n + 3) × Fin (n + 2), doubleTerm K R n s x := by
  rw [Fintype.sum_prod_type]
  simp only [map_sum, boundary_single, Finset.smul_sum, Finsupp.smul_single]
  rfl

private theorem double_sum_zero (n : ℕ) (s : Face K (n + 2)) :
    ∑ x : Fin (n + 3) × Fin (n + 2), doubleTerm K R n s x = 0 := by
  classical
  simpa using (Finset.sum_involution
    (s := (Finset.univ : Finset (Fin (n + 3) × Fin (n + 2))))
    (f := doubleTerm K R n s) (g := fun x _ => swapDeletion (n + 1) x)
    (fun x _ => doubleTerm_pair K R n s x)
    (fun x _ _ => swapDeletion_ne (n + 1) x)
    (fun _ _ => Finset.mem_univ _)
    (fun x _ => swapDeletion_involutive (n + 1) x))

/-- The signed boundary on ordered faces squares to zero.
@isnad1 id=eq.0h4v.s9.58e76039c41a from=translated src=- shape=bc335f70 vocab=b67c5c0a
-/
theorem boundary_comp_boundary (n : ℕ) :
    (boundary K R n).comp (boundary K R (n + 1)) = 0 := by
  apply Finsupp.lhom_ext
  intro s a
  change boundary K R n (boundary K R (n + 1) (Finsupp.single s a)) = 0
  rw [boundary_single K R (n + 1) s a, map_smul,
    boundary_on_signed_sum K R n s, double_sum_zero K R n s]
  simp

open CategoryTheory Module

/-- The ordinary unaugmented chain complex on the ordered faces.-/
noncomputable def simplicialChainComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Chain K R n))
    (fun n => ModuleCat.ofHom (boundary K R n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact boundary_comp_boundary K R n)

/--
@isnad1 id=eq.0h4v.s6.ee7602fd47f5 from=translated src=- shape=2b00f4b3 vocab=c263d6f3
-/
@[simp]
theorem simplicialChainComplex_X (n : ℕ) :
    (simplicialChainComplex K R).X n = ModuleCat.of R (Chain K R n) :=
  rfl

/--
@isnad1 id=eq.0h4v.s8.98ba730b3ee2 from=translated src=- shape=5f48366e vocab=ed45bd2b
-/
@[simp]
theorem simplicialChainComplex_d (n : ℕ) :
    (simplicialChainComplex K R).d (n + 1) n =
      ModuleCat.ofHom (boundary K R n) := by
  exact ChainComplex.of_d (fun q => ModuleCat.of R (Chain K R q))
    (fun q => ModuleCat.ofHom (boundary K R q)) n

/--
@isnad1 id=eq.0h4v.s8.0593320d2e0d from=translated src=- shape=3760d109 vocab=52cc4fe1
-/
@[simp]
theorem simplicialChainComplex_d_zero (j : ℕ) :
    (simplicialChainComplex K R).d 0 j = 0 := by
  exact ChainComplex.of_d_ne (fun q => ModuleCat.of R (Chain K R q))
    (fun q => ModuleCat.ofHom (boundary K R q)) (by omega)

section Fixtures

private abbrev triangleK : PreAbstractSimplicialComplex (Fin 3) := ⊤

private def triangleVertex (i : Fin 3) : Face triangleK 0 :=
  ⟨{i}, by change ({i} : Finset (Fin 3)).Nonempty; simp, by simp⟩
private def triangleEdge01 : Face triangleK 1 :=
  ⟨{0, 1}, by change ({0, 1} : Finset (Fin 3)).Nonempty; decide, by decide⟩
private def triangleEdge02 : Face triangleK 1 :=
  ⟨{0, 2}, by change ({0, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
private def triangleEdge12 : Face triangleK 1 :=
  ⟨{1, 2}, by change ({1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩
private def triangleFace : Face triangleK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 3)).Nonempty; decide, by decide⟩

private abbrev tetraK : PreAbstractSimplicialComplex (Fin 4) := ⊤

private def tetrahedron : Face tetraK 3 :=
  ⟨{0, 1, 2, 3}, by change ({0, 1, 2, 3} : Finset (Fin 4)).Nonempty; decide,
    by decide⟩

private def triangle012 : Face tetraK 2 :=
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle013 : Face tetraK 2 :=
  ⟨{0, 1, 3}, by change ({0, 1, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle023 : Face tetraK 2 :=
  ⟨{0, 2, 3}, by change ({0, 2, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩
private def triangle123 : Face tetraK 2 :=
  ⟨{1, 2, 3}, by change ({1, 2, 3} : Finset (Fin 4)).Nonempty; decide, by decide⟩

end Fixtures

end TDA.Simplicial
