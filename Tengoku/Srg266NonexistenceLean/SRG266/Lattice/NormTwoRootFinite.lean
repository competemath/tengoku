/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRoots
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Dual
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

/--
@isnad1 id=le.0h3v.s8.fc282615704a from=translated src=- shape=287c92f3 vocab=1e54a0e1
-/
theorem pairing_self_nonneg {n : ℕ} (L : PDUnimodularLattice n)
    (x : L.carrier) : 0 ≤ L.pairing x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (L.positiveDefinite x hx).le

/--
@isnad1 id=finite.0h2v.s3.d74df322ed27 from=translated src=- shape=1f8e965c vocab=647941ed
-/
theorem normTwoRoot_finite {n : ℕ} (L : PDUnimodularLattice n) :
    Finite (NormTwoRoot L) := by
  let := L.moduleFree
  let := L.moduleFinite
  let b : Module.Basis (Fin n) ℤ L.carrier :=
    Module.finBasisOfFinrankEq ℤ L.carrier L.rank
  choose d hd using fun i : Fin n => L.unimodular.2 (b.coord i)
  let bound : Fin n → ℤ := fun i => 2 * L.pairing (d i) (d i) + 1
  let BoxCoord : Fin n → Type := fun i =>
    {a : ℤ // a ∈ Set.Icc (-bound i) (bound i)}
  let (i : Fin n) : Fintype (BoxCoord i) :=
    (Set.finite_Icc (-bound i) (bound i)).fintype
  let encode : NormTwoRoot L → (∀ i, BoxCoord i) := fun r i =>
    ⟨b.equivFun r.1 i, by
      have hcoord : b.equivFun r.1 i = L.pairing (d i) r.1 := by
        change b.coord i r.1 = L.pairing (d i) r.1
        exact (DFunLike.congr_fun (hd i) r.1).symm
      have hcs := L.pairing.apply_sq_le_of_symm
        (pairing_self_nonneg L)
        (LinearMap.BilinForm.isSymm_iff.mp L.symmetric) (d i) r.1
      rw [r.2] at hcs
      have hq := pairing_self_nonneg L (d i)
      change -bound i ≤ b.equivFun r.1 i ∧
        b.equivFun r.1 i ≤ bound i
      dsimp only [bound]
      rw [hcoord]
      constructor <;> nlinarith⟩
  exact Finite.of_injective encode fun r s hrs => by
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    exact congrArg Subtype.val (congrFun hrs i)

/--
@isnad1 id=finite.0h2v.s3.d74df322ed27 from=translated src=- shape=1f8e965c vocab=647941ed
-/
noncomputable instance normTwoRootFinite {n : ℕ}
    (L : PDUnimodularLattice n) : Finite (NormTwoRoot L) :=
  normTwoRoot_finite L

noncomputable instance normTwoRootFintype {n : ℕ}
    (L : PDUnimodularLattice n) : Fintype (NormTwoRoot L) :=
  Fintype.ofFinite _

end Lattice
end SRG266
