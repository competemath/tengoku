/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.NormTwoRootFinite
import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266
namespace Lattice

open Polynomial

noncomputable def coordinatePolynomial {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (x : L.carrier) : ℤ[X] :=
  ∑ i : Fin n, C (b.coord i x) * X ^ (i : ℕ)

/--
@isnad1 id=eq.0h5v.s7.d165b886814e from=translated src=- shape=51dda6c2 vocab=d50d5903
-/
theorem coordinatePolynomial_coeff {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (x : L.carrier) (i : Fin n) :
    (coordinatePolynomial b x).coeff i = b.coord i x := by
  classical
  simp [coordinatePolynomial, ← Fin.ext_iff]

/--
@isnad1 id=ne.1h4v.s7.6ddf740abab3 from=translated src=- shape=deb43dfd vocab=1888cb75
-/
theorem coordinatePolynomial_ne_zero {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    {x : L.carrier} (hx : x ≠ 0) : coordinatePolynomial b x ≠ 0 := by
  intro hp
  have hcoords : ∀ i : Fin n, b.coord i x = 0 := by
    intro i
    rw [← coordinatePolynomial_coeff b x i, hp, coeff_zero]
  apply hx
  apply b.equivFun.injective
  ext i
  simpa using hcoords i

noncomputable def coordinateEvaluation {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (a : ℤ) : L.carrier →ₗ[ℤ] ℤ :=
  ∑ i : Fin n, (a ^ (i : ℕ)) • b.coord i

/--
@isnad1 id=eq.0h5v.s7.e18bc60bac23 from=translated src=- shape=56870ac7 vocab=d15db8e8
-/
theorem coordinateEvaluation_apply {n : ℕ}
    {L : PDUnimodularLattice n} (b : Module.Basis (Fin n) ℤ L.carrier)
    (a : ℤ) (x : L.carrier) :
    coordinateEvaluation b a x = (coordinatePolynomial b x).eval a := by
  classical
  simp [coordinateEvaluation, coordinatePolynomial, Polynomial.eval_finsetSum, mul_comm]

noncomputable def rootAvoidancePolynomial {n : ℕ}
    (L : PDUnimodularLattice n)
    (b : Module.Basis (Fin n) ℤ L.carrier) : ℤ[X] :=
  ∏ r : NormTwoRoot L, coordinatePolynomial b r.1

/--
@isnad1 id=ne.0h3v.s5.e9c5b9da97b3 from=translated src=- shape=39050a89 vocab=27c39915
-/
theorem rootAvoidancePolynomial_ne_zero {n : ℕ}
    (L : PDUnimodularLattice n)
    (b : Module.Basis (Fin n) ℤ L.carrier) :
    rootAvoidancePolynomial L b ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro r _
  exact coordinatePolynomial_ne_zero b (normTwoRootVal_ne_zero r)

/--
@isnad1 id=ex.0h2v.s9.764e62179b6b from=translated src=- shape=8577e94c vocab=a4a1c8da
-/
theorem exists_rootSeparatingFunctional {n : ℕ}
    (L : PDUnimodularLattice n) :
    ∃ f : L.carrier →+ ℤ, ∀ r : NormTwoRoot L, f r.1 ≠ 0 := by
  classical
  let := L.moduleFree
  let := L.moduleFinite
  let b : Module.Basis (Fin n) ℤ L.carrier :=
    Module.finBasisOfFinrankEq ℤ L.carrier L.rank
  let p := rootAvoidancePolynomial L b
  have hp : p ≠ 0 := rootAvoidancePolynomial_ne_zero L b
  obtain ⟨a, _, ha⟩ := Set.infinite_univ.exists_notMem_finite
    (Polynomial.finite_setOfPred_isRoot hp)
  refine ⟨(coordinateEvaluation b a).toAddMonoidHom, ?_⟩
  intro r
  change coordinateEvaluation b a r.1 ≠ 0
  rw [coordinateEvaluation_apply]
  intro hr
  apply ha
  change (rootAvoidancePolynomial L b).eval a = 0
  rw [rootAvoidancePolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ r) hr

end Lattice
end SRG266
