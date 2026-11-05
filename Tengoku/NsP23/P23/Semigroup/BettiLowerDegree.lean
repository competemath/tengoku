import Tengoku.NsP23.P23.Semigroup.BettiRelationSpace
import Tengoku.Seed.LinearAlgebra.Quotient.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact lower-degree quotient for one toric factorization fiber

This module repairs the missing converse in Run24.  The actual preimage of
`lowerToricIdeal d` under the degree-`d` fiber-polynomial realization is shown
to equal the kernel of the component-sum map.
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

open FourGeneratedNumericalSemigroup

variable {k : Type*} [Field k]

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

/-- The frozen Run24 fiber-polynomial realization, restricted to relations.-/
def fiberRelationPolynomial (d : ℕ) :
    D.FiberRelationSpace k d →ₗ[k] FourPoly k :=
  (D.fiberPolynomial (k := k) d).comp
    (D.FiberRelationSpace k d).subtype

/--
@isnad1 id=eq.0h4v.s11.cc105d20dcbc from=translated src=- shape=6a8fe868 vocab=4ecabc36
-/
@[simp] theorem fiberRelationPolynomial_apply (d : ℕ)
    (a : D.FiberRelationSpace k d) :
    D.fiberRelationPolynomial (k := k) d a =
      D.fiberPolynomial (k := k) d a.1 := rfl

/-- Actual degree-`d` relations coming from all strictly lower weighted
degrees, defined intrinsically as a preimage of the genuine lower toric
ideal.-/
def ActualLowerDegreeRelationSubmodule (d : ℕ) :
    Submodule k (D.FiberRelationSpace k d) :=
  Submodule.comap (D.fiberRelationPolynomial (k := k) d)
    ((D.lowerToricIdeal (k := k) d).restrictScalars k)

/--
@isnad1 id=iff.0h4v.s11.72265d9e356c from=translated src=- shape=cd5d28e3 vocab=6298a2f0
-/
@[simp] theorem mem_actualLowerDegreeRelationSubmodule_iff (d : ℕ)
    (a : D.FiberRelationSpace k d) :
    a ∈ D.ActualLowerDegreeRelationSubmodule (k := k) d ↔
      D.fiberPolynomial (k := k) d a.1 ∈ D.lowerToricIdeal (k := k) d :=
  Iff.rfl

/-- Sum degree-`d` polynomial coefficients separately over every connected
component of the factorization graph.-/
def degreeComponentCoeffVector (d : ℕ) :
    FourPoly k →ₗ[k] (D.BettiComponent d → k) := by
  classical
  exact {
    toFun := fun p C => ∑ u with D.componentOf u = C,
      MvPolynomial.coeff u.1 p
    map_add' := by
      intro p q
      funext C
      simp [MvPolynomial.coeff_add, Finset.sum_add_distrib]
    map_smul' := by
      intro r p
      funext C
      simp only [MvPolynomial.coeff_smul, Pi.smul_apply, RingHom.id_apply,
        smul_eq_mul]
      exact (Finset.mul_sum _ _ _).symm }

def degreeComponentCoeff (d : ℕ) (C : D.BettiComponent d) :
    FourPoly k →ₗ[k] k :=
  LinearMap.proj C |>.comp (D.degreeComponentCoeffVector (k := k) d)

/--
@isnad1 id=eq.0h4v.s9.1c3bd37eb90d from=translated src=- shape=bce500fe vocab=15ae78f3
-/
theorem degreeComponentCoeffVector_fiberPolynomial (d : ℕ)
    (a : D.FiberCoeff k d) :
    D.degreeComponentCoeffVector (k := k) d
        (D.fiberPolynomial (k := k) d a) =
      D.componentCoeff (k := k) d a := by
  classical
  funext C
  simp only [degreeComponentCoeffVector, LinearMap.coe_mk, AddHom.coe_mk,
    componentCoeff]
  apply Finset.sum_congr rfl
  intro u _
  exact D.coeff_fiberPolynomial d a u

/-- Add one exponent vector to a vertex in a smaller fiber.-/
def shiftedFactorization {e d : ℕ} (u : D.FactorizationAt e)
    (w : Fin 4 →₀ ℕ) (hdeg : D.weightedDegree w + e = d) :
    D.FactorizationAt d := by
  refine ⟨w + u.1, D.mem_factorizations.mpr ?_⟩
  have hu := D.factorizationAt_degree u
  change weightedDegreeOf D.n u.1 = e at hu
  change weightedDegreeOf D.n (w + u.1) = d
  rw [weightedDegreeOf_add, hu, hdeg]

/--
@isnad1 id=eq.2h6v.s6.30a12c43be8f from=translated src=- shape=a0e98c1b vocab=227bf3bb
-/
theorem shiftedFactorizations_sameComponent {e d : ℕ}
    (u v : D.FactorizationAt e) (w : Fin 4 →₀ ℕ)
    (hdeg : D.weightedDegree w + e = d) (hw : w ≠ 0) :
    D.componentOf (D.shiftedFactorization u w hdeg) =
      D.componentOf (D.shiftedFactorization v w hdeg) := by
  classical
  obtain ⟨j, hjmem⟩ := Finsupp.support_nonempty_iff.mpr hw
  have hwj : 0 < w j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hjmem)
  let su := D.shiftedFactorization u w hdeg
  let sv := D.shiftedFactorization v w hdeg
  by_cases huv : su = sv
  · exact congrArg D.componentOf huv
  · apply (D.componentOf_eq_iff_reachable su sv).2
    exact ((D.factorizationGraph_adj su sv).2 ⟨huv, j,
      by
        change 0 < w j + u.1 j
        omega,
      by
        change 0 < w j + v.1 j
        omega⟩).reachable

/--
@isnad1 id=eq.1h5v.s9.7275a9a9e918 from=translated src=- shape=a77bcb24 vocab=92691586
-/
theorem degreeComponentCoeffVector_monomial_of_degree_ne
    (d : ℕ) (w : Fin 4 →₀ ℕ) (r : k)
    (hdeg : D.weightedDegree w ≠ d) :
    D.degreeComponentCoeffVector (k := k) d (MvPolynomial.monomial w r) = 0 := by
  classical
  funext C
  simp only [degreeComponentCoeffVector, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro u _
  have huw : u.1 ≠ w := by
    intro h
    apply hdeg
    rw [← D.factorizationAt_degree u, h]
  simp [MvPolynomial.coeff_monomial, huw.symm]

/--
@isnad1 id=eq.1h8v.s9.7486bf866519 from=translated src=- shape=2bd8c0e8 vocab=f18a3fe7
-/
theorem degreeComponentCoeffVector_monomial_mul_fiberBinomial
    {e d : ℕ} (hed : e < d) (u v : D.FactorizationAt e)
    (w : Fin 4 →₀ ℕ) (r : k) :
    D.degreeComponentCoeffVector (k := k) d
      (MvPolynomial.monomial w r * D.fiberBinomial (k := k) u v) = 0 := by
  classical
  by_cases hdeg : D.weightedDegree w + e = d
  · have hw : w ≠ 0 := by
      intro hw
      subst w
      simp only [weightedDegreeOf_zero, zero_add] at hdeg
      omega
    let su := D.shiftedFactorization u w hdeg
    let sv := D.shiftedFactorization v w hdeg
    have hcomp : D.componentOf su = D.componentOf sv :=
      D.shiftedFactorizations_sameComponent u v w hdeg hw
    have hpoly :
        MvPolynomial.monomial w r * D.fiberBinomial (k := k) u v =
          r • D.fiberBinomial (k := k) su sv := by
      simp [fiberBinomial, fiberMonomial, su, sv, shiftedFactorization,
        mul_sub, MvPolynomial.monomial_mul_monomial, smul_sub,
        MvPolynomial.smul_monomial, smul_eq_mul]
    rw [hpoly, ← D.fiberPolynomial_fiberDelta su sv, ← map_smul,
      D.degreeComponentCoeffVector_fiberPolynomial]
    have hcomponent :
        D.componentCoeff (k := k) d (D.fiberDelta (k := k) su sv) =
          D.componentDelta (k := k) su sv := by
      exact congrArg Subtype.val
        (D.fiberToComponentRelation_fiberDelta (k := k) su sv)
    rw [map_smul, hcomponent]
    simp [componentDelta, hcomp]
  · have huDegree : D.weightedDegree (w + u.1) ≠ d := by
      have hu := D.factorizationAt_degree u
      change weightedDegreeOf D.n u.1 = e at hu
      change weightedDegreeOf D.n (w + u.1) ≠ d
      rw [weightedDegreeOf_add, hu]
      exact hdeg
    have hvDegree : D.weightedDegree (w + v.1) ≠ d := by
      have hv := D.factorizationAt_degree v
      change weightedDegreeOf D.n v.1 = e at hv
      change weightedDegreeOf D.n (w + v.1) ≠ d
      rw [weightedDegreeOf_add, hv]
      exact hdeg
    have hpoly :
        MvPolynomial.monomial w r * D.fiberBinomial (k := k) u v =
          MvPolynomial.monomial (w + u.1) r -
            MvPolynomial.monomial (w + v.1) r := by
      simp [fiberBinomial, fiberMonomial, mul_sub,
        MvPolynomial.monomial_mul_monomial]
    rw [hpoly, map_sub,
      D.degreeComponentCoeffVector_monomial_of_degree_ne d (w + u.1) r huDegree,
      D.degreeComponentCoeffVector_monomial_of_degree_ne d (w + v.1) r hvDegree,
      sub_zero]

/--
@isnad1 id=eq.1h7v.s8.96a30af667db from=translated src=- shape=e0c6510b vocab=974f3f9d
-/
theorem degreeComponentCoeffVector_mul_fiberBinomial
    {e d : ℕ} (hed : e < d) (u v : D.FactorizationAt e)
    (p : FourPoly k) :
    D.degreeComponentCoeffVector (k := k) d
      (p * D.fiberBinomial (k := k) u v) = 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro w _
  exact D.degreeComponentCoeffVector_monomial_mul_fiberBinomial
    (k := k) hed u v w (MvPolynomial.coeff w p)

/-- Every genuine consequence of strictly lower-degree fiber binomials has
zero coefficient sum in each degree-`d` graph component.
@isnad1 id=eq.1h4v.s9.03ce082f9a4a from=translated src=- shape=6d4b4edc vocab=f33518b4
-/
theorem mem_lowerToricIdeal_componentCoeff_zero (d : ℕ) (p : FourPoly k)
    (hp : p ∈ D.lowerToricIdeal (k := k) d) :
    D.degreeComponentCoeffVector (k := k) d p = 0 := by
  classical
  unfold lowerToricIdeal at hp
  have hall : ∀ q : FourPoly k,
      D.degreeComponentCoeffVector (k := k) d (q * p) = 0 := by
    refine Submodule.span_induction
      (p := fun x (_hx : x ∈ Submodule.span (FourPoly k)
        {p | ∃ (e : ℕ) (_ : e < d) (u v : D.FactorizationAt e),
          p = D.fiberBinomial (k := k) u v}) =>
        ∀ q : FourPoly k,
          D.degreeComponentCoeffVector (k := k) d (q * x) = 0)
      ?_ ?_ ?_ ?_ hp
    · intro x hx
      rcases hx with ⟨e, hed, u, v, rfl⟩
      intro q
      exact D.degreeComponentCoeffVector_mul_fiberBinomial hed u v q
    · intro q
      simp
    · intro x y hx hy ihx ihy q
      rw [mul_add, map_add, ihx q, ihy q, add_zero]
    · intro a x hx ihx q
      change D.degreeComponentCoeffVector (k := k) d (q * (a * x)) = 0
      rw [← mul_assoc]
      exact ihx (q * a)
  simpa using hall 1

/-- The missing Run24 direction: membership in the actual lower ideal forces
all component sums to vanish.
@isnad1 id=mem.1h4v.s11.9f9b6145335d from=translated src=- shape=dbf88ffe vocab=0ef486f8
-/
theorem componentKernel_of_fiberPolynomial_mem_lower {d : ℕ}
    (a : D.FiberRelationSpace k d)
    (ha : D.fiberPolynomial (k := k) d a.1 ∈
      D.lowerToricIdeal (k := k) d) :
    a ∈ LinearMap.ker (D.fiberToComponentRelation (k := k) d) := by
  have hz := D.mem_lowerToricIdeal_componentCoeff_zero d
    (D.fiberPolynomial (k := k) d a.1) ha
  rw [D.degreeComponentCoeffVector_fiberPolynomial] at hz
  change D.fiberToComponentRelation (k := k) d a = 0
  apply Subtype.ext
  exact hz

/--
@isnad1 id=iff.0h4v.s11.44dc084f28c8 from=translated src=- shape=7b4fbb18 vocab=0ef486f8
-/
theorem fiberPolynomial_mem_lower_iff_componentKernel {d : ℕ}
    (a : D.FiberRelationSpace k d) :
    D.fiberPolynomial (k := k) d a.1 ∈ D.lowerToricIdeal (k := k) d ↔
      a ∈ LinearMap.ker (D.fiberToComponentRelation (k := k) d) := by
  constructor
  · exact D.componentKernel_of_fiberPolynomial_mem_lower a
  · exact D.fiberPolynomial_mem_lower_of_componentKernel a

/-- The load-bearing repair equality.
@isnad1 id=eq.0h3v.s10.3a7ac6ae04d0 from=translated src=- shape=e3835d6a vocab=56bb9115
-/
theorem actualLowerDegreeRelationSubmodule_eq_componentKernel (d : ℕ) :
    D.ActualLowerDegreeRelationSubmodule (k := k) d =
      LinearMap.ker (D.fiberToComponentRelation (k := k) d) := by
  ext a
  exact D.fiberPolynomial_mem_lower_iff_componentKernel a

/-- The genuine degree-new quotient by the actual preimage of all strictly
lower-degree toric consequences.-/
abbrev ActualDegreeNewToricRelationSpace (k : Type*) [Field k] (d : ℕ) :=
  D.FiberRelationSpace k d ⧸ D.ActualLowerDegreeRelationSubmodule (k := k) d

def actualDegreeNewMk (d : ℕ) :
    D.FiberRelationSpace k d →ₗ[k] D.ActualDegreeNewToricRelationSpace k d :=
  (D.ActualLowerDegreeRelationSubmodule (k := k) d).mkQ

def actualDegreeNewEquivRun24DegreeNew (d : ℕ) :
    D.ActualDegreeNewToricRelationSpace k d ≃ₗ[k]
      D.DegreeNewToricRelationSpace k d :=
  Submodule.quotEquivOfEq _ _
    (D.actualLowerDegreeRelationSubmodule_eq_componentKernel (k := k) d)

/--
@isnad1 id=eq.0h4v.s14.50fcbce12575 from=translated src=- shape=50215582 vocab=27a1ce94
-/
@[simp] theorem actualDegreeNewEquivRun24DegreeNew_mk (d : ℕ)
    (a : D.FiberRelationSpace k d) :
    D.actualDegreeNewEquivRun24DegreeNew (k := k) d
        (D.actualDegreeNewMk (k := k) d a) =
      D.degreeNewMk (k := k) d a := by
  exact Submodule.quotEquivOfEq_mk _ _ _ _

def actualDegreeNewEquivComponentRelation (d : ℕ) :
    D.ActualDegreeNewToricRelationSpace k d ≃ₗ[k]
      D.ComponentRelationSpace k d :=
  (D.actualDegreeNewEquivRun24DegreeNew (k := k) d).trans
    (D.degreeNewToricRelationSpaceEquiv (k := k) d)

/--
@isnad1 id=eq.1h3v.s9.9a1651acc7ec from=translated src=- shape=81103fe5 vocab=1da5b8a7
-/
theorem actualDegreeNewToricRelationSpace_finrank {d : ℕ}
    (hd : D.IsBettiDegree d) :
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) =
      D.bettiContribution d := by
  rw [(D.actualDegreeNewEquivComponentRelation (k := k) d).finrank_eq]
  exact D.componentRelationSpace_finrank hd

/--
@isnad1 id=eq.1h3v.s9.75e2c5a5d32a from=translated src=- shape=87135772 vocab=902c19f9
-/
theorem actualDegreeNewToricRelationSpace_finrank_eq_componentCount_sub_one
    {d : ℕ} (hd : D.IsBettiDegree d) :
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) =
      D.componentCount d - 1 := by
  rw [D.actualDegreeNewToricRelationSpace_finrank (k := k) hd]
  rfl

def actualConnectorClass {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) :
    D.ActualDegreeNewToricRelationSpace k d :=
  D.actualDegreeNewMk (k := k) d (D.connectorFiberRelation (k := k) hd e)

/--
@isnad1 id=eq.1h4v.s13.3159169b9864 from=translated src=- shape=1d215eb3 vocab=d4330ef8
-/
@[simp] theorem actualEquivRun24_connectorClass {d : ℕ}
    (hd : D.IsBettiDegree d) (e : D.ComponentConnector hd) :
    D.actualDegreeNewEquivRun24DegreeNew (k := k) d
        (D.actualConnectorClass (k := k) hd e) =
      D.connectorClass (k := k) hd e := by
  simp [actualConnectorClass, connectorClass]

def actualConnectorClassBasis {d : ℕ} (hd : D.IsBettiDegree d) :
    Module.Basis (D.ComponentConnector hd) k
      (D.ActualDegreeNewToricRelationSpace k d) :=
  (D.connectorClassBasis (k := k) hd).map
    (D.actualDegreeNewEquivRun24DegreeNew (k := k) d).symm

/--
@isnad1 id=eq.1h4v.s10.fa30e8084240 from=translated src=- shape=46622520 vocab=dc213fd2
-/
@[simp] theorem actualConnectorClassBasis_apply {d : ℕ}
    (hd : D.IsBettiDegree d) (e : D.ComponentConnector hd) :
    D.actualConnectorClassBasis (k := k) hd e =
      D.actualConnectorClass (k := k) hd e := by
  apply (D.actualDegreeNewEquivRun24DegreeNew (k := k) d).injective
  simp [actualConnectorClassBasis]

/--
@isnad1 id=eq.1h3v.s11.156251fb9755 from=translated src=- shape=f40ade23 vocab=0c63f090
-/
theorem actualConnectorClass_span_eq_top {d : ℕ}
    (hd : D.IsBettiDegree d) :
    Submodule.span k (Set.range (D.actualConnectorClass (k := k) hd)) = ⊤ := by
  have hfun : D.actualConnectorClass (k := k) hd =
      fun e => D.actualConnectorClassBasis (k := k) hd e := by
    funext e
    exact (D.actualConnectorClassBasis_apply (k := k) hd e).symm
  rw [hfun]
  exact (D.actualConnectorClassBasis (k := k) hd).span_eq

def actualDegreeNewGeneratorFinset {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) :
    Finset (D.ActualDegreeNewToricRelationSpace k d) := by
  classical
  exact G.image (D.actualDegreeNewMk (k := k) d)

def GeneratesActualDegreeNewRelations {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) : Prop :=
  Submodule.span k (D.actualDegreeNewGeneratorFinset (k := k) G :
    Set (D.ActualDegreeNewToricRelationSpace k d)) = ⊤

/--
@isnad1 id=generate.1h3v.s4.b4cd9c1c32f8 from=translated src=- shape=0be45707 vocab=cf4e1416
-/
theorem actualConnectorRelationFinset_generates {d : ℕ}
    (hd : D.IsBettiDegree d) :
    D.GeneratesActualDegreeNewRelations
      (D.connectorRelationFinset (k := k) hd) := by
  classical
  unfold GeneratesActualDegreeNewRelations
  have hle :
      Submodule.span k (Set.range (D.actualConnectorClass (k := k) hd)) ≤
        Submodule.span k
          (D.actualDegreeNewGeneratorFinset (k := k)
            (D.connectorRelationFinset (k := k) hd) :
              Set (D.ActualDegreeNewToricRelationSpace k d)) := by
    rw [Submodule.span_le]
    rintro z ⟨e, rfl⟩
    apply Submodule.subset_span (R := k)
    show D.actualConnectorClass (k := k) hd e ∈
      D.actualDegreeNewGeneratorFinset (k := k)
        (D.connectorRelationFinset (k := k) hd)
    unfold actualDegreeNewGeneratorFinset actualConnectorClass
    apply Finset.mem_image.mpr
    refine ⟨D.connectorFiberRelation (k := k) hd e, ?_, rfl⟩
    unfold connectorRelationFinset
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  rw [D.actualConnectorClass_span_eq_top (k := k) hd] at hle
  exact top_unique hle

/--
@isnad1 id=le.2h4v.s9.6c3872b6519b from=translated src=- shape=496e7f09 vocab=5ff7579d
-/
theorem actualDegreeToricRelation_generator_card_lower_bound {d : ℕ}
    (hd : D.IsBettiDegree d) (G : Finset (D.FiberRelationSpace k d))
    (hG : D.GeneratesActualDegreeNewRelations (k := k) G) :
    D.bettiContribution d ≤ G.card := by
  rw [← D.actualDegreeNewToricRelationSpace_finrank (k := k) hd]
  classical
  unfold GeneratesActualDegreeNewRelations at hG
  have h := finrank_span_le_card (R := k)
    (D.actualDegreeNewGeneratorFinset (k := k) G :
      Set (D.ActualDegreeNewToricRelationSpace k d))
  rw [hG] at h
  calc
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) ≤
        (D.actualDegreeNewGeneratorFinset (k := k) G).card := by simpa using h
    _ ≤ G.card := by
      unfold actualDegreeNewGeneratorFinset
      exact Finset.card_image_le

/--
@isnad1 id=eq.1h3v.s8.f594e3efdb43 from=translated src=- shape=141fa38b vocab=c2759d57
-/
theorem actualConnectorRelationFinset_card_exact {d : ℕ}
    (hd : D.IsBettiDegree d) :
    (D.connectorRelationFinset (k := k) hd).card =
      D.bettiContribution d :=
  D.connectorRelationFinset_card_exact hd

/-- Literal polynomial-language generation in degree `d`: after subtracting
a combination of `G`, the fiber polynomial lies in the genuine lower toric
ideal.-/
def GeneratesDegreeDModuloLower {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) : Prop :=
  ∀ a : D.FiberRelationSpace k d,
    ∃ b : D.FiberRelationSpace k d,
      b ∈ Submodule.span k (G : Set (D.FiberRelationSpace k d)) ∧
      D.fiberPolynomial (k := k) d (a - b).1 ∈
        D.lowerToricIdeal (k := k) d

/--
@isnad1 id=iff.0h4v.s12.d8240d00dfcf from=translated src=- shape=97021931 vocab=785e81a4
-/
theorem generatesDegreeDModuloLower_iff_sup_span {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) :
    D.GeneratesDegreeDModuloLower (k := k) G ↔
      D.ActualLowerDegreeRelationSubmodule (k := k) d ⊔
        Submodule.span k (G : Set (D.FiberRelationSpace k d)) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro a _
    obtain ⟨b, hb, hab⟩ := h a
    have hdiff : a - b ∈
        D.ActualLowerDegreeRelationSubmodule (k := k) d :=
      (D.mem_actualLowerDegreeRelationSubmodule_iff d (a - b)).2 hab
    have hsum := Submodule.add_mem
      (D.ActualLowerDegreeRelationSubmodule (k := k) d ⊔
        Submodule.span k (G : Set (D.FiberRelationSpace k d)))
      (Submodule.mem_sup_left hdiff) (Submodule.mem_sup_right hb)
    simpa using hsum
  · intro htop a
    have ha : a ∈ D.ActualLowerDegreeRelationSubmodule (k := k) d ⊔
        Submodule.span k (G : Set (D.FiberRelationSpace k d)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨x, hx, b, hb, hxb⟩ := Submodule.mem_sup.mp ha
    refine ⟨b, hb, ?_⟩
    apply (D.mem_actualLowerDegreeRelationSubmodule_iff d (a - b)).1
    have hab : a - b = x := by
      rw [← hxb]
      abel
    simpa [hab] using hx

/--
@isnad1 id=iff.0h4v.s12.4997a6d23e6c from=translated src=- shape=97021931 vocab=de5e5e17
-/
theorem generatesActualDegreeNewRelations_iff_sup_span {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) :
    D.GeneratesActualDegreeNewRelations (k := k) G ↔
      D.ActualLowerDegreeRelationSubmodule (k := k) d ⊔
        Submodule.span k (G : Set (D.FiberRelationSpace k d)) = ⊤ := by
  classical
  unfold GeneratesActualDegreeNewRelations actualDegreeNewGeneratorFinset
  have hset :
      ((G.image (D.actualDegreeNewMk (k := k) d) :
          Finset (D.ActualDegreeNewToricRelationSpace k d)) :
          Set (D.ActualDegreeNewToricRelationSpace k d)) =
        D.actualDegreeNewMk (k := k) d ''
          (G : Set (D.FiberRelationSpace k d)) := by
    ext z
    simp
  rw [hset, ← Submodule.map_span]
  simpa [actualDegreeNewMk] using
    ((D.ActualLowerDegreeRelationSubmodule (k := k) d).map_mkQ_eq_top
      (Submodule.span k (G : Set (D.FiberRelationSpace k d))))

/--
@isnad1 id=iff.0h4v.s8.14d05720ff19 from=translated src=- shape=094d2a71 vocab=36dde54c
-/
theorem generatesDegreeDModuloLower_iff_actual {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) :
    D.GeneratesDegreeDModuloLower (k := k) G ↔
      D.GeneratesActualDegreeNewRelations (k := k) G := by
  rw [D.generatesDegreeDModuloLower_iff_sup_span,
    D.generatesActualDegreeNewRelations_iff_sup_span]

/--
@isnad1 id=le.2h4v.s9.9201674cb14b from=translated src=- shape=496e7f09 vocab=5b8c3935
-/
theorem degreeD_mod_lower_generator_card_lower_bound {d : ℕ}
    (hd : D.IsBettiDegree d) (G : Finset (D.FiberRelationSpace k d))
    (hG : D.GeneratesDegreeDModuloLower (k := k) G) :
    D.bettiContribution d ≤ G.card :=
  D.actualDegreeToricRelation_generator_card_lower_bound hd G
    ((D.generatesDegreeDModuloLower_iff_actual G).1 hG)

/-- Corrected load-bearing degree-local toric presentation package.-/
structure ExactToricBettiPresentationBridge (d : ℕ)
    (hd : D.IsBettiDegree d) : Prop where
  actualLowerExact :
    D.ActualLowerDegreeRelationSubmodule (k := k) d =
      LinearMap.ker (D.fiberToComponentRelation (k := k) d)
  actualQuotientEquiv :
    Nonempty (D.ActualDegreeNewToricRelationSpace k d ≃ₗ[k]
      D.ComponentRelationSpace k d)
  actualContributionExact :
    Module.finrank k (D.ActualDegreeNewToricRelationSpace k d) =
      D.componentCount d - 1
  actualConnectorBasis :
    Nonempty (Module.Basis (D.ComponentConnector hd) k
      (D.ActualDegreeNewToricRelationSpace k d))
  actualConnectorFamilyGenerates :
    D.GeneratesDegreeDModuloLower (k := k)
      (D.connectorRelationFinset (k := k) hd)
  actualUniversalLowerBound :
    ∀ G : Finset (D.FiberRelationSpace k d),
      D.GeneratesDegreeDModuloLower (k := k) G →
        D.bettiContribution d ≤ G.card
  connectorCardExact :
    (D.connectorRelationFinset (k := k) hd).card =
      D.bettiContribution d

/--
@isnad1 id=exacttor.1h3v.s4.da4f6c97fb85 from=translated src=- shape=21e1c7fe vocab=93628d8d
-/
theorem exactToricBettiPresentationBridge {d : ℕ}
    (hd : D.IsBettiDegree d) :
    D.ExactToricBettiPresentationBridge (k := k) d hd where
  actualLowerExact :=
    D.actualLowerDegreeRelationSubmodule_eq_componentKernel d
  actualQuotientEquiv :=
    ⟨D.actualDegreeNewEquivComponentRelation d⟩
  actualContributionExact :=
    D.actualDegreeNewToricRelationSpace_finrank_eq_componentCount_sub_one hd
  actualConnectorBasis :=
    ⟨D.actualConnectorClassBasis hd⟩
  actualConnectorFamilyGenerates :=
    (D.generatesDegreeDModuloLower_iff_actual
      (D.connectorRelationFinset (k := k) hd)).2
      (D.actualConnectorRelationFinset_generates hd)
  actualUniversalLowerBound := fun G hG =>
    D.degreeD_mod_lower_generator_card_lower_bound hd G hG
  connectorCardExact := D.actualConnectorRelationFinset_card_exact hd

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
