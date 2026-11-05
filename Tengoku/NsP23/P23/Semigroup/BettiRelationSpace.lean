import Tengoku.NsP23.P23.Semigroup.ToricPresentation
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Isomorphisms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite relation spaces of one factorization fiber
-/

namespace P23.Semigroup

open scoped BigOperators

noncomputable section

open FourGeneratedNumericalSemigroup

variable {k : Type*} [Field k]

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

abbrev FiberCoeff (k : Type*) [Field k] (d : ℕ) := D.FactorizationAt d → k

def totalCoeff (d : ℕ) : D.FiberCoeff k d →ₗ[k] k where
  toFun a := ∑ u, a u
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm

abbrev FiberRelationSpace (k : Type*) [Field k] (d : ℕ) :=
  LinearMap.ker (D.totalCoeff (k := k) d)

def fiberPolynomial (d : ℕ) : D.FiberCoeff k d →ₗ[k] FourPoly k where
  toFun a := ∑ u, a u • D.fiberMonomial (k := k) u
  map_add' := by
    intro a b
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    simp [smul_eq_mul, smul_smul]

/--
@isnad1 id=eq.0h5v.s8.3a6c021b84d2 from=translated src=- shape=8af94b55 vocab=1be9f1c8
-/
@[simp] theorem coeff_fiberPolynomial (d : ℕ) (a : D.FiberCoeff k d)
    (u : D.FactorizationAt d) :
    MvPolynomial.coeff u.1 (D.fiberPolynomial (k := k) d a) = a u := by
  classical
  simp only [fiberPolynomial, LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, fiberMonomial, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    have hne : v.1 ≠ u.1 := fun h => hv (Subtype.ext h)
    simp [hne]
  · simp

/--
@isnad1 id=injectiv.0h3v.s8.0679711efa9e from=translated src=- shape=2a0e33f6 vocab=1038216d
-/
theorem fiberPolynomial_injective (d : ℕ) :
    Function.Injective (D.fiberPolynomial (k := k) d) := by
  intro a b h
  funext u
  exact (D.coeff_fiberPolynomial d a u).symm.trans
    ((congrArg (MvPolynomial.coeff u.1) h).trans (D.coeff_fiberPolynomial d b u))

/--
@isnad1 id=eq.0h4v.s10.5b4e8b3c91cc from=translated src=- shape=e836d074 vocab=7d5ba7a0
-/
theorem semigroupPolyMap_fiberPolynomial (d : ℕ) [Nonempty (D.FactorizationAt d)]
    (a : D.FiberCoeff k d) :
    D.semigroupPolyMap (D.fiberPolynomial (k := k) d a) =
      (D.totalCoeff (k := k) d a) •
        T (k := k) D ⟨d, (D.mem_Gamma_iff _).2
          ⟨(Classical.choice (inferInstance : Nonempty (D.FactorizationAt d))).1,
            D.factorizationAt_degree
              (Classical.choice (inferInstance : Nonempty (D.FactorizationAt d)))⟩⟩ := by
  classical
  simp only [fiberPolynomial, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    D.semigroupPolyMap_fiberMonomial, totalCoeff]
  rw [Finset.sum_smul]

/--
@isnad1 id=iff.0h4v.s9.cd186ff98cb3 from=translated src=- shape=93d7f205 vocab=46cb7402
-/
theorem fiberPolynomial_mem_toricIdeal_iff (d : ℕ) (a : D.FiberCoeff k d) :
    D.fiberPolynomial (k := k) d a ∈ D.toricIdeal (k := k) ↔
      a ∈ D.FiberRelationSpace k d := by
  classical
  cases isEmpty_or_nonempty (D.FactorizationAt d) with
  | inl hempty =>
      letI := hempty
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      simp [toricIdeal]
  | inr hnonempty =>
      letI := hnonempty
      change D.semigroupPolyMap (D.fiberPolynomial (k := k) d a) = 0 ↔
        D.totalCoeff (k := k) d a = 0
      rw [D.semigroupPolyMap_fiberPolynomial]
      constructor
      · intro h
        by_contra hn
        have hT : T (k := k) D ⟨d, (D.mem_Gamma_iff _).2
              ⟨(Classical.choice (inferInstance : Nonempty (D.FactorizationAt d))).1,
                D.factorizationAt_degree
                  (Classical.choice (inferInstance : Nonempty (D.FactorizationAt d)))⟩⟩ ≠ 0 := by
          simpa [T] using
            (Finsupp.single_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0) :
              AddMonoidAlgebra.single
                (⟨d, (D.mem_Gamma_iff _).2
                  ⟨(Classical.choice (inferInstance : Nonempty (D.FactorizationAt d))).1,
                    D.factorizationAt_degree
                      (Classical.choice (inferInstance : Nonempty (D.FactorizationAt d)))⟩⟩ : D.Gamma)
                (1 : k) ≠ 0)
        exact hT (smul_eq_zero.mp h |>.resolve_left hn)
      · intro h
        simp [h]

/-- Sum coefficients separately on every overlap component.-/
def componentCoeff (d : ℕ) :
    D.FiberCoeff k d →ₗ[k] (D.BettiComponent d → k) := by
  classical
  exact {
    toFun := fun a C => ∑ u with D.componentOf u = C, a u
    map_add' := by
      intro a b
      funext C
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      funext C
      simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
      exact (Finset.mul_sum _ _ _).symm }

def componentTotalCoeff (d : ℕ) : (D.BettiComponent d → k) →ₗ[k] k where
  toFun a := ∑ C, a C
  map_add' := by simp [Finset.sum_add_distrib]
  map_smul' := by
    intro r a
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    exact (Finset.mul_sum _ _ _).symm

abbrev ComponentRelationSpace (k : Type*) [Field k] (d : ℕ) :=
  LinearMap.ker (D.componentTotalCoeff (k := k) d)

/--
@isnad1 id=eq.0h4v.s9.6655695f9f89 from=translated src=- shape=11fa7004 vocab=f6f9e22d
-/
theorem component_total_componentCoeff (d : ℕ) (a : D.FiberCoeff k d) :
    D.componentTotalCoeff (k := k) d (D.componentCoeff (k := k) d a) =
      D.totalCoeff (k := k) d a := by
  classical
  simp only [componentTotalCoeff, componentCoeff, totalCoeff, LinearMap.coe_mk, AddHom.coe_mk]
  exact Finset.sum_fiberwise Finset.univ D.componentOf a

def fiberToComponentRelation (d : ℕ) :
    D.FiberRelationSpace k d →ₗ[k] D.ComponentRelationSpace k d :=
  LinearMap.codRestrict _
    ((D.componentCoeff (k := k) d).domRestrict (D.FiberRelationSpace k d))
    (by
      intro a
      change D.componentTotalCoeff (k := k) d (D.componentCoeff (k := k) d a.1) = 0
      rw [D.component_total_componentCoeff]
      exact a.2)

def fiberDelta {d : ℕ} (u v : D.FactorizationAt d) : D.FiberCoeff k d :=
  (Pi.single u (1 : k) : D.FactorizationAt d → k) -
    (Pi.single v (1 : k) : D.FactorizationAt d → k)

/--
@isnad1 id=mem.0h5v.s8.70de6a3e3f59 from=translated src=- shape=e1a7b675 vocab=0b66bcc4
-/
theorem fiberDelta_mem_relation {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberDelta (k := k) u v ∈ D.FiberRelationSpace k d := by
  classical
  change (∑ x, ((Pi.single u (1 : k) : D.FactorizationAt d → k) -
    (Pi.single v (1 : k) : D.FactorizationAt d → k)) x) = 0
  simp

def fiberDeltaRelation {d : ℕ} (u v : D.FactorizationAt d) :
    D.FiberRelationSpace k d :=
  ⟨D.fiberDelta (k := k) u v, D.fiberDelta_mem_relation u v⟩

/--
@isnad1 id=eq.0h5v.s8.efd0543141d5 from=translated src=- shape=e2ce1250 vocab=d4e44922
-/
@[simp] theorem fiberPolynomial_fiberDelta {d : ℕ} (u v : D.FactorizationAt d) :
    D.fiberPolynomial (k := k) d (D.fiberDelta (k := k) u v) =
      D.fiberBinomial (k := k) u v := by
  classical
  have hsingle (w : D.FactorizationAt d) :
      D.fiberPolynomial (k := k) d
          (Pi.single w (1 : k) : D.FactorizationAt d → k) =
        D.fiberMonomial (k := k) w := by
    ext q
    by_cases hq : q = w.1
    · subst q
      rw [D.coeff_fiberPolynomial]
      simp [Pi.single_apply, fiberMonomial]
    · simp [fiberPolynomial, fiberMonomial, Pi.single_apply, hq]
  change D.fiberPolynomial (k := k) d
      ((Pi.single u (1 : k) : D.FactorizationAt d → k) - Pi.single v 1) = _
  rw [map_sub, hsingle u, hsingle v]
  rfl

def componentDelta {d : ℕ} (u v : D.FactorizationAt d) :
    D.BettiComponent d → k := by
  classical
  exact Pi.single (D.componentOf u) 1 - Pi.single (D.componentOf v) 1

/--
@isnad1 id=mem.0h5v.s8.18ba1e327ec6 from=translated src=- shape=91d10426 vocab=105a4162
-/
theorem componentDelta_mem_relation {d : ℕ} (u v : D.FactorizationAt d) :
    D.componentDelta (k := k) u v ∈ D.ComponentRelationSpace k d := by
  classical
  change (∑ C, D.componentDelta (k := k) u v C) = 0
  simp [componentDelta]

/--
@isnad1 id=eq.0h5v.s11.334e02d7b888 from=translated src=- shape=ce8e30d6 vocab=e8b0fbfd
-/
theorem fiberToComponentRelation_fiberDelta {d : ℕ} (u v : D.FactorizationAt d) :
    (D.fiberToComponentRelation (k := k) d) (D.fiberDeltaRelation (k := k) u v) =
      ⟨D.componentDelta (k := k) u v, D.componentDelta_mem_relation u v⟩ := by
  classical
  apply Subtype.ext
  change D.componentCoeff (k := k) d (D.fiberDelta (k := k) u v) =
    D.componentDelta (k := k) u v
  simp only [fiberDelta, map_sub]
  congr 1 <;> funext C <;>
    simp [componentCoeff, componentDelta, Pi.single_apply, eq_comm]

def componentLift (d : ℕ) :
    (D.BettiComponent d → k) →ₗ[k] D.FiberCoeff k d := by
  classical
  exact {
    toFun := fun b => ∑ C, b C •
      (Pi.single (D.componentRepresentative C) (1 : k) : D.FactorizationAt d → k)
    map_add' := by
      intro a b
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro r a
      simp only [Pi.smul_apply, RingHom.id_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro C _
      simp [smul_eq_mul, smul_smul] }

def componentSingle {d : ℕ} (C : D.BettiComponent d) : D.BettiComponent d → k := by
  classical
  exact Pi.single C 1

/--
@isnad1 id=eq.0h4v.s8.8cc0196e6a83 from=translated src=- shape=4196b679 vocab=bdd9d7fa
-/
theorem componentCoeff_single (d : ℕ) (u : D.FactorizationAt d) :
    D.componentCoeff (k := k) d
        (Pi.single u (1 : k) : D.FactorizationAt d → k) =
      D.componentSingle (k := k) (D.componentOf u) := by
  classical
  funext C
  simp [componentCoeff, componentSingle, Pi.single_apply, eq_comm]

/--
@isnad1 id=eq.0h4v.s9.27b87e89bfd1 from=translated src=- shape=2fde5afc vocab=e7aee691
-/
theorem componentCoeff_componentLift (d : ℕ) (b : D.BettiComponent d → k) :
    D.componentCoeff (k := k) d (D.componentLift (k := k) d b) = b := by
  classical
  simp only [componentLift, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    D.componentCoeff_single]
  funext C
  simp [componentSingle, Pi.single_apply, D.componentRepresentative_component]

def componentRelationLift (d : ℕ) :
    D.ComponentRelationSpace k d →ₗ[k] D.FiberRelationSpace k d :=
  LinearMap.codRestrict _
    ((D.componentLift (k := k) d).domRestrict (D.ComponentRelationSpace k d))
    (by
      intro b
      change D.totalCoeff (k := k) d (D.componentLift (k := k) d b.1) = 0
      rw [← D.component_total_componentCoeff, D.componentCoeff_componentLift]
      exact b.2)

/--
@isnad1 id=eq.0h4v.s12.083b709f43f7 from=translated src=- shape=725d60bf vocab=b91f168f
-/
theorem fiberToComponentRelation_componentRelationLift (d : ℕ)
    (b : D.ComponentRelationSpace k d) :
    D.fiberToComponentRelation (k := k) d (D.componentRelationLift (k := k) d b) = b := by
  apply Subtype.ext
  exact D.componentCoeff_componentLift d b.1

/--
@isnad1 id=surjecti.0h3v.s11.7d11cc67139a from=translated src=- shape=98feb356 vocab=c3db03da
-/
theorem fiberToComponentRelation_surjective (d : ℕ) :
    Function.Surjective (D.fiberToComponentRelation (k := k) d) := by
  intro b
  exact ⟨D.componentRelationLift (k := k) d b,
    D.fiberToComponentRelation_componentRelationLift d b⟩

/--
@isnad1 id=surjecti.1h3v.s7.2970dbc3aee0 from=translated src=- shape=ed8c74d2 vocab=d5c802a0
-/
theorem componentTotalCoeff_surjective {d : ℕ} (hd : D.IsBettiDegree d) :
    Function.Surjective (D.componentTotalCoeff (k := k) d) := by
  classical
  intro r
  let C := D.rootComponent hd
  refine ⟨Pi.single C r, ?_⟩
  simp [componentTotalCoeff, Pi.single_apply]

/--
@isnad1 id=eq.1h3v.s8.55cf24bafcaf from=translated src=- shape=36f6624e vocab=2cc71b77
-/
theorem componentRelationSpace_finrank {d : ℕ} (hd : D.IsBettiDegree d) :
    Module.finrank k (D.ComponentRelationSpace k d) = D.bettiContribution d := by
  classical
  have hsurj := D.componentTotalCoeff_surjective (k := k) hd
  have hrange : LinearMap.range (D.componentTotalCoeff (k := k) d) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim := (D.componentTotalCoeff (k := k) d).finrank_range_add_finrank_ker
  rw [hrange] at hdim
  simp at hdim
  change 1 + Module.finrank k (D.ComponentRelationSpace k d) =
    Fintype.card (D.BettiComponent d) at hdim
  unfold bettiContribution componentCount
  omega

/-- The genuine degree-new quotient, not a dimension-indexed surrogate.-/
abbrev DegreeNewToricRelationSpace (k : Type*) [Field k] (d : ℕ) :=
  D.FiberRelationSpace k d ⧸ LinearMap.ker (D.fiberToComponentRelation (k := k) d)

def degreeNewMk (d : ℕ) :
    D.FiberRelationSpace k d →ₗ[k] D.DegreeNewToricRelationSpace k d :=
  (LinearMap.ker (D.fiberToComponentRelation (k := k) d)).mkQ

def degreeNewToricRelationSpaceEquiv (d : ℕ) :
    D.DegreeNewToricRelationSpace k d ≃ₗ[k] D.ComponentRelationSpace k d :=
  (D.fiberToComponentRelation (k := k) d).quotKerEquivOfSurjective
    (D.fiberToComponentRelation_surjective d)

/--
@isnad1 id=eq.1h3v.s11.458ffa374a8b from=translated src=- shape=87135772 vocab=14215b1f
-/
theorem toricBettiContribution_eq_componentCount_sub_one {d : ℕ}
    (hd : D.IsBettiDegree d) :
    Module.finrank k (D.DegreeNewToricRelationSpace k d) =
      D.componentCount d - 1 := by
  rw [(D.degreeNewToricRelationSpaceEquiv (k := k) d).finrank_eq]
  exact D.componentRelationSpace_finrank hd

def connectorFiberRelation {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) : D.FiberRelationSpace k d :=
  D.fiberDeltaRelation (k := k) (D.connectorEndpoints hd e).1
    (D.connectorEndpoints hd e).2

def connectorClass {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) : D.DegreeNewToricRelationSpace k d :=
  D.degreeNewMk (k := k) d (D.connectorFiberRelation (k := k) hd e)

/--
@isnad1 id=eq.1h4v.s13.73266f90e35c from=translated src=- shape=92652f13 vocab=f4bff38c
-/
theorem degreeNewEquiv_connectorClass {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) :
    D.degreeNewToricRelationSpaceEquiv (k := k) d (D.connectorClass (k := k) hd e) =
      ⟨D.componentDelta (k := k) (D.connectorEndpoints hd e).1
          (D.connectorEndpoints hd e).2,
        D.componentDelta_mem_relation _ _⟩ := by
  unfold connectorClass degreeNewMk degreeNewToricRelationSpaceEquiv
  change ((D.fiberToComponentRelation (k := k) d).quotKerEquivOfSurjective _)
      (Submodule.Quotient.mk (D.connectorFiberRelation (k := k) hd e)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact D.fiberToComponentRelation_fiberDelta _ _

/--
@isnad1 id=linearin.1h3v.s11.c3c010c7f3a8 from=translated src=- shape=6758ddba vocab=44672b67
-/
theorem connectorClass_linearIndependent {d : ℕ} (hd : D.IsBettiDegree d) :
    LinearIndependent k (D.connectorClass (k := k) hd) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g h e
  have hmap := congrArg (D.degreeNewToricRelationSpaceEquiv (k := k) d) h
  simp only [map_sum, map_smul, map_zero, D.degreeNewEquiv_connectorClass] at hmap
  have hcoord := congrArg
    (fun z : D.ComponentRelationSpace k d => z.1 e.1) hmap
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
    Pi.smul_apply, Submodule.coe_zero, Pi.zero_apply] at hcoord
  have heroot : e.1 ≠ D.rootComponent hd := e.2
  have hends := D.connectorEndpoints_components hd e
  simp [componentDelta, componentSingle, Pi.single_apply, heroot,
    D.connectorEndpoints_components, Subtype.ext_iff] at hcoord
  have heq (x : D.ComponentConnector hd) : (e.1 = x.1) ↔ e = x := by
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  simp_rw [heq] at hcoord
  simpa using hcoord

/--
@isnad1 id=eq.1h3v.s13.45c254e47b35 from=translated src=- shape=f40ade23 vocab=4c1eaa92
-/
theorem connectorClass_span_eq_top {d : ℕ} (hd : D.IsBettiDegree d) :
    Submodule.span k (Set.range (D.connectorClass (k := k) hd)) = ⊤ := by
  apply (D.connectorClass_linearIndependent (k := k) hd).span_eq_top_of_card_eq_finrank'
  rw [D.connectorCount hd, D.toricBettiContribution_eq_componentCount_sub_one hd]

def connectorClassBasis {d : ℕ} (hd : D.IsBettiDegree d) :
    Module.Basis (D.ComponentConnector hd) k (D.DegreeNewToricRelationSpace k d) :=
  Module.Basis.mk (D.connectorClass_linearIndependent (k := k) hd)
    (D.connectorClass_span_eq_top (k := k) hd).ge

/--
@isnad1 id=eq.1h4v.s12.b32ca439c3f6 from=translated src=- shape=46622520 vocab=c3b6fc78
-/
@[simp] theorem connectorClassBasis_apply {d : ℕ} (hd : D.IsBettiDegree d)
    (e : D.ComponentConnector hd) :
    D.connectorClassBasis (k := k) hd e = D.connectorClass (k := k) hd e :=
  Module.Basis.mk_apply _ _ _

/--
@isnad1 id=eq.1h2v.s4.7d96e0c73a2e from=translated src=- shape=754fec3b vocab=9d179674
-/
theorem degreeToricRelation_connector_card_exact {d : ℕ} (hd : D.IsBettiDegree d) :
    Fintype.card (D.ComponentConnector hd) = D.bettiContribution d := by
  exact D.connectorCount hd

def withinComponentStarSum (d : ℕ) (a : D.FiberRelationSpace k d) :
    D.FiberRelationSpace k d :=
  ∑ u, a.1 u • D.fiberDeltaRelation (k := k) u
    (D.componentRepresentative (D.componentOf u))

/--
@isnad1 id=eq.1h4v.s11.f9c2c0a5a3a3 from=translated src=- shape=3d7d8450 vocab=45a3b8cb
-/
theorem withinComponentStarSum_eq_of_mem_ker {d : ℕ}
    (a : D.FiberRelationSpace k d)
    (ha : a ∈ LinearMap.ker (D.fiberToComponentRelation (k := k) d)) :
    D.withinComponentStarSum (k := k) d a = a := by
  classical
  apply Subtype.ext
  funext x
  have hcomp : D.componentCoeff (k := k) d a.1 = 0 := by
    exact congrArg Subtype.val ha
  have hzero (C : D.BettiComponent d) :
      (∑ u with D.componentOf u = C, a.1 u) = 0 := by
    exact congrFun hcomp C
  simp only [withinComponentStarSum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul_of_tower, Pi.smul_apply, fiberDeltaRelation, fiberDelta,
    Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ u, a.1 u * if x = u then 1 else 0) = a.1 x := by
    simp
  rw [hfirst, sub_eq_self]
  by_cases hx : x = D.componentRepresentative (D.componentOf x)
  · have hiff (u : D.FactorizationAt d) :
        x = D.componentRepresentative (D.componentOf u) ↔
          D.componentOf u = D.componentOf x := by
      constructor
      · intro h
        rw [h, D.componentRepresentative_component]
      · intro h
        rw [hx, h]
    simp_rw [hiff]
    have hz := hzero (D.componentOf x)
    rw [Finset.sum_filter] at hz
    simpa only [mul_ite, mul_one, mul_zero] using hz
  · apply Finset.sum_eq_zero
    intro u _
    have hne : x ≠ D.componentRepresentative (D.componentOf u) := by
      intro h
      have hc : D.componentOf x = D.componentOf u := by
        rw [h, D.componentRepresentative_component]
      apply hx
      calc
        x = D.componentRepresentative (D.componentOf u) := h
        _ = D.componentRepresentative (D.componentOf x) :=
          congrArg D.componentRepresentative hc.symm
    simp [hne]

/--
@isnad1 id=mem.1h4v.s11.b1fb021b9100 from=translated src=- shape=2c49d11b vocab=0ef486f8
-/
theorem fiberPolynomial_mem_lower_of_componentKernel {d : ℕ}
    (a : D.FiberRelationSpace k d)
    (ha : a ∈ LinearMap.ker (D.fiberToComponentRelation (k := k) d)) :
    D.fiberPolynomial (k := k) d a.1 ∈ D.lowerToricIdeal (k := k) d := by
  rw [← D.withinComponentStarSum_eq_of_mem_ker a ha]
  simp only [withinComponentStarSum, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    map_sum, map_smul]
  apply Submodule.sum_mem
  intro u _
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  simpa [fiberDeltaRelation] using
    (D.fiberBinomial_mem_lower_of_sameComponent (k := k)
      (D.componentRepresentative_component (D.componentOf u)).symm)

/-- Difference vectors whose two endpoints lie in one overlap component.-/
def withinComponentDifferenceSet (d : ℕ) : Set (D.FiberRelationSpace k d) :=
  {a | ∃ (u v : D.FactorizationAt d), D.componentOf u = D.componentOf v ∧
    a = D.fiberDeltaRelation (k := k) u v}

/-- Exact kernel description: component sums forget precisely the
within-component differences.
@isnad1 id=eq.0h3v.s10.254bf626d6d9 from=translated src=- shape=d10dbf47 vocab=a5d0d7a9
-/
theorem ker_fiberToComponentRelation_eq_withinComponentSpan (d : ℕ) :
    LinearMap.ker (D.fiberToComponentRelation (k := k) d) =
      Submodule.span k (D.withinComponentDifferenceSet (k := k) d) := by
  classical
  apply le_antisymm
  · intro a ha
    rw [← D.withinComponentStarSum_eq_of_mem_ker a ha]
    apply Submodule.sum_mem
    intro u _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨u, D.componentRepresentative (D.componentOf u),
      (D.componentRepresentative_component (D.componentOf u)).symm, rfl⟩
  · rw [Submodule.span_le]
    rintro a ⟨u, v, huv, rfl⟩
    change D.fiberToComponentRelation (k := k) d
      (D.fiberDeltaRelation (k := k) u v) = 0
    rw [D.fiberToComponentRelation_fiberDelta]
    apply Subtype.ext
    simp [componentDelta, huv]

end FourGeneratedNumericalSemigroup

end

namespace FourGeneratedNumericalSemigroup

noncomputable section

variable (D : FourGeneratedNumericalSemigroup)

def degreeNewGeneratorFinset {k : Type*} [Field k] {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) :
    Finset (D.DegreeNewToricRelationSpace k d) := by
  classical
  exact G.image (D.degreeNewMk (k := k) d)

/-- A finite family spans all genuinely new degree-`d` relations.-/
def GeneratesDegreeNewRelations {k : Type*} [Field k] {d : ℕ}
    (G : Finset (D.FiberRelationSpace k d)) : Prop :=
  Submodule.span k (D.degreeNewGeneratorFinset (k := k) G :
    Set (D.DegreeNewToricRelationSpace k d)) = ⊤

/-- The frozen root-star connector relations, now regarded as genuine
degree-`d` fiber relations.-/
def connectorRelationFinset {k : Type*} [Field k] {d : ℕ}
    (hd : D.IsBettiDegree d) : Finset (D.FiberRelationSpace k d) := by
  classical
  exact Finset.univ.image (D.connectorFiberRelation (k := k) hd)

/--
@isnad1 id=generate.1h3v.s4.4056a76118d2 from=translated src=- shape=68b73707 vocab=c38f5367
-/
theorem connectorRelationFinset_generates {k : Type*} [Field k] {d : ℕ}
    (hd : D.IsBettiDegree d) :
    D.GeneratesDegreeNewRelations (D.connectorRelationFinset (k := k) hd) := by
  classical
  unfold GeneratesDegreeNewRelations
  have hle : Submodule.span k (Set.range (D.connectorClass (k := k) hd)) ≤
      Submodule.span k
        (D.degreeNewGeneratorFinset (k := k)
          (D.connectorRelationFinset (k := k) hd) :
            Set (D.DegreeNewToricRelationSpace k d)) := by
    rw [Submodule.span_le]
    rintro z ⟨e, rfl⟩
    apply Submodule.subset_span (R := k)
    show D.connectorClass (k := k) hd e ∈
      D.degreeNewGeneratorFinset (k := k) (D.connectorRelationFinset (k := k) hd)
    unfold degreeNewGeneratorFinset connectorClass
    apply Finset.mem_image.mpr
    refine ⟨D.connectorFiberRelation (k := k) hd e, ?_, rfl⟩
    unfold connectorRelationFinset
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  rw [D.connectorClass_span_eq_top (k := k) hd] at hle
  exact top_unique hle

/--
@isnad1 id=le.2h4v.s9.b03c3eb5d256 from=translated src=- shape=4155f721 vocab=5a647051
-/
theorem degreeToricRelation_generator_card_lower_bound {k : Type*} [Field k]
    {d : ℕ} (hd : D.IsBettiDegree d) (G : Finset (D.FiberRelationSpace k d))
    (hG : D.GeneratesDegreeNewRelations G) :
    D.bettiContribution d ≤ G.card := by
  unfold bettiContribution
  rw [← D.toricBettiContribution_eq_componentCount_sub_one (k := k) hd]
  classical
  unfold GeneratesDegreeNewRelations at hG
  have h := finrank_span_le_card (R := k)
    (D.degreeNewGeneratorFinset (k := k) G : Set (D.DegreeNewToricRelationSpace k d))
  rw [hG] at h
  calc
    Module.finrank k (D.DegreeNewToricRelationSpace k d) ≤
        (D.degreeNewGeneratorFinset (k := k) G).card := by simpa using h
    _ ≤ G.card := by
      unfold degreeNewGeneratorFinset
      exact Finset.card_image_le

/--
@isnad1 id=eq.1h3v.s8.54d2f93e1797 from=translated src=- shape=e0dc18d8 vocab=c2759d57
-/
theorem connectorRelationFinset_card_exact {k : Type*} [Field k] {d : ℕ}
    (hd : D.IsBettiDegree d) :
    (D.connectorRelationFinset (k := k) hd).card = D.bettiContribution d := by
  classical
  unfold connectorRelationFinset
  have hinj : Function.Injective (D.connectorFiberRelation (k := k) hd) := by
    intro e f hef
    apply (D.connectorClass_linearIndependent (k := k) hd).injective
    exact congrArg (D.degreeNewMk (k := k) d) hef
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  exact D.degreeToricRelation_connector_card_exact hd

/-- Scope-explicit stable package for the degree-local toric presentation
bridge.  It deliberately contains no global `rho` or chosen-base reduction.-/
structure ToricBettiPresentationBridge {k : Type*} [Field k] (d : ℕ)
    (hd : D.IsBettiDegree d) : Prop where
  toricKernelGenerated :
    D.toricIdeal (k := k) = Ideal.span (D.fiberBinomialSet (k := k))
  componentKernelExact :
    LinearMap.ker (D.fiberToComponentRelation (k := k) d) =
      Submodule.span k (D.withinComponentDifferenceSet (k := k) d)
  localContributionExact :
    Module.finrank k (D.DegreeNewToricRelationSpace k d) =
      D.componentCount d - 1
  connectorClassesSpan :
    Submodule.span k (Set.range (D.connectorClass (k := k) hd)) = ⊤
  connectorFamilyGenerates :
    D.GeneratesDegreeNewRelations (D.connectorRelationFinset (k := k) hd)
  universalLocalLowerBound :
    ∀ G : Finset (D.FiberRelationSpace k d),
      D.GeneratesDegreeNewRelations G → D.bettiContribution d ≤ G.card
  connectorCardExact :
    (D.connectorRelationFinset (k := k) hd).card = D.bettiContribution d

/--
@isnad1 id=toricbet.1h3v.s4.6173b591ee06 from=translated src=- shape=6adc2d68 vocab=e79a352f
-/
theorem toricBettiPresentationBridge {k : Type*} [Field k] {d : ℕ}
    (hd : D.IsBettiDegree d) : D.ToricBettiPresentationBridge (k := k) d hd where
  toricKernelGenerated := D.toricIdeal_eq_span_fiberBinomials
  componentKernelExact := D.ker_fiberToComponentRelation_eq_withinComponentSpan d
  localContributionExact := D.toricBettiContribution_eq_componentCount_sub_one hd
  connectorClassesSpan := D.connectorClass_span_eq_top hd
  connectorFamilyGenerates := D.connectorRelationFinset_generates hd
  universalLocalLowerBound := fun G hG =>
    D.degreeToricRelation_generator_card_lower_bound hd G hG
  connectorCardExact := D.connectorRelationFinset_card_exact hd

end

end FourGeneratedNumericalSemigroup

end P23.Semigroup
