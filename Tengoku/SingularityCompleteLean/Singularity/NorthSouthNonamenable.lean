import Tengoku.SingularityCompleteLean.Singularity.NorthSouthConjugate
import Tengoku.SingularityCompleteLean.Singularity.FiniteOrbitDisplacement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# North--south dynamics and infinite endpoint orbits imply nonamenability

Finite-set displacement supplies a conjugate with disjoint endpoints. Its
positive powers generate an actual free subgroup, which obstructs invariant means.
-/

noncomputable section
open Set MulAction
open scoped Classical Topology Pointwise

namespace Singularity

/-- Displacement of a two-point set makes the four original and translated points distinct.
@isnad1 id=injectiv.2h5v.s7.b0bdd9fb6d3d from=translated src=- shape=b423654b vocab=ca3be393
-/
theorem twoPoint_translate_injective {G X : Type*} [Group G] [MulAction G X]
    {p q : X} (hpq : p ≠ q) (b : G)
    (hdisj : Disjoint ((fun x => b • x) '' {p, q}) {p, q}) :
    Function.Injective (fun z : Bool × Bool =>
      if z.1 then b • (if z.2 then p else q) else (if z.2 then p else q)) := by
  let e : Bool → X := fun i => if i then p else q
  have he (i : Bool) : e i ∈ ({p, q} : Set X) := by cases i <;> simp [e]
  have hei : Function.Injective e := by
    intro i j hij
    cases i <;> cases j <;> simp_all [e]
  rintro ⟨i, k⟩ ⟨j, l⟩ h
  cases i <;> cases j
  · change e k = e l at h
    exact Prod.ext rfl (hei h)
  · change e k = b • e l at h
    exact False.elim (Set.disjoint_left.mp hdisj ⟨e l, he l, h.symm⟩ (he k))
  · change b • e k = e l at h
    exact False.elim (Set.disjoint_left.mp hdisj ⟨e k, he k, h⟩ (he l))
  · change b • e k = b • e l at h
    exact Prod.ext rfl (hei (MulAction.injective b h))

/-- One north--south element with infinite endpoint orbits yields a free subgroup.
@isnad1 id=ex.4h5v.s7.b02c12b1f13f from=translated src=- shape=cde05286 vocab=98688d46
-/
theorem exists_free_subgroup_of_northSouth {G : Type} {X : Type*} [Group G]
    [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    {g : G} {p q : X} (hpq : p ≠ q) (hdyn : UniformNorthSouth g p q)
    (hp : (MulAction.orbit G p).Infinite) (hq : (MulAction.orbit G q).Infinite) :
    ∃ j : FreeGroup Bool →* G, Function.Injective j := by
  obtain ⟨b, hb⟩ := exists_translate_disjoint_of_infinite_orbits
    ({p, q} : Set X) {p, q} (by simp) (by simp) (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hp
      · have hxq : x = q := Set.mem_singleton_iff.mp hx
        subst x
        exact hq)
  obtain ⟨n, _, hn⟩ := northSouth_conjugate_free_powers hdyn b
    (twoPoint_translate_injective hpq b hb)
  exact ⟨_, hn⟩

/-- Infinite endpoint orbits and north--south dynamics imply nonamenability.
@isnad1 id=not.4h5v.s6.0ec2a92660e4 from=translated src=- shape=939bb34f vocab=9948b3e0
-/
theorem no_invariantMean_of_northSouth_infinite_orbits {G : Type} {X : Type*} [Group G]
    [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousConstSMul G X]
    {g : G} {p q : X} (hpq : p ≠ q) (hdyn : UniformNorthSouth g p q)
    (hp : (MulAction.orbit G p).Infinite) (hq : (MulAction.orbit G q).Infinite) :
    ¬HasInvariantMean G := by
  obtain ⟨j, hj⟩ := exists_free_subgroup_of_northSouth hpq hdyn hp hq
  exact no_invariantMean_of_free_subgroup j hj

end Singularity
