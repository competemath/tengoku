import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.EulerSurplus
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.OrbitQuotientAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Incoming occurrences in orbit quotients

An equivariant map from arrow occurrences to their target vertices descends
to every subgroup-orbit quotient.  When the action on vertices is free, the
arrows ending at a chosen lift are in bijection with the arrow-orbits ending
at its quotient vertex: every orbit has a unique representative with that
target.  This is the combinatorial content of preservation of incoming arrow
multiplicity, and hence of the arrow term in the manuscript's local density.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.CoveringAction

universe u v w

variable {G : Type u} [Group G]
variable {X : Type v} {Y : Type w}
variable [MulAction G X] [MulAction G Y]

/-- An equivariant map descends to the orbit quotient by the whole acting
group.-/
def groupOrbitQuotientMap (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    MulAction.orbitRel.Quotient G X →
      MulAction.orbitRel.Quotient G Y :=
  Quotient.map' f fun a b hab ↦ by
    rw [MulAction.orbitRel_apply] at hab ⊢
    obtain ⟨g, hn⟩ := hab
    exact ⟨g, (equivariant g b).symm.trans (congrArg f hn)⟩

/--
@isnad1 id=eq.1h5v.s7.7e40c0c49152 from=translated src=- shape=93b0902b vocab=f83b5450
-/
@[simp]
theorem groupOrbitQuotientMap_mk (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (x : X) :
    groupOrbitQuotientMap f equivariant
        (Quotient.mk'' x : MulAction.orbitRel.Quotient G X) =
      (Quotient.mk'' (f x) : MulAction.orbitRel.Quotient G Y) :=
  rfl

/-- An equivariant map descends to the orbit quotients by any subgroup.-/
def orbitQuotientMap (N : Subgroup G) (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x) :
    MulAction.orbitRel.Quotient N X →
      MulAction.orbitRel.Quotient N Y :=
  Quotient.map' f fun a b hab ↦ by
    rw [MulAction.orbitRel_apply] at hab ⊢
    obtain ⟨n, hn⟩ := hab
    refine ⟨n, ?_⟩
    calc
      n • f b = f ((n : G) • b) := by
        simpa only [MulAction.subgroup_smul_def] using
          (equivariant (n : G) b).symm
      _ = f a := congrArg f hn

/--
@isnad1 id=eq.1h6v.s7.791c18692976 from=translated src=- shape=fefd8693 vocab=fc628527
-/
@[simp]
theorem orbitQuotientMap_mk (N : Subgroup G) (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (x : X) :
    orbitQuotientMap N f equivariant
        (Quotient.mk'' x : MulAction.orbitRel.Quotient N X) =
      (Quotient.mk'' (f x) : MulAction.orbitRel.Quotient N Y) :=
  rfl

/-- For a free action on the target, every whole-group orbit in a fibre of
the descended map has a unique representative in the corresponding original
fibre.-/
noncomputable def groupOrbitQuotientMapFiberEquiv
    [IsCancelSMul G Y]
    (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (y : Y) :
    {x : X // f x = y} ≃
      {q : MulAction.orbitRel.Quotient G X //
        groupOrbitQuotientMap f equivariant q =
          (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)} := by
  let toOrbit : {x : X // f x = y} →
      {q : MulAction.orbitRel.Quotient G X //
        groupOrbitQuotientMap f equivariant q =
          (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)} :=
    fun x ↦ ⟨Quotient.mk'' x.1, by simp [x.2]⟩
  apply Equiv.ofBijective toOrbit
  constructor
  · intro a b hab
    apply Subtype.ext
    have horbit : a.1 ∈ MulAction.orbit G b.1 :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
    have hfix : g • y = y := by
      calc
        g • y = g • f b.1 := by rw [b.property]
        _ = f (g • b.1) := (equivariant g b.1).symm
        _ = f a.1 := by rw [hg]
        _ = y := a.property
    have hgOne : g = 1 :=
      IsCancelSMul.right_cancel g 1 y (by simpa using hfix)
    calc
      a.1 = g • b.1 := hg.symm
      _ = b.1 := by rw [hgOne, one_smul]
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn' with
    | _ x =>
        have horbit : f x ∈ MulAction.orbit G y := by
          have hrel := Quotient.exact
            (show (Quotient.mk'' (f x) :
                MulAction.orbitRel.Quotient G Y) = Quotient.mk'' y by
              simpa only [groupOrbitQuotientMap_mk] using hq)
          change MulAction.orbitRel G Y (f x) y at hrel
          rwa [MulAction.orbitRel_apply] at hrel
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp horbit
        let x' : X := g⁻¹ • x
        have hx' : f x' = y := by
          dsimp only [x']
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := equivariant g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hg.symm]
            _ = y := by simp only [smul_smul, inv_mul_cancel, one_smul]
        refine ⟨⟨x', hx'⟩, ?_⟩
        apply Subtype.ext
        change (Quotient.mk'' x' : MulAction.orbitRel.Quotient G X) =
          Quotient.mk'' x
        apply Quotient.sound
        exact MulAction.mem_orbit x g⁻¹

/-- For a free action on the target, every orbit in a fibre of the descended
map has a unique representative in the corresponding original fibre.-/
noncomputable def orbitQuotientMapFiberEquiv
    [IsCancelSMul G Y]
    (N : Subgroup G) (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (y : Y) :
    {x : X // f x = y} ≃
      {q : MulAction.orbitRel.Quotient N X //
        orbitQuotientMap N f equivariant q =
          (Quotient.mk'' y : MulAction.orbitRel.Quotient N Y)} := by
  let toOrbit : {x : X // f x = y} →
      {q : MulAction.orbitRel.Quotient N X //
        orbitQuotientMap N f equivariant q =
          (Quotient.mk'' y : MulAction.orbitRel.Quotient N Y)} :=
    fun x ↦ ⟨Quotient.mk'' x.1, by simp [x.2]⟩
  apply Equiv.ofBijective toOrbit
  constructor
  · intro a b hab
    apply Subtype.ext
    have horbit : a.1 ∈ MulAction.orbit N b.1 :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp horbit
    have hfix : (n : G) • y = y := by
      calc
        (n : G) • y = (n : G) • f b.1 := by rw [b.property]
        _ = f ((n : G) • b.1) :=
          (equivariant (n : G) b.1).symm
        _ = f a.1 := by
          rw [show (n : G) • b.1 = a.1 by
            simpa only [MulAction.subgroup_smul_def] using hn]
        _ = y := a.property
    have hnOne : (n : G) = 1 :=
      IsCancelSMul.right_cancel (n : G) 1 y (by simpa using hfix)
    calc
      a.1 = (n : G) • b.1 := by
        simpa only [MulAction.subgroup_smul_def] using hn.symm
      _ = b.1 := by rw [hnOne, one_smul]
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn' with
    | _ x =>
        have horbit : f x ∈ MulAction.orbit N y := by
          have hrel := Quotient.exact
            (show (Quotient.mk'' (f x) :
                MulAction.orbitRel.Quotient N Y) = Quotient.mk'' y by
              simpa only [orbitQuotientMap_mk] using hq)
          change MulAction.orbitRel N Y (f x) y at hrel
          rwa [MulAction.orbitRel_apply] at hrel
        obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp horbit
        let x' : X := (n⁻¹ : N) • x
        have hx' : f x' = y := by
          dsimp only [x']
          calc
            f ((n⁻¹ : N) • x) = (n⁻¹ : G) • f x := by
              simpa only [MulAction.subgroup_smul_def,
                Subgroup.coe_inv] using
                equivariant ((n : G)⁻¹) x
            _ = (n⁻¹ : G) • ((n : G) • y) := by
              rw [show f x = (n : G) • y by
                simpa only [MulAction.subgroup_smul_def] using hn.symm]
            _ = y := by simp only [smul_smul, inv_mul_cancel, one_smul]
        refine ⟨⟨x', hx'⟩, ?_⟩
        apply Subtype.ext
        change (Quotient.mk'' x' : MulAction.orbitRel.Quotient N X) =
          Quotient.mk'' x
        apply Quotient.sound
        exact MulAction.mem_orbit x (n⁻¹ : N)

/-- Cardinal form of the whole-group fibre equivalence.
@isnad1 id=eq.1h5v.s7.d0db78545072 from=translated src=- shape=b75fcb10 vocab=36924dd4
-/
theorem card_groupOrbitQuotientMap_fiber_eq
    [IsCancelSMul G Y] [Finite X]
    (f : X → Y)
    (equivariant : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (y : Y) :
    Nat.card
        {q : MulAction.orbitRel.Quotient G X //
          groupOrbitQuotientMap f equivariant q =
            (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y)} =
      Nat.card {x : X // f x = y} :=
  Nat.card_congr (groupOrbitQuotientMapFiberEquiv f equivariant y).symm

/-- Incoming arrow occurrences at a vertex, counted with multiplicity.-/
noncomputable def occurrenceIndegree
    {Arrow Vertex : Type*} [Finite Arrow]
    (target : Arrow → Vertex) (v : Vertex) : ℤ :=
  Nat.card {a : Arrow // target a = v}

/-- The local density written directly in terms of incoming arrow
occurrences.-/
noncomputable def occurrenceLocalDensity
    {Arrow Vertex : Type*} [Finite Arrow]
    (target : Arrow → Vertex) (IsProjective : Vertex → Prop)
    (v : Vertex) : ℤ := by
  classical
  exact 2 * (if IsProjective v then 0 else 1) -
    occurrenceIndegree target v

/-- The arrow-multiplicity matrix obtained by counting a type of arrow
occurrences with specified source and target.-/
noncomputable def arrowMultiplicityOfOccurrences
    {Arrow Vertex : Type*} [Finite Arrow]
    (source target : Arrow → Vertex) (x y : Vertex) : ℕ :=
  Nat.card {a : Arrow // source a = x ∧ target a = y}

/-- Partition the arrows ending at `y` according to their source.-/
noncomputable def targetFiberEquivSigmaSourceFibers
    {Arrow Vertex : Type*}
    (source target : Arrow → Vertex) (y : Vertex) :
    {a : Arrow // target a = y} ≃
      Σ x : Vertex, {a : Arrow // source a = x ∧ target a = y} where
  toFun a := ⟨source a.1, ⟨a.1, rfl, a.property⟩⟩
  invFun a := ⟨a.2.1, a.2.2.2⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨x, ⟨a, hsource, htarget⟩⟩
    subst x
    rfl

/-- Summing the occurrence multiplicities over all sources gives the literal
cardinality of the incoming-arrow fibre.
@isnad1 id=eq.0h5v.s5.94a3a93435ae from=translated src=- shape=3e69a9e1 vocab=db94f615
-/
theorem indegree_arrowMultiplicityOfOccurrences_eq
    {Arrow Vertex : Type*} [Finite Arrow] [Fintype Vertex]
    (source target : Arrow → Vertex) (y : Vertex) :
    ARCount.indegree (arrowMultiplicityOfOccurrences source target) y =
      occurrenceIndegree target y := by
  change
    (∑ x : Vertex,
      (Nat.card {a : Arrow // source a = x ∧ target a = y} : ℤ)) =
        (Nat.card {a : Arrow // target a = y} : ℤ)
  rw [← Nat.cast_sum]
  norm_cast
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    (targetFiberEquivSigmaSourceFibers source target y).symm

/-- The occurrence form of local density is exactly the manuscript's
arrow-multiplicity-matrix form.
@isnad1 id=eq.0h6v.s5.c5e6d4327deb from=translated src=- shape=bb503cb0 vocab=38b1e82a
-/
theorem localDensity_arrowMultiplicityOfOccurrences_eq
    {Arrow Vertex : Type*} [Finite Arrow] [Fintype Vertex]
    (source target : Arrow → Vertex)
    (IsProjective : Vertex → Prop) [DecidablePred IsProjective]
    (y : Vertex) :
    ARCount.localDensity
        (arrowMultiplicityOfOccurrences source target) IsProjective y =
      occurrenceLocalDensity target IsProjective y := by
  rw [ARCount.localDensity, occurrenceLocalDensity,
    indegree_arrowMultiplicityOfOccurrences_eq]
  by_cases h : IsProjective y <;> simp [h]

/-- An orbit has a property when one of its representatives has it.-/
def OrbitQuotientProperty
    (N : Subgroup G) (P : Y → Prop)
    (q : MulAction.orbitRel.Quotient N Y) : Prop :=
  ∃ y ∈ q.orbit, P y

/-- A whole-group orbit has a property when one of its representatives has
it.-/
def GroupOrbitQuotientProperty
    (P : Y → Prop)
    (q : MulAction.orbitRel.Quotient G Y) : Prop :=
  ∃ y ∈ q.orbit, P y

/-- An invariant property holds on the whole-group orbit of a point exactly
when it holds at that point.
@isnad1 id=iff.1h4v.s6.d2048ff766a0 from=translated src=- shape=379cf1ab vocab=889e54f6
-/
theorem groupOrbitQuotientProperty_mk_iff
    (P : Y → Prop)
    (invariant : ∀ (g : G) (y : Y), P (g • y) ↔ P y)
    (y : Y) :
    GroupOrbitQuotientProperty P
        (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y) ↔
      P y := by
  rw [GroupOrbitQuotientProperty,
    MulAction.orbitRel.Quotient.orbit_mk]
  constructor
  · rintro ⟨y', hy', hPy'⟩
    rw [MulAction.mem_orbit_iff] at hy'
    obtain ⟨g, rfl⟩ := hy'
    exact (invariant g y).mp hPy'
  · intro hPy
    exact ⟨y, MulAction.mem_orbit_self y, hPy⟩

/-- Incoming occurrence multiplicity is unchanged at a chosen lift after
passing to the whole-group orbit quotient.
@isnad1 id=eq.1h5v.s7.691423c47c84 from=translated src=- shape=6dddf23a vocab=1d97376e
-/
theorem occurrenceIndegree_groupOrbitQuotientMap_mk
    [IsCancelSMul G Y] [Finite X]
    (target : X → Y)
    (target_equivariant :
      ∀ (g : G) (a : X), target (g • a) = g • target a)
    (y : Y) :
    occurrenceIndegree (groupOrbitQuotientMap target target_equivariant)
        (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y) =
      occurrenceIndegree target y := by
  rw [occurrenceIndegree, occurrenceIndegree]
  exact congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_groupOrbitQuotientMap_fiber_eq target target_equivariant y)

/-- If projectivity is invariant on vertex orbits, then the full local
density is unchanged at a chosen lift after the whole-group quotient.
@isnad1 id=eq.2h6v.s7.596711d2045e from=translated src=- shape=0fb3608a vocab=0fb58c66
-/
theorem occurrenceLocalDensity_groupOrbitQuotientMap_mk
    [IsCancelSMul G Y] [Finite X]
    (target : X → Y)
    (target_equivariant :
      ∀ (g : G) (a : X), target (g • a) = g • target a)
    (IsProjective : Y → Prop)
    (projective_invariant :
      ∀ (g : G) (y : Y), IsProjective (g • y) ↔ IsProjective y)
    (y : Y) :
    occurrenceLocalDensity
        (groupOrbitQuotientMap target target_equivariant)
        (GroupOrbitQuotientProperty IsProjective)
        (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y) =
      occurrenceLocalDensity target IsProjective y := by
  classical
  rw [occurrenceLocalDensity, occurrenceLocalDensity,
    groupOrbitQuotientProperty_mk_iff IsProjective projective_invariant,
    occurrenceIndegree_groupOrbitQuotientMap_mk]

/-- Occurrence local density is invariant under the group action whenever
the target action is free and projectivity is invariant.
@isnad1 id=eq.2h7v.s7.c57c3542c7e4 from=translated src=- shape=6ecf935b vocab=87e24b8e
-/
theorem occurrenceLocalDensity_invariant
    [IsCancelSMul G Y] [Finite X]
    (target : X → Y)
    (target_equivariant :
      ∀ (g : G) (a : X), target (g • a) = g • target a)
    (IsProjective : Y → Prop)
    (projective_invariant :
      ∀ (g : G) (y : Y), IsProjective (g • y) ↔ IsProjective y)
    (g : G) (y : Y) :
    occurrenceLocalDensity target IsProjective (g • y) =
      occurrenceLocalDensity target IsProjective y := by
  classical
  let quotientDensity := occurrenceLocalDensity
    (groupOrbitQuotientMap target target_equivariant)
    (GroupOrbitQuotientProperty IsProjective)
  calc
    occurrenceLocalDensity target IsProjective (g • y) =
        quotientDensity
          (Quotient.mk'' (g • y) : MulAction.orbitRel.Quotient G Y) :=
      (occurrenceLocalDensity_groupOrbitQuotientMap_mk target
        target_equivariant IsProjective projective_invariant (g • y)).symm
    _ = quotientDensity
          (Quotient.mk'' y : MulAction.orbitRel.Quotient G Y) := by
      apply congrArg quotientDensity
      apply Quotient.sound
      exact MulAction.mem_orbit y g
    _ = occurrenceLocalDensity target IsProjective y :=
      occurrenceLocalDensity_groupOrbitQuotientMap_mk target
        target_equivariant IsProjective projective_invariant y

/-- Descending the invariant upstairs local density gives exactly the local
density formed from the quotient occurrence and projectivity data.
@isnad1 id=eq.2h6v.s7.5a3086d7f0ea from=translated src=- shape=92979aad vocab=bfe91f61
-/
theorem orbitInvariantDescend_occurrenceLocalDensity
    [IsCancelSMul G Y] [Finite X]
    (target : X → Y)
    (target_equivariant :
      ∀ (g : G) (a : X), target (g • a) = g • target a)
    (IsProjective : Y → Prop)
    (projective_invariant :
      ∀ (g : G) (y : Y), IsProjective (g • y) ↔ IsProjective y)
    (q : MulAction.orbitRel.Quotient G Y) :
    orbitInvariantDescend
        (occurrenceLocalDensity target IsProjective)
        (occurrenceLocalDensity_invariant target target_equivariant
          IsProjective projective_invariant) q =
      occurrenceLocalDensity
        (groupOrbitQuotientMap target target_equivariant)
        (GroupOrbitQuotientProperty IsProjective) q := by
  classical
  induction q using Quotient.inductionOn' with
  | _ y =>
      exact (occurrenceLocalDensity_groupOrbitQuotientMap_mk target
        target_equivariant IsProjective projective_invariant y).symm

/-- Endpoint scaling in local-density form: the total upstairs occurrence
local density is the covering degree times the total quotient density.  No
separate free action on a chosen set of arrow bases is required.
@isnad1 id=eq.2h5v.s8.c132c7e0a3e2 from=translated src=- shape=14e65358 vocab=1293a879
-/
theorem sum_occurrenceLocalDensity_eq_group_card_mul_quotient
    [Fintype G] [Fintype X] [Fintype Y]
    [Fintype (MulAction.orbitRel.Quotient G Y)]
    [IsCancelSMul G Y]
    (target : X → Y)
    (target_equivariant :
      ∀ (g : G) (a : X), target (g • a) = g • target a)
    (IsProjective : Y → Prop)
    (projective_invariant :
      ∀ (g : G) (y : Y), IsProjective (g • y) ↔ IsProjective y) :
    (∑ y, occurrenceLocalDensity target IsProjective y) =
      (Fintype.card G : ℤ) *
        ∑ q : MulAction.orbitRel.Quotient G Y,
          occurrenceLocalDensity
            (groupOrbitQuotientMap target target_equivariant)
            (GroupOrbitQuotientProperty IsProjective) q := by
  classical
  rw [sum_eq_card_mul_sum_orbitInvariantDescend
    (occurrenceLocalDensity target IsProjective)
    (occurrenceLocalDensity_invariant target target_equivariant
      IsProjective projective_invariant)]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact orbitInvariantDescend_occurrenceLocalDensity target
    target_equivariant IsProjective projective_invariant q

end MagnitudeConjecture.CoveringAction
