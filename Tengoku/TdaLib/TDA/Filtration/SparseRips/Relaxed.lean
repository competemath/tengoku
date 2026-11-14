import Tengoku.TdaLib.TDA.Filtration.Rips
import Tengoku.TdaLib.TDA.Filtration.SparseRips.Deletion
import Tengoku.TdaLib.TDA.Simplicial.Contiguity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relaxed complexes and the sparse inclusion filtration

Relaxed dissimilarity adds both vertex weights to the original distance, including
self-pairs. Closed active complexes retain vertices at their deletion times.
Taking their union over all earlier nonnegative scales gives an ordinary inclusion
filtration on the fixed ambient vertex type.
-/

namespace TDA.Filtration.SparseRips

open TDA.Simplicial

noncomputable section

variable {V : Type*} [MetricSpace V]

local instance relaxedDecidableEq : DecidableEq V := Classical.decEq V

/-- A dissimilarity, rather than a purported metric: self-distances are twice the weight.-/
def relaxedDistance (η : ℝ) (time : V → Option ℝ) (r : ℝ) (x y : V) : ℝ :=
  dist x y + weight η (time x) r + weight η (time y) r

/--
@isnad1 id=eq.0h5v.s5.eec69f672c3e from=translated src=- shape=e38db088 vocab=a8954ee0
-/
@[simp] theorem relaxedDistance_self (η : ℝ) (time : V → Option ℝ) (r : ℝ) (x : V) :
    relaxedDistance η time r x x = 2 * weight η (time x) r := by
  simp [relaxedDistance]; ring

/-- Closed relaxed threshold complexes, extended by bottom at negative scales.-/
def relaxedComplex (η : ℝ) (time : V → Option ℝ) (r : ℝ) :
    PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ 0 ≤ r ∧
    ∀ x ∈ s, ∀ y ∈ s, relaxedDistance η time r x y ≤ r}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => ⟨ht, hs.2.1,
      fun x hx y hy => hs.2.2 x (hts hx) y (hts hy)⟩⟩

/--
@isnad1 id=iff.0h5v.s6.659d767bc8da from=translated src=- shape=ed128b87 vocab=6cb9df74
-/
@[simp] theorem mem_relaxedComplex (η : ℝ) (time : V → Option ℝ) (r : ℝ) (s : Finset V) :
    s ∈ relaxedComplex η time r ↔ s.Nonempty ∧ 0 ≤ r ∧
      ∀ x ∈ s, ∀ y ∈ s, relaxedDistance η time r x y ≤ r := Iff.rfl

/-- The half-slope bound makes relaxed threshold complexes nested.
@isnad1 id=monotone.3h3v.s6.866b17754b35 from=translated src=- shape=821f5a96 vocab=2afbaf0a
-/
theorem relaxedComplex_mono {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (time : V → Option ℝ) (ht : ∀ x t, t ∈ time x → 0 ≤ t) :
    Monotone (relaxedComplex η time) := by
  intro r s hrs σ hσ
  refine ⟨hσ.1, hσ.2.1.trans hrs, ?_⟩
  intro x hx y hy
  have hxy := hσ.2.2 x hx y hy
  have hxw := (weight_increment hη hη' (time x) (ht x) hσ.2.1 hrs).2
  have hyw := (weight_increment hη hη' (time y) (ht y) hσ.2.1 hrs).2
  dsimp [relaxedDistance] at hxy ⊢
  linarith

/-- Relaxed complexes are bounded between two diameter-scale Rips complexes.
@isnad1 id=le.3h4v.s6.e080d1533f93 from=translated src=- shape=f568696a vocab=f980e68b
-/
theorem rips_le_relaxedComplex {η r : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hr : 0 ≤ r) (time : V → Option ℝ) :
    (Rips.filter inferInstance).sublevel ((1 - 2 * η) * r) ≤ relaxedComplex η time r := by
  intro σ hσ
  obtain ⟨hne, hdist⟩ := (Rips.mem_sublevel_iff _ _ _).mp hσ
  refine ⟨hne, hr, ?_⟩
  intro x hx y hy
  have hwx := weight_le hη hη' hr (time x)
  have hwy := weight_le hη hη' hr (time y)
  have hxy := hdist x hx y hy
  dsimp [relaxedDistance]
  nlinarith

/--
@isnad1 id=le.1h4v.s5.4848bfd684c4 from=translated src=- shape=ac6de322 vocab=a93fc4d8
-/
theorem relaxedComplex_le_rips {η r : ℝ} (hη : 0 ≤ η) (time : V → Option ℝ) :
    relaxedComplex η time r ≤ (Rips.filter inferInstance).sublevel r := by
  intro σ hσ
  apply (Rips.mem_sublevel_iff _ _ _).mpr
  refine ⟨hσ.1, ?_⟩
  intro x hx y hy
  have hwx := weight_nonneg hη hσ.2.1 (time x)
  have hwy := weight_nonneg hη hσ.2.1 (time y)
  have hxy := hσ.2.2 x hx y hy
  dsimp [relaxedDistance] at hxy
  linarith

variable [Fintype V]

/-- Restrict the relaxed complex to vertices whose deletion time has not passed.-/
def closedActiveComplex (seed : V) (η r : ℝ) : PreAbstractSimplicialComplex V where
  faces := {s | s ∈ relaxedComplex η (deletionTime seed η) r ∧
    ∀ x ∈ s, ClosedActive (deletionTime seed η x) r}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1.1, fun t hts ht =>
      ⟨⟨ht, hs.1.2.1, fun x hx y hy => hs.1.2.2 x (hts hx) y (hts hy)⟩,
        fun x hx => hs.2 x (hts hx)⟩⟩

/--
@isnad1 id=iff.0h5v.s6.b3bf199fec99 from=translated src=- shape=56a52b0e vocab=385ee0e0
-/
@[simp] theorem mem_closedActiveComplex (seed : V) (η r : ℝ) (s : Finset V) :
    s ∈ closedActiveComplex seed η r ↔
      s ∈ relaxedComplex η (deletionTime seed η) r ∧
        ∀ x ∈ s, ClosedActive (deletionTime seed η x) r := Iff.rfl

/-- The union of all closed active complexes up to the current scale.-/
def sparseComplex (seed : V) (η r : ℝ) : PreAbstractSimplicialComplex V where
  faces := {s | ∃ a, 0 ≤ a ∧ a ≤ r ∧ s ∈ closedActiveComplex seed η a}
  isRelLowerSet_faces := by
    rintro s ⟨a, ha, har, hs⟩
    exact ⟨hs.1.1, fun t hts ht =>
      ⟨a, ha, har, (closedActiveComplex seed η a).isRelLowerSet_faces hs |>.2 hts ht⟩⟩

/--
@isnad1 id=iff.0h5v.s6.6132e5b88991 from=translated src=- shape=4aac79bd vocab=1bfe468d
-/
@[simp] theorem mem_sparseComplex (seed : V) (η r : ℝ) (s : Finset V) :
    s ∈ sparseComplex seed η r ↔ ∃ a, 0 ≤ a ∧ a ≤ r ∧ s ∈ closedActiveComplex seed η a :=
  Iff.rfl

/--
@isnad1 id=monotone.0h3v.s4.f32bfc07b016 from=translated src=- shape=48380b5f vocab=1f35e429
-/
theorem sparseComplex_mono (seed : V) (η : ℝ) : Monotone (sparseComplex seed η) := by
  intro r s hrs σ
  rintro ⟨a, ha, har, hσ⟩
  exact ⟨a, ha, har.trans hrs, hσ⟩

/-- The sparse filtration uses actual face inclusions at all scales.-/
def sparseFiltration (seed : V) (η : ℝ) : SimplicialFiltration ℝ V where
  toFun := sparseComplex seed η
  monotone' := sparseComplex_mono seed η

/--
@isnad1 id=eq.1h4v.s5.84e31c70aa5d from=translated src=- shape=cb03cdfe vocab=cf42ee67
-/
theorem sparseComplex_eq_bot_of_neg (seed : V) (η : ℝ) {r : ℝ} (hr : r < 0) :
    sparseComplex seed η r = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  obtain ⟨a, ha, har, _⟩ := hs
  exact (not_le_of_gt hr (ha.trans har)).elim

/--
@isnad1 id=le.1h4v.s5.dc1f8ef19549 from=translated src=- shape=1ef6279c vocab=7c418244
-/
theorem closedActiveComplex_le_sparseComplex (seed : V) (η : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    closedActiveComplex seed η r ≤ sparseComplex seed η r := by
  intro s hs
  exact ⟨r, hr, le_rfl, hs⟩

/-- The initial vertex survives at every nonnegative scale, including a singleton input.
@isnad1 id=mem.1h4v.s6.93ff27200bc0 from=translated src=- shape=9a9a7022 vocab=65776f5a
-/
theorem singleton_seed_mem_sparse (seed : V) (η : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ({seed} : Finset V) ∈ sparseFiltration seed η r := by
  apply closedActiveComplex_le_sparseComplex seed η hr
  refine ⟨⟨by simp, hr, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst x; subst y
    simpa [relaxedDistance] using hr
  · intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp

/-- A seed-free extension chooses an initial vertex when one exists and uses bottom on empty input.-/
def finiteSparseFiltration (η : ℝ) : SimplicialFiltration ℝ V := by
  classical
  exact if h : Nonempty V then sparseFiltration (Classical.choice h) η else ⊥

/--
@isnad1 id=eq.0h2v.s5.8882fbdfb332 from=translated src=- shape=45520f39 vocab=c3b091d8
-/
@[simp] theorem finiteSparseFiltration_of_isEmpty [IsEmpty V] (η : ℝ) :
    finiteSparseFiltration (V := V) η = ⊥ := by
  simp [finiteSparseFiltration]

/--
@isnad1 id=le.2h4v.s6.43c145bc399f from=translated src=- shape=ac234d50 vocab=e0eb1058
-/
theorem sparseComplex_le_relaxedComplex (seed : V) {η : ℝ}
    (hη : 0 < η) (hη' : η ≤ 1 / 3) (r : ℝ) :
    sparseComplex seed η r ≤ relaxedComplex η (deletionTime seed η) r := by
  intro σ hσ
  obtain ⟨a, _, har, hσa⟩ := hσ
  exact relaxedComplex_mono hη.le (by linarith) (deletionTime seed η)
    (deletionTime_nonneg seed hη hη') har hσa.1

end

end TDA.Filtration.SparseRips
