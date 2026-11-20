import Tengoku.Seed.Combinatorics.SimpleGraph.Metric
import Tengoku.Seed.Data.Fin.Embedding
import Tengoku.Seed.Data.Fin.Rev
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Seed.Data.Nat.Find

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graph burning via ranked covers

This file records the ranked-cover formulation of graph burning. A source indexed by
`r : Fin t` covers the integer closed ball of radius `r`. Chronological source lists are
obtained from ranked lists, and conversely, by the involution `Fin.rev`.
-/

namespace SimpleGraph

universe u v

variable {V : Type u} {ι : Type v}

/-- The integer closed ball of radius `r` in the graph extended metric.-/
def closedBall (G : SimpleGraph V) (c : V) (r : ℕ) : Set V :=
  {v | G.edist v c ≤ (r : ℕ∞)}

/--
@isnad1 id=iff.0h5v.s5.2ab6f4319291 from=translated src=- shape=0334cc1c vocab=381ed24f
-/
@[simp]
theorem mem_closedBall {G : SimpleGraph V} {c v : V} {r : ℕ} :
    v ∈ G.closedBall c r ↔ G.edist v c ≤ (r : ℕ∞) :=
  Iff.rfl

/--
@isnad1 id=mem.0h4v.s4.caecd7e4076b from=translated src=- shape=3971d209 vocab=b560b615
-/
@[simp, nolint simpNF]
theorem mem_closedBall_self (G : SimpleGraph V) (c : V) (r : ℕ) :
    c ∈ G.closedBall c r := by
  simp [closedBall]

/-- A ranked cover of length `t` has one center for each radius `0, ..., t - 1`.-/
def IsRankedCover (G : SimpleGraph V) {t : ℕ} (centers : Fin t → V) : Prop :=
  ∀ v, ∃ r : Fin t, v ∈ G.closedBall (centers r) r.1

/--
A ranked subcover of length `t` uses pairwise distinct radii selected by the embedding
`radii : ι ↪ Fin t`.-/
def IsRankedSubcover (G : SimpleGraph V) {t : ℕ} (radii : ι ↪ Fin t)
    (centers : ι → V) : Prop :=
  ∀ v, ∃ i : ι, v ∈ G.closedBall (centers i) (radii i).1

/--
A ranked subcover can be filled at every omitted radius without changing any of its
chosen centers.
@isnad1 id=ex.1h6v.s6.f9653997c05f from=translated src=- shape=928619b6 vocab=c915dac4
-/
theorem IsRankedSubcover.extend [Nonempty V] {G : SimpleGraph V} {t : ℕ}
    {radii : ι ↪ Fin t} {centers : ι → V} (h : G.IsRankedSubcover radii centers) :
    ∃ fullCenters : Fin t → V,
      G.IsRankedCover fullCenters ∧ ∀ i, fullCenters (radii i) = centers i := by
  classical
  let fullCenters : Fin t → V :=
    Function.extend radii centers (fun _ ↦ Classical.choice (inferInstance : Nonempty V))
  have hfull : ∀ i, fullCenters (radii i) = centers i := by
    intro i
    exact radii.injective.extend_apply centers
      (fun _ ↦ Classical.choice (inferInstance : Nonempty V)) i
  refine ⟨fullCenters, ?_, hfull⟩
  intro v
  obtain ⟨i, hi⟩ := h v
  refine ⟨radii i, ?_⟩
  rw [hfull i]
  exact hi

/-- Increasing the available length preserves the existence of a ranked cover.
@isnad1 id=ex.2h5v.s5.d53d042c64c2 from=translated src=- shape=56cd5581 vocab=3a56c8a4
-/
theorem IsRankedCover.extendLength [Nonempty V] {G : SimpleGraph V} {s t : ℕ}
    {centers : Fin s → V} (h : G.IsRankedCover centers) (hst : s ≤ t) :
    ∃ fullCenters : Fin t → V, G.IsRankedCover fullCenters := by
  have hsub : G.IsRankedSubcover (Fin.castLEEmb hst) centers := by
    intro v
    obtain ⟨r, hr⟩ := h v
    exact ⟨r, hr⟩
  obtain ⟨fullCenters, hcover, _⟩ := hsub.extend
  exact ⟨fullCenters, hcover⟩

/-! ## Chronological and ranked indexing -/

/-- Reindex a chronological source list by its final radii.-/
def chronologicalToRanked {t : ℕ} (sources : Fin t → V) : Fin t → V :=
  fun r ↦ sources r.rev

/-- Reindex a ranked source list by ignition time.-/
def rankedToChronological {t : ℕ} (centers : Fin t → V) : Fin t → V :=
  fun i ↦ centers i.rev

/--
@isnad1 id=eq.0h4v.s4.4ff88e07adae from=translated src=- shape=8845664e vocab=2238a9ce
-/
@[simp]
theorem chronologicalToRanked_apply {t : ℕ} (sources : Fin t → V) (r : Fin t) :
    chronologicalToRanked sources r = sources r.rev :=
  rfl

/--
@isnad1 id=eq.0h4v.s4.adb44f3e0c36 from=translated src=- shape=8845664e vocab=a4e6f117
-/
@[simp]
theorem rankedToChronological_apply {t : ℕ} (centers : Fin t → V) (i : Fin t) :
    rankedToChronological centers i = centers i.rev :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.564cdbb17967 from=translated src=- shape=85d531ed vocab=141d295a
-/
@[simp]
theorem chronologicalToRanked_rankedToChronological {t : ℕ} (centers : Fin t → V) :
    chronologicalToRanked (rankedToChronological centers) = centers := by
  funext r
  simp

/--
@isnad1 id=eq.0h3v.s4.9e25ae862ec5 from=translated src=- shape=85d531ed vocab=141d295a
-/
@[simp]
theorem rankedToChronological_chronologicalToRanked {t : ℕ} (sources : Fin t → V) :
    rankedToChronological (chronologicalToRanked sources) = sources := by
  funext i
  simp

/-- The final radius of the source ignited at chronological index `i`.-/
def chronologicalRadius {t : ℕ} (i : Fin t) : ℕ :=
  i.rev.1

/--
@isnad1 id=eq.0h2v.s5.ada50fd6b365 from=translated src=- shape=16b5a628 vocab=871013ad
-/
theorem chronologicalRadius_eq {t : ℕ} (i : Fin t) :
    chronologicalRadius i = t - (i.1 + 1) :=
  Fin.val_rev i

/-- The chronological source at index `r.rev` has final radius `r`.
@isnad1 id=eq.0h2v.s3.88207f03379a from=translated src=- shape=74148a6e vocab=fb6f21d5
-/
@[simp]
theorem chronologicalRadius_rev {t : ℕ} (r : Fin t) :
    chronologicalRadius r.rev = r.1 := by
  simp [chronologicalRadius]

/-- The chronological form of the burning-cover condition.-/
def IsChronologicalCover (G : SimpleGraph V) {t : ℕ} (sources : Fin t → V) : Prop :=
  ∀ v, ∃ i : Fin t, v ∈ G.closedBall (sources i) (chronologicalRadius i)

/--
@isnad1 id=iff.0h4v.s4.0b75d074146a from=translated src=- shape=6bc2e6e0 vocab=40fe69eb
-/
theorem isChronologicalCover_iff_isRankedCover {G : SimpleGraph V} {t : ℕ}
    {sources : Fin t → V} :
    G.IsChronologicalCover sources ↔ G.IsRankedCover (chronologicalToRanked sources) := by
  constructor
  · intro h v
    obtain ⟨i, hi⟩ := h v
    exact ⟨i.rev, by simpa [chronologicalRadius] using hi⟩
  · intro h v
    obtain ⟨r, hr⟩ := h v
    exact ⟨r.rev, by simpa [chronologicalRadius] using hr⟩

/-! ## Burning number -/

/-- A positive natural number is a feasible burning length when it supports a ranked cover.-/
def IsBurningLength (G : SimpleGraph V) (t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ centers : Fin t → V, G.IsRankedCover centers

/--
A positive length admits a ranked cover exactly when it admits the chronological
source-ball formulation of the burning process.
@isnad1 id=iff.0h3v.s5.4f5a7d51ce04 from=translated src=- shape=00c2931c vocab=769f1e28
-/
theorem isBurningLength_iff_exists_isChronologicalCover {G : SimpleGraph V} {t : ℕ} :
    G.IsBurningLength t ↔
      1 ≤ t ∧ ∃ sources : Fin t → V, G.IsChronologicalCover sources := by
  constructor
  · rintro ⟨ht, centers, hcover⟩
    refine ⟨ht, rankedToChronological centers, ?_⟩
    rw [isChronologicalCover_iff_isRankedCover]
    simpa
  · rintro ⟨ht, sources, hcover⟩
    exact
      ⟨ht, chronologicalToRanked sources,
        isChronologicalCover_iff_isRankedCover.mp hcover⟩

/-- Every graph on a finite nonempty vertex type has a feasible burning length.
@isnad1 id=ex.0h2v.s4.51096523fd39 from=translated src=- shape=b184f226 vocab=ef3167d6
-/
theorem exists_isBurningLength [Finite V] [Nonempty V] (G : SimpleGraph V) :
    ∃ t, G.IsBurningLength t := by
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  refine ⟨Fintype.card V, Fintype.card_pos, e.symm, ?_⟩
  intro v
  refine ⟨e v, ?_⟩
  simp [closedBall]

/-- Feasible burning lengths are upward closed.
@isnad1 id=isburnin.2h4v.s4.27ef3521ba0f from=translated src=- shape=5d1452b4 vocab=b9671d4c
-/
theorem IsBurningLength.mono [Nonempty V] {G : SimpleGraph V} {s t : ℕ}
    (h : G.IsBurningLength s) (hst : s ≤ t) : G.IsBurningLength t := by
  refine ⟨h.1.trans hst, ?_⟩
  obtain ⟨centers, hcover⟩ := h.2
  exact hcover.extendLength hst

/-- The burning number is the least positive length admitting a ranked cover.-/
noncomputable def burningNumber [Fintype V] [Nonempty V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find G.exists_isBurningLength

/-- The burning number itself is a feasible burning length.
@isnad1 id=isburnin.0h2v.s4.a9e98bc7f52b from=translated src=- shape=fe3051fb vocab=d454258f
-/
theorem burningNumber_spec [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    G.IsBurningLength G.burningNumber := by
  classical
  simpa only [burningNumber] using Nat.find_spec G.exists_isBurningLength

/--
@isnad1 id=le.0h2v.s4.13a5d5df6fda from=translated src=- shape=abec20dc vocab=7b660dd1
-/
theorem one_le_burningNumber [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    1 ≤ G.burningNumber :=
  (G.burningNumber_spec).1

/-- The burning number is no larger than any feasible burning length.
@isnad1 id=le.1h3v.s4.e653b1c8892f from=translated src=- shape=02a20c49 vocab=42a5dfe4
-/
theorem burningNumber_min [Fintype V] [Nonempty V] (G : SimpleGraph V) {t : ℕ}
    (h : G.IsBurningLength t) : G.burningNumber ≤ t := by
  classical
  simpa only [burningNumber] using Nat.find_min' G.exists_isBurningLength h

/-- A length is at least the burning number exactly when it admits a ranked cover.
@isnad1 id=iff.0h3v.s5.5fdc241be72b from=translated src=- shape=8085a1a0 vocab=842db2c8
-/
theorem burningNumber_le_iff [Fintype V] [Nonempty V] (G : SimpleGraph V) {t : ℕ} :
    G.burningNumber ≤ t ↔
      1 ≤ t ∧ ∃ centers : Fin t → V, G.IsRankedCover centers := by
  change G.burningNumber ≤ t ↔ G.IsBurningLength t
  constructor
  · exact fun h ↦ G.burningNumber_spec.mono h
  · exact G.burningNumber_min

end SimpleGraph
