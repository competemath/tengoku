import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BlockClassification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ranked covers from block classes

This file constructs ranked covers for the explicit ordered-coordinate path metric. Conversion to
graph-distance burning covers is deferred until the graph metric theorem is available.
-/

namespace BurningPath

/-- A ranked cover for the explicit path-configuration metric.-/
def IsPathMetricRankedCover {n k t : ℕ}
    (centers : Fin t → Configuration (Fin n) k) : Prop :=
  ∀ A, ∃ r : Fin t, pathConfigurationDist A (centers r) ≤ r.val

/-- A subcover using a pairwise distinct selection of the available radii.-/
def IsPathMetricRankedSubcover {n k t : ℕ} {ι : Type*} (radii : ι ↪ Fin t)
    (centers : ι → Configuration (Fin n) k) : Prop :=
  ∀ A, ∃ i : ι, pathConfigurationDist A (centers i) ≤ (radii i).val

/-- Existence of a ranked cover of the given length for the explicit path metric.-/
def HasPathMetricRankedCover (n k t : ℕ) : Prop :=
  ∃ centers : Fin t → Configuration (Fin n) k, IsPathMetricRankedCover centers

/-- Fill every radius omitted by an explicit-metric ranked subcover.
@isnad1 id=ex.1h6v.s6.ad81bdbe864b from=translated src=- shape=8ca93122 vocab=c37f6627
-/
theorem IsPathMetricRankedSubcover.extend [Nonempty (Configuration (Fin n) k)]
    {t : ℕ} {ι : Type*} {radii : ι ↪ Fin t}
    {centers : ι → Configuration (Fin n) k}
    (h : IsPathMetricRankedSubcover radii centers) :
    ∃ fullCenters : Fin t → Configuration (Fin n) k,
      IsPathMetricRankedCover fullCenters ∧
        ∀ i, fullCenters (radii i) = centers i := by
  classical
  let fullCenters : Fin t → Configuration (Fin n) k :=
    Function.extend radii centers
      (fun _ ↦ Classical.choice (inferInstance : Nonempty (Configuration (Fin n) k)))
  have hfull : ∀ i, fullCenters (radii i) = centers i := by
    intro i
    exact radii.injective.extend_apply centers
      (fun _ ↦ Classical.choice (inferInstance : Nonempty (Configuration (Fin n) k))) i
  refine ⟨fullCenters, ?_, hfull⟩
  intro A
  obtain ⟨i, hi⟩ := h A
  refine ⟨radii i, ?_⟩
  rw [hfull i]
  exact hi

/-- Increasing the available length preserves explicit-metric ranked coverage.
@isnad1 id=haspathm.2h5v.s5.4892105ed484 from=translated src=- shape=1408f7ec vocab=8b91eeb3
-/
theorem IsPathMetricRankedCover.extendLength [Nonempty (Configuration (Fin n) k)]
    {u v : ℕ} {centers : Fin u → Configuration (Fin n) k}
    (h : IsPathMetricRankedCover centers) (huv : u ≤ v) :
    HasPathMetricRankedCover n k v := by
  have hsub :
      IsPathMetricRankedSubcover (Fin.castLEEmb huv) centers := by
    intro A
    obtain ⟨r, hr⟩ := h A
    exact ⟨r, hr⟩
  obtain ⟨fullCenters, hcover, _⟩ := hsub.extend
  exact ⟨fullCenters, hcover⟩

/-- The signatures actually realized by path-token configurations.-/
noncomputable def realizedBlockSignatures (n k s : ℕ) (hs : 1 ≤ s) :
    Finset (BlockSignature n k s) :=
  Finset.univ.image (blockSignature s hs)

/-- The number of nonempty block classes.-/
noncomputable def realizedBlockClassCount (n k s : ℕ) (hs : 1 ≤ s) : ℕ :=
  (realizedBlockSignatures n k s hs).card

/-- The number of realized block classes is at most the full stars-and-bars count.
@isnad1 id=le.1h3v.s5.ad9bdaa60668 from=translated src=- shape=64287b29 vocab=3c7d6139
-/
theorem realizedBlockClassCount_le (n k s : ℕ) (hs : 1 ≤ s) :
    realizedBlockClassCount n k s hs ≤
      Nat.choose (blockCount n s + k - 1) k := by
  rw [← card_blockSignature n k s]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- Embed `Fin M` into the top `M` radii of a list of length `M + R`.-/
private def highRadiusEmbedding (R M : ℕ) : Fin M ↪ Fin (M + R) where
  toFun i := ⟨R + i.val, by omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

@[simp]
private theorem highRadiusEmbedding_val (R M : ℕ) (i : Fin M) :
    (highRadiusEmbedding R M i).val = R + i.val := by
  rfl

private theorem configuration_nonempty_of_le {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (Configuration (Fin n) k) := by
  obtain ⟨A, hA, hcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (by simpa using hkn)
  exact ⟨⟨A, hcard⟩⟩

/--
The nonempty block classes give a ranked cover whose length is their number plus the common
within-class radius.
@isnad1 id=haspathm.2h3v.s5.8ff267e7040a from=translated src=- shape=d4b543fc vocab=0110d1ec
-/
theorem hasPathMetricRankedCover_realizedBlockClasses {n k : ℕ} (hkn : k ≤ n)
    (s : ℕ) (hs : 1 ≤ s) :
    HasPathMetricRankedCover n k
      (realizedBlockClassCount n k s hs + k * (s - 1)) := by
  classical
  letI : Nonempty (Configuration (Fin n) k) := configuration_nonempty_of_le hkn
  let signatures := realizedBlockSignatures n k s hs
  let M := signatures.card
  let R := k * (s - 1)
  have representative_exists :
      ∀ σ : signatures, ∃ A : Configuration (Fin n) k,
        blockSignature s hs A = σ.1 := by
    intro σ
    rcases Finset.mem_image.mp σ.2 with ⟨A, hA, hsignature⟩
    exact ⟨A, hsignature⟩
  choose representative hrepresentative using representative_exists
  let enumerate : signatures ≃ Fin M := signatures.equivFin
  let radii : signatures ↪ Fin (M + R) :=
    enumerate.toEmbedding.trans (highRadiusEmbedding R M)
  have hsub : IsPathMetricRankedSubcover radii representative := by
    intro A
    let σ : signatures :=
      ⟨blockSignature s hs A, Finset.mem_image.mpr ⟨A, Finset.mem_univ A, rfl⟩⟩
    refine ⟨σ, ?_⟩
    have hdist :
        pathConfigurationDist A (representative σ) ≤ R := by
      apply pathConfigurationDist_le_of_blockSignature_eq s hs
      simpa [σ] using (hrepresentative σ).symm
    calc
      pathConfigurationDist A (representative σ) ≤ R := hdist
      _ ≤ (radii σ).val := by
        change R ≤ R + (enumerate σ).val
        exact Nat.le_add_right R _
  obtain ⟨centers, hcover, _⟩ := hsub.extend
  simpa [M, R, realizedBlockClassCount, signatures] using
    (show HasPathMetricRankedCover n k (M + R) from ⟨centers, hcover⟩)

/-- Package the realized class count, its exact combinatorial bound, and its ranked cover.
@isnad1 id=ex.2h3v.s6.e4e1d60f76c1 from=translated src=- shape=88dee315 vocab=40e67f92
-/
theorem exists_blockClassCount_and_pathMetricRankedCover {n k : ℕ} (hkn : k ≤ n)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ M', M' ≤ Nat.choose (blockCount n s + k - 1) k ∧
      HasPathMetricRankedCover n k (M' + k * (s - 1)) :=
  ⟨realizedBlockClassCount n k s hs, realizedBlockClassCount_le n k s hs,
    hasPathMetricRankedCover_realizedBlockClasses hkn s hs⟩

/--
There is an explicit-metric ranked cover whose length is at most the finite block upper bound.
@isnad1 id=ex.2h3v.s6.80627186b155 from=translated src=- shape=8d6c331d vocab=f27564e4
-/
theorem exists_pathMetricRankedCover_length_le_blockBound {n k : ℕ} (hkn : k ≤ n)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ t, t ≤ Nat.choose (n ⌈/⌉ s + k - 1) k + k * (s - 1) ∧
      HasPathMetricRankedCover n k t := by
  refine
    ⟨realizedBlockClassCount n k s hs + k * (s - 1), ?_,
      hasPathMetricRankedCover_realizedBlockClasses hkn s hs⟩
  exact Nat.add_le_add_right
    (by simpa [blockCount] using realizedBlockClassCount_le n k s hs) _

/-- A ranked cover exists at the exact finite block upper-bound length.
@isnad1 id=haspathm.2h3v.s6.0dddb3611258 from=translated src=- shape=b8300238 vocab=f27564e4
-/
theorem hasPathMetricRankedCover_blockBound {n k : ℕ} (hkn : k ≤ n)
    (s : ℕ) (hs : 1 ≤ s) :
    HasPathMetricRankedCover n k
      (Nat.choose (n ⌈/⌉ s + k - 1) k + k * (s - 1)) := by
  letI : Nonempty (Configuration (Fin n) k) := configuration_nonempty_of_le hkn
  obtain ⟨centers, hcover⟩ :=
    hasPathMetricRankedCover_realizedBlockClasses hkn s hs
  apply hcover.extendLength
  exact Nat.add_le_add_right
    (by simpa [blockCount] using realizedBlockClassCount_le n k s hs) _

end BurningPath
