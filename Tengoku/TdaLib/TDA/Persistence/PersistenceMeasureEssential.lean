import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasure
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The essential boundary of a q-tame persistence measure

The strip value at a finite target is the dimension of `im(b → c) / im(a → c)`.
As the target increases these natural numbers decrease. Their minimum is attained,
and all sufficiently late targets have that value. This defines the measure on the
death-at-infinity boundary without requiring finite-dimensional fibers or an interval
decomposition. Birth-coordinate splitting remains additive on this boundary.
-/

universe u w

namespace TDA.Persistence

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- The image quotient counting births in a strip that survive to a finite target.-/
abbrev PersistenceTailSpace {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :=
  persistenceImage M hbc ⧸
    (persistenceImage M (hab.trans hbc)).comap (persistenceImage M hbc).subtype

/-- The finite-target strip count.-/
noncomputable def persistenceTailMeasureValue {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : ℕ :=
  Module.finrank k (PersistenceTailSpace M hab hbc)

/-- A finite crossing image makes the tail image quotient finite-dimensional.
@isnad1 id=finitedi.2h5v.s12.f600c73d63fd from=translated src=- shape=03174ba2 vocab=09b1591e
-/
theorem persistenceTailSpace_finiteDimensional {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    [FiniteDimensional k (persistenceImage M hbc)] :
    FiniteDimensional k (PersistenceTailSpace M hab hbc) := by
  infer_instance

/-- Rank formula for the finite-target strip count.
@isnad1 id=eq.2h5v.s11.a61a56745109 from=translated src=- shape=64658adc vocab=4100cb4d
-/
theorem persistenceTailMeasureValue_add_image {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceTailMeasureValue M hab hbc +
      Module.finrank k (persistenceImage M (hab.trans hbc)) =
        Module.finrank k (persistenceImage M hbc) := by
  have h := Submodule.finrank_quotient_add_finrank
    ((persistenceImage M (hab.trans hbc)).comap (persistenceImage M hbc).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (persistenceImage_mono M hab hbc)).finrank_eq] at h
  exact h

/-- The mass lost from a tail strip is precisely the intervening rectangle mass.
@isnad1 id=eq.3h6v.s9.8f92ebcd9590 from=translated src=- shape=ad6bb6a8 vocab=08e8be33
-/
theorem persistenceMeasureValue_add_tail {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceMeasureValue M hab hbc hcd +
      persistenceTailMeasureValue M hab (hbc.trans hcd) =
        persistenceTailMeasureValue M hab hbc := by
  have : FiniteDimensional k (persistenceImage M (hbc.trans hcd)) :=
    persistenceImage_finiteDimensional_target M hbc hcd
  have h₁ := persistenceTailMeasureValue_add_image M hab hbc
  have h₂ := persistenceTailMeasureValue_add_image M hab (hbc.trans hcd)
  have h₃ := persistenceMeasureValue_four_rank M hab hbc hcd
  omega

/-- Tail-strip counts decrease with the target.
@isnad1 id=le.3h6v.s9.fb835d136c85 from=translated src=- shape=fcbbd8c6 vocab=790fa880
-/
theorem persistenceTailMeasureValue_antitone {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceTailMeasureValue M hab (hbc.trans hcd) ≤
      persistenceTailMeasureValue M hab hbc := by
  have := persistenceMeasureValue_add_tail M hab hbc hcd
  omega

/-- Splitting a finite-target birth strip is additive.
@isnad1 id=eq.3h6v.s9.9c8bfff96c55 from=translated src=- shape=f3118719 vocab=fe91c01d
-/
theorem persistenceTailMeasureValue_split_birth {a x b c : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hbc : b ≤ c)
    [FiniteDimensional k (persistenceImage M hbc)] :
    persistenceTailMeasureValue M (hax.trans hxb) hbc =
      persistenceTailMeasureValue M hax (hxb.trans hbc) +
        persistenceTailMeasureValue M hxb hbc := by
  have : FiniteDimensional k (persistenceImage M (hxb.trans hbc)) :=
    Submodule.finiteDimensional_of_le (persistenceImage_mono M hxb hbc)
  have h₁ := persistenceTailMeasureValue_add_image M (hax.trans hxb) hbc
  have h₂ := persistenceTailMeasureValue_add_image M hax (hxb.trans hbc)
  have h₃ := persistenceTailMeasureValue_add_image M hxb hbc
  omega

/-- The measure of a birth strip on the essential, death-at-infinity boundary.
For a q-tame module this is the eventual finite-target strip count.-/
noncomputable def essentialMeasureValue {a b : ℝ} (hab : a ≤ b) : ℕ :=
  sInf {n | ∃ (c : ℝ) (hbc : b < c), persistenceTailMeasureValue M hab hbc.le = n}

/-- The essential strip count is a lower bound for every finite-target count.
@isnad1 id=le.2h5v.s5.058ca4c4fb8a from=translated src=- shape=34b5c4ed vocab=3b20035a
-/
theorem essentialMeasureValue_le_tail {a b c : ℝ} (hab : a ≤ b) (hbc : b < c) :
    essentialMeasureValue M hab ≤ persistenceTailMeasureValue M hab hbc.le :=
  csInf_le' ⟨c, hbc, rfl⟩

/-- The essential boundary count is locally finite, bounded by any strict crossing rank.
@isnad1 id=le.2h5v.s10.8cd95477f297 from=translated src=- shape=8792796f vocab=79ea0a48
-/
theorem essentialMeasureValue_le_crossing_rank {a b c : ℝ} (hab : a ≤ b) (hbc : b < c)
    [FiniteDimensional k (persistenceImage M hbc.le)] :
    essentialMeasureValue M hab ≤ Module.finrank k (persistenceImage M hbc.le) := by
  have h := persistenceTailMeasureValue_add_image M hab hbc.le
  have h' := essentialMeasureValue_le_tail M hab hbc
  omega

/-- The minimum defining the essential boundary is attained at a finite target.
@isnad1 id=ex.1h4v.s5.0f6a1d6e61db from=translated src=- shape=57a6c27d vocab=3b20035a
-/
theorem exists_tail_eq_essentialMeasureValue {a b : ℝ} (hab : a ≤ b) :
    ∃ (c : ℝ) (hbc : b < c),
      persistenceTailMeasureValue M hab hbc.le = essentialMeasureValue M hab := by
  exact csInf_mem (s := {n | ∃ (c : ℝ) (hbc : b < c),
    persistenceTailMeasureValue M hab hbc.le = n})
    ⟨persistenceTailMeasureValue M hab (show b ≤ b + 1 by linarith),
      b + 1, by linarith, rfl⟩

/-- For a q-tame module the essential strip count is attained permanently.
This is an eventual-value construction, rather than an assumption about essential bars.
@isnad1 id=ex.2h4v.s6.37729d7d1277 from=translated src=- shape=ad5b472c vocab=767faa9c
-/
theorem PModule.QTame.essentialMeasureValue_eventually (hM : M.QTame)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ (c : ℝ) (hbc : b < c), ∀ (d : ℝ) (hcd : c ≤ d),
      persistenceTailMeasureValue M hab (hbc.le.trans hcd) = essentialMeasureValue M hab := by
  obtain ⟨c, hbc, hc⟩ := exists_tail_eq_essentialMeasureValue M hab
  refine ⟨c, hbc, fun d hcd => ?_⟩
  have : FiniteDimensional k (persistenceImage M hbc.le) := hM b c hbc
  apply le_antisymm
  · exact (persistenceTailMeasureValue_antitone M hab hbc.le hcd).trans_eq hc
  · exact essentialMeasureValue_le_tail M hab (hbc.trans_le hcd)

/-- After a sufficiently late target, a fixed birth strip has no further finite deaths.
@isnad1 id=ex.2h4v.s6.159ca401a949 from=translated src=- shape=9ad3a5c3 vocab=e47f80a7
-/
theorem PModule.QTame.persistenceMeasureValue_eventually_zero (hM : M.QTame)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ (c : ℝ) (hbc : b < c), ∀ (d : ℝ) (hcd : c ≤ d),
      persistenceMeasureValue M hab hbc.le hcd = 0 := by
  obtain ⟨c, hbc, hc⟩ := PModule.QTame.essentialMeasureValue_eventually M hM hab
  refine ⟨c, hbc, fun d hcd => ?_⟩
  have : FiniteDimensional k (persistenceImage M hbc.le) := hM b c hbc
  have h := persistenceMeasureValue_add_tail M hab hbc.le hcd
  rw [hc d hcd, hc c le_rfl] at h
  omega

/-- Essential boundary mass is additive under birth-coordinate splitting.
@isnad1 id=eq.3h5v.s6.34707f57c3c0 from=translated src=- shape=98b58b23 vocab=e5f184a6
-/
theorem PModule.QTame.essentialMeasureValue_split_birth (hM : M.QTame)
    {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    essentialMeasureValue M (hax.trans hxb) =
      essentialMeasureValue M hax + essentialMeasureValue M hxb := by
  obtain ⟨c₀, hb₀, h₀⟩ := PModule.QTame.essentialMeasureValue_eventually M hM (hax.trans hxb)
  obtain ⟨c₁, _, h₁⟩ := PModule.QTame.essentialMeasureValue_eventually M hM hax
  obtain ⟨c₂, _, h₂⟩ := PModule.QTame.essentialMeasureValue_eventually M hM hxb
  let d := max c₀ (max c₁ c₂)
  have h₀d : c₀ ≤ d := le_max_left _ _
  have h₁d : c₁ ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have h₂d : c₂ ≤ d := (le_max_right _ _).trans (le_max_right _ _)
  have hbd : b < d := hb₀.trans_le h₀d
  have : FiniteDimensional k (persistenceImage M hbd.le) := hM b d hbd
  have h := persistenceTailMeasureValue_split_birth M hax hxb hbd.le
  rw [h₀ d h₀d, h₁ d h₁d, h₂ d h₂d] at h
  exact h

/-- A degenerate birth strip has zero essential boundary measure.
@isnad1 id=eq.1h3v.s5.e6b1ae307e01 from=translated src=- shape=28c0f392 vocab=a85466c9
-/
@[simp] theorem PModule.QTame.essentialMeasureValue_self (hM : M.QTame) (a : ℝ) :
    essentialMeasureValue M (le_refl a) = 0 := by
  have h := PModule.QTame.essentialMeasureValue_split_birth M hM (le_refl a) (le_refl a)
  omega

end TDA.Persistence
