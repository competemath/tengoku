/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.LanaOka.Oka.Uniformization.CoveringLift
import Tengoku.LanaOka.Oka.Uniformization.Holomorphic
import Tengoku.LanaOka.Oka.Uniformization.KoebeMap
import Tengoku.Seed.Topology.MetricSpace.HausdorffDistance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Koebe–Fisher–Hubbard–Wittner iteration

Let `U₀ ⊆ 𝔻` be open with `0 ∈ U₀`. We build open sets `U₀, U₁, U₂, …` in `𝔻` containing `0`
and maps `qₙ₊₁ : Uₙ₊₁ → Uₙ` which are covering maps: if `a` is a point of `ℂ ∖ Uₙ` closest to `0`
and `|a| < 1`, then `qₙ₊₁ = koebe b` with `b² = -a` and `Uₙ₊₁ = qₙ₊₁ ⁻¹' Uₙ` (the Koebe map is a
covering off its critical value `a ∉ Uₙ`); if `|a| ≥ 1` then `Uₙ = 𝔻` and `qₙ₊₁` is the identity.
The composites `projₙ = q₁ ∘ ⋯ ∘ qₙ : Uₙ → U₀` lift maps from convex sets
(`Uniformization.Good.exists_lift`), are holomorphic and locally injective, and — by the Koebe
estimate `norm_koebe_lt` — the in-radius of `Uₙ` about `0` tends to `1`
(`Uniformization.Good.exists_ball_subset`).

This is the construction of [Fisher–Hubbard–Wittner, *A proof of the uniformization theorem for
arbitrary plane domains*, Proc. AMS 104 (1988)], §3, parts b and c, with the abstract universal
cover removed: only the plane domains `Uₙ` occur.
-/

open Complex Metric Set Filter Topology

namespace Uniformization

/-! ### One step -/

/-- The in-radius of `U` about `0`: the distance from `0` to the complement. -/
noncomputable def inradius (U : Set ℂ) : ℝ := infDist (0 : ℂ) Uᶜ

/-- The standing hypotheses on the sets of the iteration. -/
structure Good (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  subset_ball : U ⊆ ball 0 1
  zero_mem : (0 : ℂ) ∈ U

theorem ball_inradius_subset (U : Set ℂ) : ball 0 (inradius U) ⊆ U := by
  intro z hz
  by_contra h
  have := infDist_le_dist_of_mem (x := (0 : ℂ)) (show z ∈ Uᶜ from h)
  rw [mem_ball, dist_comm] at hz
  exact absurd (this.trans_lt hz) (lt_irrefl _)

theorem Good.compl_nonempty {U : Set ℂ} (hU : Good U) : (Uᶜ).Nonempty :=
  ⟨1, fun h ↦ by simpa using hU.subset_ball h⟩

theorem Good.inradius_pos {U : Set ℂ} (hU : Good U) : 0 < inradius U :=
  (hU.isOpen.isClosed_compl.notMem_iff_infDist_pos hU.compl_nonempty).mp
    fun h ↦ h hU.zero_mem

theorem Good.inradius_le_one {U : Set ℂ} (hU : Good U) : inradius U ≤ 1 := by
  have := infDist_le_dist_of_mem (x := (0 : ℂ)) (show (1 : ℂ) ∈ Uᶜ from
    fun h ↦ by simpa using hU.subset_ball h)
  change infDist (0 : ℂ) Uᶜ ≤ 1
  simpa using this

theorem le_inradius {U : Set ℂ} (hU : Good U) {r : ℝ} (h : ball 0 r ⊆ U) : r ≤ inradius U := by
  refine (le_infDist hU.compl_nonempty).mpr fun y hy ↦ ?_
  by_contra hlt
  push Not at hlt
  exact hy (h (by rwa [mem_ball, dist_comm]))

theorem Good.exists_crit {U : Set ℂ} (hU : Good U) : ∃ a, a ∉ U ∧ ‖a‖ = inradius U := by
  obtain ⟨a, ha, hd⟩ := hU.isOpen.isClosed_compl.exists_infDist_eq_dist hU.compl_nonempty 0
  exact ⟨a, ha, by rw [inradius, hd, dist_comm, dist_zero_right]⟩

/-- A point of `ℂ ∖ U` closest to `0`. -/
noncomputable def crit (U : Set ℂ) : ℂ := by
  classical
  exact if h : ∃ a, a ∉ U ∧ ‖a‖ = inradius U then h.choose else 0

theorem Good.crit_spec {U : Set ℂ} (hU : Good U) : crit U ∉ U ∧ ‖crit U‖ = inradius U := by
  have h := hU.exists_crit
  simp only [crit, h, dite_true]
  exact h.choose_spec

/-- A square root of `-crit U`. -/
noncomputable def critRoot (U : Set ℂ) : ℂ := (-crit U) ^ (((2 : ℕ) : ℂ)⁻¹)

theorem critRoot_sq (U : Set ℂ) : critRoot U ^ 2 = -crit U :=
  cpow_nat_inv_pow _ two_ne_zero

theorem norm_critRoot_sq (U : Set ℂ) : ‖critRoot U‖ ^ 2 = ‖crit U‖ := by
  rw [← norm_pow, critRoot_sq, norm_neg]

/-- The identity on `𝔻`, and `2` outside `𝔻`. -/
noncomputable def discId (z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball (0 : ℂ) 1 then z else 2

theorem discId_of_mem {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : discId z = z := by
  simp [discId, hz]

theorem preimage_discId {U : Set ℂ} (hU : U ⊆ ball 0 1) : discId ⁻¹' U = U := by
  ext z
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · simp [discId_of_mem hz]
  · simp only [mem_preimage, discId, hz, ite_false]
    exact ⟨fun h ↦ absurd (hU h) two_notMem_ball, fun h ↦ absurd (hU h) hz⟩

/-- The map of one step of the iteration. -/
noncomputable def stepMap (U : Set ℂ) : ℂ → ℂ := by
  classical
  exact if ‖crit U‖ < 1 then koebe (critRoot U) else discId

/-- The set of one step of the iteration. -/
def stepSet (U : Set ℂ) : Set ℂ := stepMap U ⁻¹' U

theorem Good.critRoot_mem_ball {U : Set ℂ} (h : ‖crit U‖ < 1) : critRoot U ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  have := norm_critRoot_sq U
  nlinarith [norm_nonneg (critRoot U)]

theorem stepMap_zero (U : Set ℂ) : stepMap U 0 = 0 := by
  unfold stepMap
  split_ifs
  · exact koebe_zero _
  · exact discId_of_mem (mem_ball_self one_pos)

theorem stepMap_mem_ball {U : Set ℂ} {z : ℂ} (hz : stepMap U z ∈ ball (0 : ℂ) 1) :
    z ∈ ball (0 : ℂ) 1 := by
  unfold stepMap at hz
  split_ifs at hz
  · exact mem_ball_of_koebe_mem hz
  · by_contra h
    simp only [discId, h, ite_false] at hz
    exact two_notMem_ball hz

theorem differentiableOn_stepMap {U : Set ℂ} : DifferentiableOn ℂ (stepMap U) (ball 0 1) := by
  unfold stepMap
  split_ifs with h
  · exact differentiableOn_koebe (Good.critRoot_mem_ball h)
  · exact differentiableOn_id.congr fun z hz ↦ discId_of_mem hz

theorem Good.isCoveringMapOn_stepMap {U : Set ℂ} (hU : Good U) :
    IsCoveringMapOn (stepMap U) U := by
  unfold stepMap
  split_ifs with h
  · have hb := Good.critRoot_mem_ball h
    refine (isCoveringMapOn_koebe hb).mono fun z hz ↦ ⟨hU.subset_ball hz, fun hz' ↦ ?_⟩
    rw [mem_singleton_iff, critRoot_sq, neg_neg] at hz'
    exact hU.crit_spec.1 (hz' ▸ hz)
  · have heq := preimage_discId hU.subset_ball
    refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hU.isOpen
      (by rw [heq]; exact hU.isOpen) ?_
    have : U.restrictPreimage discId = Homeomorph.setCongr heq := by
      funext z
      apply Subtype.ext
      have hz : (z : ℂ) ∈ U := (Set.ext_iff.mp heq z).mp z.2
      exact discId_of_mem (hU.subset_ball hz)
    rw [this]
    exact isCoveringMap_homeomorph _

theorem Good.good_stepSet {U : Set ℂ} (hU : Good U) : Good (stepSet U) where
  isOpen := by
    have : stepSet U = ball 0 1 ∩ stepMap U ⁻¹' U := by
      ext z
      exact ⟨fun h ↦ ⟨stepMap_mem_ball (hU.subset_ball h), h⟩, fun h ↦ h.2⟩
    rw [this]
    exact differentiableOn_stepMap.continuousOn.isOpen_inter_preimage isOpen_ball hU.isOpen
  subset_ball := fun _ h ↦ stepMap_mem_ball (hU.subset_ball h)
  zero_mem := by
    change stepMap U 0 ∈ U
    rw [stepMap_zero]; exact hU.zero_mem

/-- The radius guaranteed after one step. -/
noncomputable def nextRadius (r : ℝ) : ℝ := by
  classical
  exact if r < 1 then koebeRadius r else 1

theorem Good.ball_nextRadius_subset {U : Set ℂ} (hU : Good U) :
    ball 0 (nextRadius (inradius U)) ⊆ stepSet U := by
  obtain ⟨hcU, hcr⟩ := hU.crit_spec
  intro z hz
  change stepMap U z ∈ U
  unfold stepMap
  split_ifs with h
  · have hb := Good.critRoot_mem_ball h
    have hr : inradius U < 1 := hcr ▸ h
    have hz' : ‖z‖ < koebeRadius (‖critRoot U‖ ^ 2) := by
      rw [norm_critRoot_sq, hcr]
      simpa [nextRadius, hr] using hz
    obtain ⟨-, hlt⟩ := norm_koebe_lt hb hz'
    apply ball_inradius_subset
    rw [mem_ball_zero_iff, ← hcr, ← norm_critRoot_sq]
    exact hlt
  · have hr : ¬ inradius U < 1 := hcr ▸ h
    have hz1 : z ∈ ball (0 : ℂ) 1 := by simpa [nextRadius, hr] using hz
    rw [discId_of_mem hz1]
    apply ball_inradius_subset
    exact ball_subset_ball (not_lt.mp hr) hz1

theorem le_nextRadius {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : r ≤ nextRadius r := by
  unfold nextRadius
  split_ifs with h
  · exact (lt_koebeRadius hr0 h).le
  · exact hr1

/-! ### The sequence -/

variable (U₀ : Set ℂ)

/-- The domains `Uₙ` of the iteration. -/
def seq : ℕ → Set ℂ
  | 0 => U₀
  | n + 1 => stepSet (seq n)

/-- The composites `q₁ ∘ ⋯ ∘ qₙ : Uₙ → U₀`. -/
noncomputable def proj : ℕ → ℂ → ℂ
  | 0 => id
  | n + 1 => proj n ∘ stepMap (seq U₀ n)

variable {U₀}

theorem Good.good_seq (hU₀ : Good U₀) : ∀ n, Good (seq U₀ n)
  | 0 => hU₀
  | n + 1 => (hU₀.good_seq n).good_stepSet

theorem proj_zero : ∀ n, proj U₀ n 0 = 0
  | 0 => rfl
  | n + 1 => by simp [proj, stepMap_zero, proj_zero n]

theorem mapsTo_proj : ∀ n, MapsTo (proj U₀ n) (seq U₀ n) U₀
  | 0 => fun _ h ↦ h
  | n + 1 => fun _ h ↦ mapsTo_proj n h

theorem Good.differentiableOn_proj (hU₀ : Good U₀) :
    ∀ n, DifferentiableOn ℂ (proj U₀ n) (seq U₀ n)
  | 0 => differentiableOn_id
  | n + 1 => (hU₀.differentiableOn_proj n).comp
      (differentiableOn_stepMap.mono (hU₀.good_seq (n + 1)).subset_ball) fun _ h ↦ h

theorem Good.exists_nhds_injOn_proj (hU₀ : Good U₀) :
    ∀ n, ∀ z ∈ seq U₀ n, ∃ V ∈ 𝓝 z, InjOn (proj U₀ n) V
  | 0 => fun z _ ↦ ⟨univ, univ_mem, Function.injective_id.injOn⟩
  | n + 1 => by
    intro z hz
    have hcov := (hU₀.good_seq n).isCoveringMapOn_stepMap
    obtain ⟨φ, hzφ, hφ⟩ := hcov.isLocalHomeomorphOn z hz
    obtain ⟨V, hV, hinj⟩ := hU₀.exists_nhds_injOn_proj n _ hz
    have hcont : ContinuousAt (stepMap (seq U₀ n)) z := hcov.continuousAt hz
    refine ⟨φ.source ∩ stepMap (seq U₀ n) ⁻¹' V,
      inter_mem (φ.open_source.mem_nhds hzφ) (hcont.preimage_mem_nhds hV), ?_⟩
    intro x hx y hy hxy
    have h1 : stepMap (seq U₀ n) x = stepMap (seq U₀ n) y := hinj hx.2 hy.2 hxy
    rw [hφ] at h1
    exact φ.injOn hx.1 hy.1 h1

theorem Good.deriv_proj_ne_zero (hU₀ : Good U₀) (n : ℕ) {z : ℂ} (hz : z ∈ seq U₀ n) :
    deriv (proj U₀ n) z ≠ 0 := by
  obtain ⟨V, hV, hinj⟩ := hU₀.exists_nhds_injOn_proj n z hz
  exact deriv_ne_zero_of_injOn ((hU₀.differentiableOn_proj n).mono inter_subset_right)
    (inter_mem hV ((hU₀.good_seq n).isOpen.mem_nhds hz)) (hinj.mono inter_subset_left)

/-- **Lifting through the iteration.** A continuous map from a convex set into `U₀` lifts through
`projₙ : Uₙ → U₀`, with a prescribed value at one point. -/
theorem Good.exists_lift (hU₀ : Good U₀) :
    ∀ n (D : Set ℂ), Convex ℝ D → ∀ g : ℂ → ℂ, ContinuousOn g D → MapsTo g D U₀ →
      ∀ a₀ e : ℂ, a₀ ∈ D → e ∈ seq U₀ n → proj U₀ n e = g a₀ →
      ∃ σ : ℂ → ℂ, ContinuousOn σ D ∧ MapsTo σ D (seq U₀ n) ∧
        (∀ a ∈ D, proj U₀ n (σ a) = g a) ∧ σ a₀ = e
  | 0 => by
    intro D _ g hg hgU a₀ e _ _ he
    exact ⟨g, hg, hgU, fun _ _ ↦ rfl, he.symm⟩
  | n + 1 => by
    intro D hD g hg hgU a₀ e ha₀ he hpe
    set q := stepMap (seq U₀ n)
    obtain ⟨σ', hσ'c, hσ'm, hσ'p, hσ'0⟩ :=
      hU₀.exists_lift n D hD g hg hgU a₀ (q e) ha₀ he hpe
    obtain ⟨σ, hσc, hσq, hσ0⟩ := (hU₀.good_seq n).isCoveringMapOn_stepMap.exists_lift_of_convex hD
      hσ'c hσ'm ha₀ (e₀ := e) hσ'0.symm
    refine ⟨σ, hσc, fun a ha ↦ ?_, fun a ha ↦ ?_, hσ0⟩
    · change stepMap (seq U₀ n) (σ a) ∈ seq U₀ n
      rw [hσq a ha]; exact hσ'm ha
    · change proj U₀ n (stepMap (seq U₀ n) (σ a)) = g a
      rw [hσq a ha, hσ'p a ha]

/-! ### Exhaustion -/

theorem Good.inradius_mono (hU₀ : Good U₀) (n : ℕ) :
    nextRadius (inradius (seq U₀ n)) ≤ inradius (seq U₀ (n + 1)) :=
  le_inradius (hU₀.good_seq (n + 1)) (hU₀.good_seq n).ball_nextRadius_subset

theorem Good.inradius_le_succ (hU₀ : Good U₀) (n : ℕ) :
    inradius (seq U₀ n) ≤ inradius (seq U₀ (n + 1)) :=
  (le_nextRadius (hU₀.good_seq n).inradius_pos (hU₀.good_seq n).inradius_le_one).trans
    (hU₀.inradius_mono n)

theorem Good.inradius_monotone (hU₀ : Good U₀) : Monotone fun n ↦ inradius (seq U₀ n) :=
  monotone_nat_of_le_succ hU₀.inradius_le_succ

/-- **The in-radii tend to `1`**: every disc `ball 0 R` with `R < 1` is eventually contained in
`Uₙ`. -/
theorem Good.exists_ball_subset (hU₀ : Good U₀) {R : ℝ} (hR : R < 1) :
    ∃ N, ∀ n ≥ N, ball 0 R ⊆ seq U₀ n := by
  set ρ := fun n ↦ inradius (seq U₀ n)
  suffices h : ∃ N, R ≤ ρ N by
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn ↦ (ball_subset_ball (hN.trans (hU₀.inradius_monotone hn))).trans
      (ball_inradius_subset _)⟩
  by_contra hcon
  push Not at hcon
  have hρ0 : 0 < ρ 0 := (hU₀.good_seq 0).inradius_pos
  -- the gain `koebeRadius r - r` is bounded below on `[ρ 0, R]`
  have hcomp : IsCompact (Icc (ρ 0) R) := isCompact_Icc
  have hne : (Icc (ρ 0) R).Nonempty := ⟨ρ 0, le_rfl, (hcon 0).le⟩
  have hcont : ContinuousOn (fun r ↦ koebeRadius r - r) (Icc (ρ 0) R) :=
    (continuousOn_koebeRadius.mono fun r hr ↦ (hρ0.le.trans hr.1 : (0 : ℝ) ≤ r)).sub
      continuousOn_id
  obtain ⟨r₀, hr₀, hmin⟩ := hcomp.exists_isMinOn hne hcont
  set δ := koebeRadius r₀ - r₀
  have hδ : 0 < δ := sub_pos.mpr (lt_koebeRadius (hρ0.trans_le hr₀.1) (hr₀.2.trans_lt hR))
  have hstep : ∀ n, ρ n + δ ≤ ρ (n + 1) := by
    intro n
    have hmem : ρ n ∈ Icc (ρ 0) R := ⟨hU₀.inradius_monotone (Nat.zero_le n), (hcon n).le⟩
    have h1 : δ ≤ koebeRadius (ρ n) - ρ n := hmin hmem
    have hlt : ρ n < 1 := (hcon n).trans hR
    have h2 : koebeRadius (ρ n) ≤ ρ (n + 1) := by
      have := hU₀.inradius_mono n
      simp only [nextRadius] at this
      rwa [ite_eq_left hlt] at this
    change ρ n + δ ≤ ρ (n + 1)
    linarith
  have hgrow : ∀ n : ℕ, ρ 0 + n * δ ≤ ρ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => push_cast; linarith [hstep k]
  obtain ⟨n, hn⟩ := exists_nat_gt (R / δ)
  have := hgrow n
  have h1 : R < n * δ := by rwa [div_lt_iff₀ hδ] at hn
  linarith [hcon n]

end Uniformization
