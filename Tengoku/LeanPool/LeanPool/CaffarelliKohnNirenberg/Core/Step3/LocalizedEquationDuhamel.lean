/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationTested
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationDuhamelKernels

/-!
# Localized Equation Duhamel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Core.Step3
open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

lemma localized_divergence_scalar_tested_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    (i : Fin 3) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ) :
    (∫ z, localizedVelocity (show ParabolicPoint → ℝ from φ) u z i *
        (-(timePartial ψ z) - ∑ j, spatialSecondPartial ψ j j z)) =
      (∫ z, localizedDivergenceG φ u Du p f z i * ψ z) +
        ∑ j, ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z := by
  let Ψ : Vec3 × ℝ → Vec3 := fun z k => if k = i then ψ z else 0
  have hΨd : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    rw [contDiff_pi]
    intro k
    by_cases hki : k = i
    · subst k
      simpa [Ψ] using hψ.1
    · change ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Vec3 × ℝ => if k = i then ψ z else 0)
      simp only [hki, ↓reduceIte]
      exact contDiff_const
  have hΨc : HasCompactSupport Ψ := by
    apply HasCompactSupport.of_support_subset_isCompact hψ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    have hzero : ψ z = 0 := image_eq_zero_of_notMem_tsupport hnot
    funext k
    simp [Ψ, hzero]
  have hΨ : Ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ := by
    refine ⟨hΨd, hΨc, ?_⟩
    simp [spaceTimeSet]
  have h := localized_divergence_tested_of_sws hsol hφ hbox hφbox hΨ
  have htime (k : Fin 3) :
      timePartial (fun w => if k = i then ψ w else 0) =
        fun z => if k = i then timePartial ψ z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, timePartial]
  have hsecond (k j : Fin 3) :
      spatialSecondPartial (fun w => if k = i then ψ w else 0) j j =
        fun z => if k = i then spatialSecondPartial ψ j j z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, spatialSecondPartial, spatialPartial]
  have hspatial (k j : Fin 3) :
      spatialPartial (fun w => if k = i then ψ w else 0) j =
        fun z => if k = i then spatialPartial ψ j z else 0 := by
    funext z
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
    · simp [hki, spatialPartial]
  simp only [Ψ] at h
  simp_rw [htime, hsecond, hspatial] at h
  classical
  simp only [Finset.mul_sum, mul_sub, mul_neg, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_ite_irrel,
    Finset.sum_const_zero] at h
  have hleft :
      (∫ z, localizedVelocity φ u z i *
        (-timePartial ψ z - ∑ j, spatialSecondPartial ψ j j z)) =
        ∫ z, -(localizedVelocity φ u z i *
          timePartial ψ z) - ∑ j, localizedVelocity
            φ u z i * spatialSecondPartial ψ j j z := by
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [mul_sub, Finset.mul_sum, mul_neg]
  have hright :
      (∑ x, ∑ j, ∫ z, if x = i then
        localizedDivergenceH φ u p j z x * spatialPartial ψ j z else 0) =
        ∑ j, ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hterm (x : Fin 3) :
        (∫ z, if x = i then
          localizedDivergenceH φ u p j z x * spatialPartial ψ j z else 0) =
          if x = i then
            ∫ z, localizedDivergenceH φ u p j z i * spatialPartial ψ j z
          else 0 := by
      by_cases hxi : x = i
      · subst x
        simp
      · simp [hxi]
    simp_rw [hterm]
    simp
  rw [hright] at h
  exact hleft.trans h

private lemma localized_divergence_source_data_hGSupport_1 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ},
      (∀ {V : Type} [Zero V] (v : ParabolicPoint → V),
          (∀ (z : ParabolicPoint),
              ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                v z = (0 : V)) →
            HasCompactSupport v) →
        (∀ (z : ParabolicPoint),
            ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
              φ z = (0 : ℝ)) →
          (∀ (z : ParabolicPoint),
              ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                timePartial φ z = (0 : ℝ)) →
            (∀ (j : Fin (3 : ℕ)) (z : ParabolicPoint),
                ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                  spatialPartial φ j z = (0 : ℝ)) →
              ∀ (i : Fin (3 : ℕ)),
                HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) =>
                  localizedDivergenceG φ u Du p f z i
    := by
  intro u Du p f φ hsupport_of_phi hφzero htszero hspzero i
  apply hsupport_of_phi
  intro z hz
  dsimp [localizedDivergenceG]
  rw [hφzero z hz, htszero z hz]
  have hsum1 : (∑ j, u z i * u z j * spatialPartial φ j z) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hspzero j z hz]
    simp
  have hsum2 : (∑ j, Du z i j * spatialPartial φ j z) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hspzero j z hz]
    simp
  rw [hsum1, hsum2, hspzero i z hz]
  simp

lemma localized_divergence_source_data_hK_2 :
    ∀ {v g : ParabolicPoint → Vec3} {h : Fin (3 : ℕ) → ParabolicPoint → Vec3},
      (∀ (i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) => g z i) →
        (∀ (j i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) => h j z i) →
          (∀ (i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) => v z i) →
            let K : Set ParabolicPoint :=
              ((⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => v z i) ∪
                  ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => g z i) ∪
                ⋃ (j : Fin (3 : ℕ)),
                  ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => h j z i;
            IsCompact K
    := by
  intro v g h hg hh hvi K
  dsimp [K]
  have hV : IsCompact (⋃ i : Fin 3, tsupport (fun z => v z i)) :=
    isCompact_iUnion (fun i : Fin 3 => (hvi i).isCompact)
  have hG : IsCompact (⋃ i : Fin 3, tsupport (fun z => g z i)) :=
    isCompact_iUnion (fun i : Fin 3 => (hg i).isCompact)
  have hH : IsCompact (⋃ j : Fin 3, ⋃ i : Fin 3,
      tsupport (fun z => h j z i)) :=
    isCompact_iUnion (fun j : Fin 3 =>
      isCompact_iUnion (fun i : Fin 3 => (hh j i).isCompact))
  exact hV.union hG |>.union hH

lemma localized_divergence_source_data_hKsupport_3 :
    ∀ {v g : ParabolicPoint → Vec3} {h : Fin (3 : ℕ) → ParabolicPoint → Vec3},
      let K : Set ParabolicPoint :=
        ((⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => v z i) ∪
            ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => g z i) ∪
          ⋃ (j : Fin (3 : ℕ)),
            ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => h j z i;
      ∀ (hKx : IsCompact (X := ℝ) ((fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K))
        (hKt : IsCompact (X := ℝ) ((fun (z : ParabolicPoint) => z.2) '' K)),
        let C : ℝ :=
          Classical.choose (p :=
            Membership.mem (γ := Set ℝ)
              (upperBounds ((fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K)))
            (IsCompact.bddAbove (s := (fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K)
              hKx);
        (∀ (x : ℝ),
            Membership.mem (γ := Set ℝ) ((fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K)
                x →
              x ≤ C) →
          let a : ℝ :=
            Classical.choose (p :=
              Membership.mem (γ := Set ℝ) (lowerBounds ((fun (z : ParabolicPoint) => z.2) '' K)))
              (IsCompact.bddBelow (s := (fun (z : ParabolicPoint) => z.2) '' K) hKt);
          (∀ (x : ℝ),
              Membership.mem (γ := Set ℝ) ((fun (z : ParabolicPoint) => z.2) '' K) x → a ≤ x) →
            let b : ℝ :=
              Classical.choose (p :=
                Membership.mem (γ := Set ℝ) (upperBounds ((fun (z : ParabolicPoint) => z.2) '' K)))
                (IsCompact.bddAbove (s := (fun (z : ParabolicPoint) => z.2) '' K) hKt);
            (∀ (x : ℝ),
                Membership.mem (γ := Set ℝ) ((fun (z : ParabolicPoint) => z.2) '' K) x → x ≤ b) →
              let r : ℝ := max (C + (1 : ℝ)) (|b - a| + (2 : ℝ));
              let t₀ : ℝ := b + (1 : ℝ);
              b - a + (1 : ℝ) < r ^ (2 : ℕ) →
                ∀ z ∈ K, z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ (2 : ℕ)) t₀
    := by
  intro v g h K hKx hKt C hC a ha b hb r t₀ hrtime z hz
  have hzC : vec3EuclideanNorm z.1 ≤ C :=
    hC (vec3EuclideanNorm z.1) ⟨z, hz, rfl⟩
  have hza : a ≤ z.2 := ha z.2 ⟨z, hz, rfl⟩
  have hzb : z.2 ≤ b := hb z.2 ⟨z, hz, rfl⟩
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hrpos).2
    simpa [r, vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
      CKN.vecDot, pow_two] using
      (hzC.trans_lt (lt_of_lt_of_le
        (by linarith only [(zero_lt_one : (0 : ℝ) < 1)] : C < C + 1)
        (le_max_left _ _)))
  · constructor
    · dsimp [t₀]
      linarith only [hrtime, hza]
    · dsimp [t₀]
      linarith only [hzb]

private lemma localized_divergence_source_data_hφtime_c_1 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => timePartial φ z
    := by
  intro φ hφd hφc
  apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
  intro z hz
  by_contra hnot
  apply hz
  exact timePartial_zero_of_not_mem_tsupport_public hφd hnot

private lemma localized_divergence_source_data_hφtime_ts_2 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => timePartial φ z) ⊆ tsupport φ
    := by
  intro φ hφd
  apply closure_minimal
  · intro z hz
    by_contra hnot
    apply hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hnot
  · exact isClosed_tsupport φ

private lemma localized_divergence_source_data_hφsp_c_3 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
          ∀ (j : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z
    := by
  intro φ hφd hφc j
  apply HasCompactSupport.of_support_subset_isCompact hφc.isCompact
  intro z hz
  by_contra hnot
  apply hz
  exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j

private lemma localized_divergence_source_data_hφsp_ts_4 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) φ →
        ∀ (j : Fin (3 : ℕ)),
          (tsupport (α := ℝ) fun (z : Vec3 × ℝ) => spatialPartial φ j z) ⊆ tsupport φ
    := by
  intro φ hφd j
  apply closure_minimal
  · intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
  · exact isClosed_tsupport φ

private lemma localized_divergence_source_data_hbox_factor_5 :
    ∀ {_ : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ} {Ω' : Set Vec3} {J : Set ℝ},
      tsupport φ ⊆ Ω' ×ˢ J →
        let μ : Measure ParabolicPoint := Measure.restrict volume (spaceTimeSet Ω' J);
        ∀ {a : ParabolicPoint → ℝ},
          Integrable a μ →
            ∀ {α : Vec3 × ℝ → ℝ},
              HasCompactSupport α →
                tsupport α ⊆ tsupport φ →
                  Continuous α →
                    ∀ {b : Vec3 × ℝ → ℝ},
                      Continuous b →
                        @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                          (fun (z : ParabolicPoint) => a z * (α z * b z)) volume
    := by
  intro f φ Ω' J hφbox μ a ha α hαc hαts hα b hb
  have hbc : HasCompactSupport (fun z : Vec3 × ℝ => α z * b z) :=
    hαc.mul_right (f' := b)
  have hbs : tsupport (fun z : Vec3 × ℝ => α z * b z) ⊆
      (spaceTimeSet Ω' J : Set (Vec3 × ℝ)) := by
    exact (tsupport_mul_subset_left (f := α) (g := b)).trans
      (hαts.trans hφbox)
  exact compact_factor_integrable (a := a)
    (b := fun z : Vec3 × ℝ => α z * b z)
    (by simpa [μ] using ha) (hα.mul hb) hbc hbs

private lemma localized_divergence_source_data_hG_6 :
    ∀ {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin (3 : ℕ) → Vec3}
      {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {φ : Vec3 × ℝ → ℝ},
      (∀ (i : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) => u z i * timePartial φ z) volume) →
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) => u z i * u z j * spatialPartial φ j z) volume) →
          (∀ (i j : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) => Du z i j * spatialPartial φ j z) volume) →
            (∀ (i : Fin (3 : ℕ)),
                @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                  (fun (z : ParabolicPoint) => p z * spatialPartial φ i z) volume) →
              (∀ (i : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : ParabolicPoint) => f z i * φ z) volume) →
                ∀ (i : Fin (3 : ℕ)),
                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                    (fun (z : ParabolicPoint) => localizedDivergenceG φ u Du p f z i) volume
    := by
  intro u Du p f φ hGtime hGconv hGgrad hGpress hGforce i
  have hsum := (hGtime i).add
    ((integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun j _ => hGconv i j)).sub
      ((integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hGgrad i j)).sub ((hGpress i).add (hGforce i))))
  refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [localizedDivergenceG, Pi.add_apply, Pi.sub_apply]
  ring

private lemma localized_divergence_source_data_hH_7 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ},
      (∀ (i j : Fin (3 : ℕ)),
          @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
            (fun (z : ParabolicPoint) => φ z * u z i * u z j) volume) →
        (∀ (i j : Fin (3 : ℕ)),
            @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
              (fun (z : ParabolicPoint) => u z i * spatialPartial φ j z) volume) →
          (∀ (_ : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) => p z * φ z) volume) →
            ∀ (j i : Fin (3 : ℕ)),
              @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                (fun (z : ParabolicPoint) => localizedDivergenceH φ u p j z i) volume
    := by
  intro u p φ hHconv hHgrad hHpress j i
  by_cases hij : i = j
  · subst j
    have hsum := (hHconv i i).add (hHgrad i i)
    refine (hsum.add (hHpress i)).congr
      (Filter.Eventually.of_forall (fun z => ?_))
    simp [localizedDivergenceH]
  · have hsum := (hHconv i j).add (hHgrad i j)
    refine hsum.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp [localizedDivergenceH, hij]

private lemma localized_divergence_source_data_hsupport_of_phi_8 :
    ∀ {φ : Vec3 × ℝ → ℝ},
      let Kφ : Set ParabolicPoint :=
        (⇑parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) ⁻¹' tsupport φ;
      IsCompact Kφ →
        ∀ {V : Type} [Zero V] (v : ParabolicPoint → V),
          (∀ (z : ParabolicPoint),
              ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                v z = (0 : V)) →
            HasCompactSupport v
    := by
  intro φ Kφ hKφ V localHypothesis4 v hzv
  apply HasCompactSupport.of_support_subset_isCompact hKφ
  intro z hz
  by_contra hnot
  apply hz
  apply hzv z
  simpa only [Kφ, Set.mem_preimage, parabolicHomeomorph_apply] using hnot

private lemma localized_divergence_source_data_hHSupport_9 :
    ∀ {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {φ : Vec3 × ℝ → ℝ},
      (∀ {V : Type} [Zero V] (v : ParabolicPoint → V),
          (∀ (z : ParabolicPoint),
              ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                v z = (0 : V)) →
            HasCompactSupport v) →
        (∀ (z : ParabolicPoint),
            ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
              φ z = (0 : ℝ)) →
          (∀ (j : Fin (3 : ℕ)) (z : ParabolicPoint),
              ((parabolicHomeomorph : ParabolicPoint → Vec3 × ℝ) z : Vec3 × ℝ) ∉ tsupport φ →
                spatialPartial φ j z = (0 : ℝ)) →
            ∀ (j i : Fin (3 : ℕ)),
              HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) =>
                localizedDivergenceH φ u p j z i
    := by
  intro u p φ hsupport_of_phi hφzero hspzero j i
  apply hsupport_of_phi
  intro z hz
  dsimp [localizedDivergenceH]
  rw [hφzero z hz, hspzero j z hz]
  simp

lemma localized_divergence_source_data_hvi_10 :
    ∀ {v : ParabolicPoint → Vec3},
      HasCompactSupport v →
        ∀ (i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) fun (z : ParabolicPoint) => v z i
    := by
  intro v hv i
  apply HasCompactSupport.of_support_subset_isCompact hv.isCompact
  intro z hz
  by_contra hnot
  apply hz
  have hvzero : v z = 0 := image_eq_zero_of_notMem_tsupport hnot
  exact congrFun hvzero i

lemma localized_divergence_source_data_hrtime_11 :
    ∀ {v g : ParabolicPoint → Vec3} {h : Fin (3 : ℕ) → ParabolicPoint → Vec3},
      let K : Set ParabolicPoint :=
        ((⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => v z i) ∪
            ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => g z i) ∪
          ⋃ (j : Fin (3 : ℕ)),
            ⋃ (i : Fin (3 : ℕ)), tsupport (α := ℝ) fun (z : ParabolicPoint) => h j z i;
      ∀ (hKx : IsCompact (X := ℝ) ((fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K))
        (hKt : IsCompact (X := ℝ) ((fun (z : ParabolicPoint) => z.2) '' K)),
        let C : ℝ :=
          Classical.choose (p :=
            Membership.mem (γ := Set ℝ)
              (upperBounds ((fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K)))
            (IsCompact.bddAbove (s := (fun (z : ParabolicPoint) => vec3EuclideanNorm z.1) '' K)
              hKx);
        let a : ℝ :=
          Classical.choose (p :=
            Membership.mem (γ := Set ℝ) (lowerBounds ((fun (z : ParabolicPoint) => z.2) '' K)))
            (IsCompact.bddBelow (s := (fun (z : ParabolicPoint) => z.2) '' K) hKt);
        let b : ℝ :=
          Classical.choose (p :=
            Membership.mem (γ := Set ℝ) (upperBounds ((fun (z : ParabolicPoint) => z.2) '' K)))
            (IsCompact.bddAbove (s := (fun (z : ParabolicPoint) => z.2) '' K) hKt);
        let r : ℝ := max (C + (1 : ℝ)) (|b - a| + (2 : ℝ));
        b - a + (1 : ℝ) < r ^ (2 : ℕ)
    := by
  intro v g h K hKx hKt C a b r
  have habs : b - a ≤ |b - a| := le_abs_self _
  have hrbig : |b - a| + 2 ≤ r := le_max_right _ _
  have hrone : 1 < r := by
    have : 0 ≤ |b - a| := abs_nonneg _
    linarith only [this, hrbig]
  nlinarith only [habs, hrbig, hrone, sq_nonneg (r - 1)]

theorem localized_divergence_source_data_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J) :
    (∀ i : Fin 3, Integrable (fun z =>
      localizedVelocity (show ParabolicPoint → ℝ from φ) u z i) volume) ∧
    (∀ i : Fin 3, Integrable
      (fun z => localizedDivergenceG φ u Du p f z i) volume) ∧
    (∀ j i : Fin 3, Integrable
      (fun z => localizedDivergenceH φ u p j z i) volume) ∧
    HasCompactSupport (localizedVelocity (show ParabolicPoint → ℝ from φ) u) ∧
    (∀ i : Fin 3, HasCompactSupport
      (fun z => localizedDivergenceG φ u Du p f z i)) ∧
    (∀ j i : Fin 3, HasCompactSupport
      (fun z => localizedDivergenceH φ u p j z i)) := by
  rcases hsol with ⟨hΩ, hI, hIord, hq, hfSol, hdata, hS2, hS3, hS4⟩
  rcases hφ with ⟨hφd, hφc, hφΩ⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have : IsFiniteMeasure μ := local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  obtain ⟨hu, hDu, hpmeas, hfmeas, hEssSup, henergy, hp, hf, hgrad⟩ :=
    hdata Ω' J hbox
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [ENNReal.one_le_ofReal]
    linarith only [hq]
  have huComp (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hDuComp (i j : Fin 3) : MemLp (fun z => Du z i j) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
  have hpInt : Integrable p μ := hp.integrable (by norm_num)
  have hfComp (i : Fin 3) : MemLp (fun z => f z i) (ENNReal.ofReal q) μ :=
    hf.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have hφtime : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => timePartial φ z) := timePartial_contDiff_full hφd
  have hφtime_c := @localized_divergence_source_data_hφtime_c_1 φ hφd hφc
  have hφtime_ts := @localized_divergence_source_data_hφtime_ts_2 φ hφd
  have hφsp (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial φ j z) :=
    spatialPartial_contDiff hφd j
  have hφsp_c (j : Fin 3) := @localized_divergence_source_data_hφsp_c_3 φ hφd hφc j
  have hφsp_ts (j : Fin 3) := @localized_divergence_source_data_hφsp_ts_4 φ hφd j
  have hbox_factor {a : ParabolicPoint → ℝ}
      (ha : Integrable a μ) {α : Vec3 × ℝ → ℝ}
      (hαc : HasCompactSupport α) (hαts : tsupport α ⊆ tsupport φ)
      (hα : Continuous α) {b : Vec3 × ℝ → ℝ} (hb : Continuous b) :=
        @localized_divergence_source_data_hbox_factor_5 f φ Ω' J hφbox a ha α hαc hαts hα b hb
  have hUi (i : Fin 3) : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij (i j : Fin 3) : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hUU (i j : Fin 3) : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hGtime (i : Fin 3) : Integrable
      (fun z => u z i * timePartial φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) hφtime_c hφtime_ts hφtime.continuous continuous_const
    simpa using h
  have hV (i : Fin 3) : Integrable (fun z =>
      localizedVelocity (show ParabolicPoint → ℝ from φ) u z i) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa [localizedVelocity, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h
  have hGconv (i j : Fin 3) : Integrable
      (fun z => u z i * u z j * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUU i j) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hGgrad (i j : Fin 3) : Integrable
      (fun z => Du z i j * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hDij i j) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hGpress (i : Fin 3) : Integrable
      (fun z => p z * spatialPartial φ i z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      hpInt (hφsp_c i) (hφsp_ts i) (hφsp i).continuous continuous_const
    simpa using h
  have hGforce (i : Fin 3) : Integrable
      (fun z => f z i * φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      ((hfComp i).integrable hq1) hφc (by exact subset_rfl)
      hφd.continuous continuous_const
    simpa using h
  have hG (i : Fin 3) := @localized_divergence_source_data_hG_6 u Du p f φ hGtime hGconv hGgrad
    hGpress hGforce i
  have hHconv (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => φ z * u z i * u z j) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUU i j) hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hHgrad (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => u z i * spatialPartial φ j z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      (hUi i) (hφsp_c j) (hφsp_ts j) (hφsp j).continuous continuous_const
    simpa using h
  have hHpress (i : Fin 3) : Integrable
      (fun z : ParabolicPoint => p z * φ z) volume := by
    have h := hbox_factor (b := fun _ : Vec3 × ℝ => (1 : ℝ))
      hpInt hφc (by exact subset_rfl) hφd.continuous continuous_const
    simpa using h
  have hH (j i : Fin 3) := @localized_divergence_source_data_hH_7 u p φ hHconv hHgrad hHpress j i
  let Kφ : Set ParabolicPoint := parabolicHomeomorph ⁻¹' tsupport φ
  have hKφ : IsCompact Kφ := parabolicHomeomorph.isCompact_preimage.2 hφc.isCompact
  have hsupport_of_phi {V : Type} [Zero V] (v : ParabolicPoint → V)
      (hzv : ∀ z, parabolicHomeomorph z ∉ tsupport φ → v z = 0) :=
        @localized_divergence_source_data_hsupport_of_phi_8 φ hKφ V (by infer_instance) v hzv
  have hφzero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    change φ (z.1, z.2) = 0
    exact image_eq_zero_of_notMem_tsupport hz'
  have htszero (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : timePartial φ z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact timePartial_zero_of_not_mem_tsupport_public hφd hz'
  have hspzero (j : Fin 3) (z : ParabolicPoint)
      (hz : parabolicHomeomorph z ∉ tsupport φ) : spatialPartial φ j z = 0 := by
    have hz' : (z.1, z.2) ∉ tsupport φ := by
      simpa [parabolicHomeomorph_apply] using hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hz' j
  have hvSupport : HasCompactSupport
      (localizedVelocity (show ParabolicPoint → ℝ from φ) u) := by
    apply hsupport_of_phi
    intro z hz
    funext i
    simp [localizedVelocity, hφzero z hz]
  have hGSupport (i : Fin 3) := @localized_divergence_source_data_hGSupport_1 u Du p f φ
    hsupport_of_phi hφzero htszero hspzero i
  have hHSupport (j i : Fin 3) := @localized_divergence_source_data_hHSupport_9 u p φ
    hsupport_of_phi hφzero hspzero j i
  exact ⟨hV, hG, hH, hvSupport, hGSupport, hHSupport⟩

/-- Construct common Duhamel support data from compact support of velocity and every source
component. -/
noncomputable def duhamelSupportDataOfCompactSupport
    {v g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : HasCompactSupport v)
    (hg : ∀ i : Fin 3, HasCompactSupport (fun z => g z i))
    (hh : ∀ j i : Fin 3, HasCompactSupport (fun z => h j z i)) :
    DuhamelSupportData v g h := by
  have hvi (i : Fin 3) := @localized_divergence_source_data_hvi_10 v hv i
  let K : Set ParabolicPoint :=
    (⋃ i : Fin 3, tsupport (fun z => v z i)) ∪
      (⋃ i : Fin 3, tsupport (fun z => g z i)) ∪
      (⋃ j : Fin 3, ⋃ i : Fin 3, tsupport (fun z => h j z i))
  have hK := @localized_divergence_source_data_hK_2 v g h hg hh hvi
  have hKx : IsCompact (K.image (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1)) := by
    have hnorm : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hK.image (hnorm.comp continuous_fst_parabolicPoint)
  have hKt : IsCompact (K.image (fun z : ParabolicPoint => z.2)) :=
    hK.image continuous_snd_parabolicPoint
  let C : ℝ := Classical.choose hKx.bddAbove
  have hC : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint =>
      vec3EuclideanNorm z.1) → x ≤ C := Classical.choose_spec hKx.bddAbove
  let a : ℝ := Classical.choose hKt.bddBelow
  have ha : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint => z.2) → a ≤ x :=
    Classical.choose_spec hKt.bddBelow
  let b : ℝ := Classical.choose hKt.bddAbove
  have hb : ∀ x : ℝ, x ∈ K.image (fun z : ParabolicPoint => z.2) → x ≤ b :=
    Classical.choose_spec hKt.bddAbove
  let r : ℝ := max (C + 1) (|b - a| + 2)
  let R : ℝ := r + 1
  let t₀ : ℝ := b + 1
  have hr : 0 ≤ r := by
    dsimp [r]
    exact le_max_of_le_right (by positivity)
  have hrR : r < R := by
    dsimp [R]
    linarith only
  have hrtime := @localized_divergence_source_data_hrtime_11 v g h hKx hKt
  have hKsupport := @localized_divergence_source_data_hKsupport_3 v g h hKx hKt hC ha hb hrtime
  refine ⟨r, R, t₀, hr, hrR, ?_, ?_, ?_⟩
  · intro i z hz
    exact hKsupport z (Or.inl (Or.inl (mem_iUnion.2 ⟨i, hz⟩)))
  · intro i z hz
    exact hKsupport z (Or.inl (Or.inr (mem_iUnion.2 ⟨i, hz⟩)))
  · intro j i z hz
    exact hKsupport z (Or.inr (mem_iUnion.2 ⟨j,
      mem_iUnion.2 ⟨i, hz⟩⟩))

/-- Product-coordinate presentation of the parabolic point space used in weak-equation transport.
-/
def parabolicHomeomorphReal' : ParabolicPoint ≃ₜ Vec3 × ℝ :=
  parabolicHomeomorph

end CKN.Core.Step3
