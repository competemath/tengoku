import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Preliminaries for Sard's theorem (Wave 3S)

Infrastructure for the proof of Sard's theorem, following Milnor
("Topology from the differentiable viewpoint", §3).

We work in the concrete spaces `Fin n → ℝ` (with the sup norm, so that closed
balls are cubes and subdivide nicely) and transfer to `EuclideanSpace` at the
very end.

Main contents:

* `Submission.image_null_of_locally_image_null` — a Lindelöf-type argument:
  if every point of `S` has a neighbourhood `V` with `μ (f '' (S ∩ V)) = 0`,
  then `μ (f '' S) = 0`;
* `Submission.exists_apply_single_ne_zero` — a continuous linear map that is
  nonzero somewhere is nonzero on a standard basis vector;
* `Submission.isOpen_setOf_surjective` / `isClosed_setOf_not_surjective` —
  surjectivity of continuous linear maps into `Fin q → ℝ` is an open condition;
* `Submission.splitCLE` — the continuous linear equivalence
  `(Fin (n+1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ)` splitting off coordinate `i`,
  together with `Submission.measurePreserving_splitCLE`;
* `Submission.critSet`, `Submission.vanishSet` — the critical set and the sets
  `C_i` of Milnor's proof, with basic compactness lemmas;
* `Submission.exists_chart` — the local chart `y ↦ update y s (σ y)` given by
  the inverse function theorem, with a smooth local inverse.
-/

namespace Submission

noncomputable section

open Function MeasureTheory Metric Set Filter
open scoped ContDiff Topology

/-! ## Smoothness index bookkeeping -/

theorem one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

theorem infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem add_one_le_infty (m : ℕ) : (m : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact_mod_cast le_top

/-! ## Local-to-global null images -/

/-- If every point of `S` has a neighbourhood `V` such that `f '' (S ∩ V)` is
`μ`-null, then `f '' S` is `μ`-null.  (Lindelöf argument.)-/
theorem image_null_of_locally_image_null
    {α β : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace β] {μ : Measure β} {f : α → β} {S : Set α}
    (h : ∀ x ∈ S, ∃ V ∈ 𝓝 x, μ (f '' (S ∩ V)) = 0) :
    μ (f '' S) = 0 := by
  choose! V hV hnull using h
  obtain ⟨t, hts, htc, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (f := V) (s := S) fun x hx => nhdsWithin_le_nhds (hV x hx)
  have hsub : f '' S ⊆ ⋃ x ∈ t, f '' (S ∩ V x) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hxt, hyV⟩ := mem_iUnion₂.1 (hcover hy)
    exact mem_iUnion₂.2 ⟨x, hxt, ⟨y, ⟨hy, hyV⟩, rfl⟩⟩
  refine measure_mono_null hsub ?_
  exact (measure_biUnion_null_iff htc).2 fun x hx => hnull x (hts hx)

/-! ## Standard basis vectors -/

theorem sum_smul_single {d : ℕ} (c : Fin d → ℝ) :
    ∑ j, c j • Pi.single j (1 : ℝ) = c := by
  have h : ∀ j : Fin d, c j • Pi.single j (1 : ℝ) = Pi.single j (c j) := by
    intro j
    funext i
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]
  simp only [h]
  exact Finset.univ_sum_single c

/-- A continuous linear map on `Fin d → ℝ` that is nonzero at some vector is
nonzero at some standard basis vector.-/
theorem exists_apply_single_ne_zero {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ξ : (Fin d → ℝ) →L[ℝ] F} {v : Fin d → ℝ} (hv : ξ v ≠ 0) :
    ∃ s : Fin d, ξ (Pi.single s 1) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  apply hv
  have hv' : v = ∑ j, v j • Pi.single j (1 : ℝ) := (sum_smul_single v).symm
  rw [hv', map_sum]
  simp [hall]

/-! ## Surjectivity is an open condition -/

/-- The set of surjective continuous linear maps into `Fin q → ℝ` is open.-/
theorem isOpen_setOf_surjective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℕ} :
    IsOpen {L : E →L[ℝ] (Fin q → ℝ) | Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  choose v hv using fun j : Fin q => hL₀ (Pi.single j 1)
  set V : (Fin q → ℝ) →L[ℝ] E :=
    ∑ j, (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ).smulRight (v j) with hV
  have hVc : ∀ c : Fin q → ℝ, V c = ∑ j, c j • v j := by
    intro c
    simp [hV]
  have hL₀V : L₀.comp V = ContinuousLinearMap.id ℝ (Fin q → ℝ) := by
    ext c : 1
    rw [ContinuousLinearMap.comp_apply, hVc, map_sum, ContinuousLinearMap.id_apply]
    simp only [map_smul, hv]
    exact sum_smul_single c
  have hcont : Continuous fun L : E →L[ℝ] (Fin q → ℝ) => L.comp V :=
    continuous_id.clm_comp continuous_const
  have hmem : {L : E →L[ℝ] (Fin q → ℝ) | IsUnit (L.comp V)} ∈ 𝓝 L₀ := by
    refine (Units.isOpen.preimage hcont).mem_nhds ?_
    show IsUnit (L₀.comp V)
    rw [hL₀V]
    exact isUnit_one
  refine mem_of_superset hmem ?_
  intro L hL
  obtain ⟨u, hu⟩ := hL
  have hsurj : Surjective (L.comp V) := by
    intro y
    refine ⟨(↑u⁻¹ : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) y, ?_⟩
    have h1 : (L.comp V) ((↑u⁻¹ : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)) y)
        = ((L.comp V) * ↑u⁻¹) y := rfl
    rw [h1, ← hu, u.mul_inv]
    rfl
  have hco : ⇑(L.comp V) = ⇑L ∘ ⇑V := rfl
  rw [hco] at hsurj
  exact hsurj.of_comp

theorem isClosed_setOf_not_surjective {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℕ} :
    IsClosed {L : E →L[ℝ] (Fin q → ℝ) | ¬Surjective L} := by
  have h := (isOpen_setOf_surjective (E := E) (q := q)).isClosed_compl
  simpa [compl_ofPred] using h

/-- The zero map is not surjective onto a nontrivial space.-/
theorem not_surjective_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Nontrivial F] :
    ¬Surjective ((0 : E →L[ℝ] F) : E → F) := by
  intro hsurj
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  obtain ⟨x, hx⟩ := hsurj y
  exact hy (by simpa using hx.symm)

/-- Surjectivity of a continuous linear map into `Fin 1 → ℝ` is equivalent to
being nonzero.-/
theorem surjective_iff_ne_zero_fin_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] (Fin 1 → ℝ)) :
    Surjective L ↔ L ≠ 0 := by
  constructor
  · rintro hsurj rfl
    exact not_surjective_zero hsurj
  · intro hL y
    have hex : ∃ x, L x ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hL (ContinuousLinearMap.ext fun x => hall x)
    obtain ⟨x, hx⟩ := hex
    have hx0 : L x 0 ≠ 0 := by
      intro h0
      apply hx
      funext j
      rw [Fin.eq_zero j]
      exact h0
    refine ⟨(y 0 / L x 0) • x, ?_⟩
    funext j
    rw [Fin.eq_zero j]
    simp [div_mul_cancel₀ _ hx0]

/-! ## Splitting off a coordinate -/

variable {n : ℕ}

/-- Splitting off the `i`-th coordinate, as a linear equivalence.-/
def splitLinearEquiv (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin n → ℝ) where
  toFun x := (x i, Fin.removeNth i x)
  invFun p := Fin.insertNth i p.1 p.2
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := Fin.insertNth_self_removeNth i x
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- Splitting off the `i`-th coordinate, as a continuous linear equivalence.-/
def splitCLE (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
  (splitLinearEquiv n i).toContinuousLinearEquiv

@[simp] theorem splitCLE_apply (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    splitCLE n i x = (x i, Fin.removeNth i x) := rfl

@[simp] theorem splitCLE_symm_apply (i : Fin (n + 1)) (p : ℝ × (Fin n → ℝ)) :
    (splitCLE n i).symm p = Fin.insertNth i p.1 p.2 := rfl

theorem measurePreserving_splitCLE (i : Fin (n + 1)) :
    MeasurePreserving (splitCLE n i) volume volume := by
  have h := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hcoe : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
      = ⇑(splitCLE n i) := rfl
  rwa [hcoe] at h

/-- If the image of `A` under the coordinate-splitting map is contained in a
null set, then `A` is null.-/
theorem splitCLE_image_null (i : Fin (n + 1)) {A : Set (Fin (n + 1) → ℝ)}
    {B : Set (ℝ × (Fin n → ℝ))} (hAB : splitCLE n i '' A ⊆ B)
    (hB : volume B = 0) : volume A = 0 := by
  have h1 : A ⊆ splitCLE n i ⁻¹' B := fun x hx => hAB ⟨x, hx, rfl⟩
  refine measure_mono_null h1 ?_
  exact (measurePreserving_splitCLE i).quasiMeasurePreserving.preimage_null hB

/-! ## Singletons are null -/

theorem volume_singleton_pi {q : ℕ} (y : Fin (q + 1) → ℝ) :
    volume ({y} : Set (Fin (q + 1) → ℝ)) = 0 := by
  have h1 : ({y} : Set (Fin (q + 1) → ℝ)) = Set.pi univ fun i => {y i} :=
    (Set.univ_pi_singleton y).symm
  rw [h1, volume_pi_pi]
  simp

/-! ## The critical set and the sets `C_i` -/

variable {p q : ℕ}

/-- The critical set of `f` on `U`: points where the differential is not
surjective.-/
def critSet (U : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → Fin q → ℝ) :
    Set (Fin p → ℝ) :=
  {x ∈ U | ¬Surjective (fderiv ℝ f x)}

/-- Milnor's set `C_i`: points of `U` where all iterated derivatives of order
between `1` and `i` vanish.-/
def vanishSet (U : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → Fin q → ℝ) (i : ℕ) :
    Set (Fin p → ℝ) :=
  {x ∈ U | ∀ j, 1 ≤ j → j ≤ i → iteratedFDeriv ℝ j f x = 0}

theorem critSet_subset (U : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → Fin q → ℝ) :
    critSet U f ⊆ U := fun _ hx => hx.1

theorem vanishSet_subset (U : Set (Fin p → ℝ)) (f : (Fin p → ℝ) → Fin q → ℝ)
    (i : ℕ) : vanishSet U f i ⊆ U := fun _ hx => hx.1

theorem vanishSet_antitone {U : Set (Fin p → ℝ)} {f : (Fin p → ℝ) → Fin q → ℝ}
    {i j : ℕ} (hij : i ≤ j) : vanishSet U f j ⊆ vanishSet U f i :=
  fun _ hx => ⟨hx.1, fun k hk1 hki => hx.2 k hk1 (hki.trans hij)⟩

theorem fderiv_eq_zero_of_mem_vanishSet {U : Set (Fin p → ℝ)}
    {f : (Fin p → ℝ) → Fin q → ℝ} {i : ℕ} (hi : 1 ≤ i) {x : Fin p → ℝ}
    (hx : x ∈ vanishSet U f i) : fderiv ℝ f x = 0 := by
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := hx.2 1 le_rfl hi
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 : fderiv ℝ f x v = iteratedFDeriv ℝ 1 f x (fun _ => v) := by
    rw [iteratedFDeriv_one_apply]
  rw [h2, h1]
  simp

/-- On a nontrivial target, the sets `C_i` (for `i ≥ 1`) consist of critical
points.-/
theorem vanishSet_subset_critSet {U : Set (Fin p → ℝ)}
    {f : (Fin p → ℝ) → Fin (q + 1) → ℝ} {i : ℕ} (hi : 1 ≤ i) :
    vanishSet U f i ⊆ critSet U f := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rw [fderiv_eq_zero_of_mem_vanishSet hi hx]
  exact not_surjective_zero

/-- The intersection of the critical set with a compact subset of `U` is
compact.-/
theorem isCompact_critSet_inter {U : Set (Fin p → ℝ)}
    {f : (Fin p → ℝ) → Fin q → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {K : Set (Fin p → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (critSet U f ∩ K) := by
  have hfd : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU one_le_infty
  have heq : critSet U f ∩ K
      = K ∩ fderiv ℝ f ⁻¹' {L | ¬Surjective L} := by
    ext x
    constructor
    · rintro ⟨⟨_, hxc⟩, hxK⟩
      exact ⟨hxK, hxc⟩
    · rintro ⟨hxK, hxc⟩
      exact ⟨⟨hKU hxK, hxc⟩, hxK⟩
  rw [heq]
  have hcl : IsClosed (K ∩ fderiv ℝ f ⁻¹' {L | ¬Surjective L}) :=
    (hfd.mono hKU).preimage_isClosed_of_isClosed hK.isClosed
      isClosed_setOf_not_surjective
  exact hK.of_isClosed_subset hcl inter_subset_left

/-! ## `Function.update` as an affine perturbation -/

theorem update_eq_add_smul_single {m : ℕ} (y : Fin m → ℝ) (s : Fin m) (a : ℝ) :
    Function.update y s a = y + (a - y s) • Pi.single s 1 := by
  funext j
  rcases eq_or_ne j s with rfl | hj
  · simp
  · simp [hj]

/-- Injectivity computation for the derivative of the chart map.-/
theorem chart_deriv_inj {D : (Fin (n + 1) → ℝ) →L[ℝ] ℝ} {s : Fin (n + 1)}
    (hd : D (Pi.single s 1) ≠ 0) (ξ : Fin (n + 1) → ℝ)
    (hξ : ξ + (D ξ - ξ s) • Pi.single s 1 = 0) : ξ = 0 := by
  have happ : ∀ j, ξ j + (D ξ - ξ s) * (Pi.single s 1 : Fin (n + 1) → ℝ) j = 0 := by
    intro j
    have h := congrFun hξ j
    simpa using h
  have hne : ∀ j, j ≠ s → ξ j = 0 := by
    intro j hj
    have h := happ j
    rw [Pi.single_eq_of_ne hj] at h
    simpa using h
  have hDs : D ξ = 0 := by
    have h := happ s
    rw [Pi.single_eq_same] at h
    linarith
  have hξs : ξ = ξ s • Pi.single s 1 := by
    funext j
    rcases eq_or_ne j s with rfl | hj
    · simp
    · simp [hne j hj, Pi.single_eq_of_ne hj]
  have hmul : ξ s * D (Pi.single s 1) = 0 := by
    conv_lhs => rw [← smul_eq_mul, ← map_smul, ← hξs]
    exact hDs
  have hξs0 : ξ s = 0 := by
    rcases mul_eq_zero.1 hmul with h | h
    · exact h
    · exact absurd h hd
  rw [hξs, hξs0, zero_smul]

/-! ## The chart lemma -/

/-- **Chart lemma.**  Let `σ` be a smooth scalar function on an open set `U`
with `∂σ/∂x_s (x₀) ≠ 0`.  Then the map `h : y ↦ update y s (σ y)` is a
diffeomorphism from a neighbourhood `V ⊆ U` of `x₀` onto an open set `W`,
with a smooth inverse `h'`.-/
theorem exists_chart {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    {σ : (Fin (n + 1) → ℝ) → ℝ} (hσ : ContDiffOn ℝ ∞ σ U)
    {x₀ : Fin (n + 1) → ℝ} (hx₀ : x₀ ∈ U) {s : Fin (n + 1)}
    (hd : fderiv ℝ σ x₀ (Pi.single s 1) ≠ 0) :
    ∃ (V W : Set (Fin (n + 1) → ℝ)) (h' : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ),
      IsOpen V ∧ IsOpen W ∧ x₀ ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ h' W ∧
      (∀ y ∈ V, Function.update y s (σ y) ∈ W) ∧
      (∀ y ∈ V, h' (Function.update y s (σ y)) = y) ∧
      (∀ w ∈ W, h' w ∈ V) ∧
      (∀ w ∈ W, Function.update (h' w) s (σ (h' w)) = w) := by
  classical
  set h : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun y => y + (σ y - y s) • Pi.single s 1 with hhdef
  have hhupd : ∀ y, h y = Function.update y s (σ y) := by
    intro y
    rw [hhdef]
    exact (update_eq_add_smul_single y s (σ y)).symm
  -- smoothness of `h` on `U`
  have hproj : ContDiff ℝ ∞ fun y : Fin (n + 1) → ℝ => y s :=
    (ContinuousLinearMap.proj s :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff
  have hsm : ContDiffOn ℝ ∞ h U :=
    contDiffOn_id.add ((hσ.sub hproj.contDiffOn).smul contDiffOn_const)
  -- the derivative of `h` at `x₀`
  have hσdiff : DifferentiableAt ℝ σ x₀ :=
    (hσ.contDiffAt (hU.mem_nhds hx₀)).differentiableAt infty_ne_zero
  set D : (Fin (n + 1) → ℝ) →L[ℝ] ℝ := fderiv ℝ σ x₀ with hDdef
  set L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ)
      + (D - (ContinuousLinearMap.proj s :
          (Fin (n + 1) → ℝ) →L[ℝ] ℝ)).smulRight (Pi.single s 1) with hLdef
  have hLapply : ∀ ζ, L ζ = ζ + (D ζ - ζ s) • Pi.single s 1 := by
    intro ζ
    simp [hLdef]
  have hhL : HasFDerivAt h L x₀ := by
    rw [hhdef, hLdef]
    exact (hasFDerivAt_id x₀).add
      ((hσdiff.hasFDerivAt.sub
        ((ContinuousLinearMap.proj s :
          (Fin (n + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt)).smul_const (Pi.single s 1))
  -- `L` is bijective
  have hLinj : Function.Injective L := by
    intro ζ η hζη
    have hker : L (ζ - η) = 0 := by rw [map_sub, hζη, sub_self]
    rw [hLapply] at hker
    exact sub_eq_zero.1 (chart_deriv_inj hd (ζ - η) hker)
  have hLsurj : Function.Surjective L := by
    have h1 := (LinearMap.injective_iff_surjective
      (f := (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)))).1
    exact h1 hLinj
  set L' := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.2 hLinj) (LinearMap.range_eq_top.2 hLsurj) with hL'def
  have hL'coe : (L' : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) = L := rfl
  -- inverse function theorem
  have hcda : ContDiffAt ℝ ∞ h x₀ := hsm.contDiffAt (hU.mem_nhds hx₀)
  have hhL' : HasFDerivAt h
      ((L' : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) :
        (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) x₀ := by
    rw [hL'coe]
    exact hhL
  set Φ := hcda.toOpenPartialHomeomorph h hhL' infty_ne_zero with hΦdef
  have hΦcoe : ⇑Φ = h := hcda.toOpenPartialHomeomorph_coe hhL' infty_ne_zero
  have hx₀Φ : x₀ ∈ Φ.source :=
    hcda.mem_toOpenPartialHomeomorph_source hhL' infty_ne_zero
  -- the set of points where the derivative of `h` is invertible
  have hfd : ContinuousOn (fderiv ℝ h) U :=
    hsm.continuousOn_fderiv_of_isOpen hU one_le_infty
  have hV₁open : IsOpen (U ∩ fderiv ℝ h ⁻¹'
      {T : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) | IsUnit T}) :=
    hfd.isOpen_inter_preimage hU Units.isOpen
  have hLunit : IsUnit L := ⟨(ContinuousLinearEquiv.unitsEquiv ℝ _).symm L', rfl⟩
  have hx₀V₁ : x₀ ∈ U ∩ fderiv ℝ h ⁻¹'
      {T : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) | IsUnit T} := by
    refine ⟨hx₀, ?_⟩
    show IsUnit (fderiv ℝ h x₀)
    rw [hhL.fderiv]
    exact hLunit
  set V : Set (Fin (n + 1) → ℝ) := Φ.source ∩ (U ∩ fderiv ℝ h ⁻¹'
      {T : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) | IsUnit T}) with hVdef
  have hVopen : IsOpen V := Φ.open_source.inter hV₁open
  have hVU : V ⊆ U := fun y hy => hy.2.1
  have hx₀V : x₀ ∈ V := ⟨hx₀Φ, hx₀V₁⟩
  set W : Set (Fin (n + 1) → ℝ) := Φ.target ∩ Φ.symm ⁻¹' V with hWdef
  have hWopen : IsOpen W :=
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hVopen
  -- smoothness of the inverse on `W`
  have hsymm : ContDiffOn ℝ ∞ Φ.symm W := by
    intro w hw
    have hyV : Φ.symm w ∈ V := hw.2
    have hyU : Φ.symm w ∈ U := hVU hyV
    have hyunit : IsUnit (fderiv ℝ h (Φ.symm w)) := hyV.2.2
    have hTcoe : ((ContinuousLinearEquiv.unitsEquiv ℝ _ hyunit.unit :
        (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
        (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) = fderiv ℝ h (Φ.symm w) :=
      hyunit.unit_spec
    have hdiff : DifferentiableAt ℝ h (Φ.symm w) :=
      (hsm.contDiffAt (hU.mem_nhds hyU)).differentiableAt infty_ne_zero
    have hhT : HasFDerivAt Φ
        (((ContinuousLinearEquiv.unitsEquiv ℝ _ hyunit.unit :
          (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) :
          (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))) (Φ.symm w) := by
      rw [hΦcoe, hTcoe]
      exact hdiff.hasFDerivAt
    have hcdw : ContDiffAt ℝ ∞ Φ (Φ.symm w) := by
      rw [hΦcoe]
      exact hsm.contDiffAt (hU.mem_nhds hyU)
    exact (Φ.contDiffAt_symm hw.1 hhT hcdw).contDiffWithinAt
  refine ⟨V, W, Φ.symm, hVopen, hWopen, hx₀V, hVU, hsymm, ?_, ?_, ?_, ?_⟩
  · -- `h` maps `V` into `W`
    intro y hy
    rw [← hhupd y]
    have h1 : Φ y ∈ Φ.target := Φ.map_source hy.1
    have h2 : Φ.symm (Φ y) = y := Φ.left_inv hy.1
    have h3 : Φ y = h y := congrFun hΦcoe y
    rw [h3] at h1 h2
    exact ⟨h1, by rw [mem_preimage, h2]; exact hy⟩
  · -- left inverse on `V`
    intro y hy
    rw [← hhupd y]
    have h2 : Φ.symm (Φ y) = y := Φ.left_inv hy.1
    have h3 : Φ y = h y := congrFun hΦcoe y
    rwa [h3] at h2
  · -- `Φ.symm` maps `W` into `V`
    intro w hw
    exact hw.2
  · -- right inverse on `W`
    intro w hw
    rw [← hhupd (Φ.symm w)]
    have h1 : Φ (Φ.symm w) = w := Φ.right_inv hw.1
    have h3 : Φ (Φ.symm w) = h (Φ.symm w) := congrFun hΦcoe (Φ.symm w)
    rwa [h3] at h1

end

end Submission
