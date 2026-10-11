import Tengoku.NavierStokesEuler.NavierStokes.HarmonicMeanInteraction

/-!
# Actual harmonic wave-update interactions

The nonlinear terms are finite convolutions of actual differentiated fields.
All-jet classes are lifted and restricted by proved norm-one linear pullbacks
before applying the full cylindrical divergence cancellation.
-/

noncomputable section

namespace NavierStokes.HarmonicWaveInteraction

open Set Filter Function HarmonicCalculus HarmonicFields WeightedClasses WaveInteractionBounds
open HarmonicMeanInteraction
open scoped Topology ContDiff BigOperators ComplexConjugate

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def pullbackStrip (s : StripData D) (L : E →L[ℝ] D) : StripData E where
  domain := L ⁻¹' s.domain
  isOpen_domain := s.isOpen_domain.preimage L.continuous
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  epsilon_le_one := s.epsilon_le_one
  slow := s.slow
  one_le_slow := s.one_le_slow
  delta := fun x => s.delta (L x)
  delta_pos := fun x hx => s.delta_pos (L x) hx
  zeta := fun x => s.zeta (L x)
  zeta_smooth := s.zeta_smooth.comp L.contDiff.contDiffOn (fun _ hx => hx)
  zeta_nonneg := fun x hx => s.zeta_nonneg (L x) hx

theorem norm_jet_comp_linear {f : D → F} {U : Set D} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] D) {x : E} (hx : L x ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * ‖L‖ ^ m := by
  have hpre := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := m) (show (m : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen m hpre hx, iteratedFDerivWithin_of_isOpen m hU hx] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

theorem class_pullback {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → F}
    (hf : MemClass s w α f) (L : E →L[ℝ] D) (hL : ‖L‖ ≤ 1) :
    MemClass (pullbackStrip s L) (fun n x => w n (L x)) α (fun n x => f n (L x)) := by
  refine ⟨fun n x hx => hf.weight_nonneg n (L x) hx,
    fun n => (hf.smooth n).comp L.contDiff.contDiffOn (fun _ hx => hx), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro n x hx j hj
  have hc := norm_jet_comp_linear s.isOpen_domain (hf.smooth n) L hx j
  have hpow : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg L) hL
  exact (hc.trans (mul_le_of_le_one_right (norm_nonneg _) hpow)).trans (hb n (L x) hx j hj)

noncomputable def projection : D × ℝ →L[ℝ] D := ContinuousLinearMap.fst ℝ D ℝ
noncomputable def inclusion : D →L[ℝ] D × ℝ :=
  (ContinuousLinearMap.id ℝ D).prod (0 : D →L[ℝ] ℝ)

theorem projection_norm : ‖projection (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x.1‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using norm_fst_le x

theorem inclusion_norm : ‖inclusion (D := D)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp [inclusion, Prod.norm_def]

noncomputable def productStrip (s : StripData D) : StripData (D × ℝ) := pullbackStrip s projection

theorem class_lift {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D → F}
    (hf : MemClass s w α f) :
    MemClass (productStrip s) (fun n p => w n p.1) α (fun n p => f n p.1) :=
  class_pullback hf projection projection_norm

theorem class_slice {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ} {f : ℕ → D × ℝ → F}
    (hf : MemClass (productStrip s) (fun n p => w n p.1) α f) :
    MemClass s w α (fun n x => f n (x, 0)) := by
  have hh := class_pullback hf inclusion inclusion_norm
  have he : pullbackStrip (productStrip s) (inclusion (D := D)) = s := by
    cases s
    rfl
  rw [he] at hh
  exact hh

noncomputable def liftedGeometry {s : StripData D} {κ : ℝ} (G : Geometry s κ) :
    Geometry (productStrip s) κ where
  radius := fun n p => G.radius n p.1
  radial := fun n p => (G.radial n p.1, 0)
  angular := fun _ _ => (0, 1)
  axial := fun n p => (G.axial n p.1, 0)
  radius_pos := fun n p hp => G.radius_pos n p.1 hp
  radial_class := (class_lift G.radial_class).map inclusion
  axial_class := (class_lift G.axial_class).map inclusion
  inverse_radius_class := class_lift G.inverse_radius_class

noncomputable def fullPhase (b : CorrectionState.HarmonicBlock D) (n : ℕ) (p : D × ℝ) : ℝ :=
  b.phase n p.1 + ((b.angularFrequency n : ℝ) / b.frequency n) * p.2

theorem fullPhase_smooth {s : StripData D} (b : CorrectionState.HarmonicBlock D)
    (hΦ : ∀ n, ContDiffOn ℝ ∞ (b.phase n) s.domain) (n : ℕ) :
    ContDiffOn ℝ ∞ (fullPhase b n) (productStrip s).domain :=
  ((hΦ n).comp contDiffOn_fst (fun _ hx => hx)).add (contDiffOn_const.mul contDiffOn_snd)

noncomputable def amplitude (b : CorrectionState.HarmonicBlock D) (j : ℤ)
    (n : ℕ) (x : D) : ComplexVector := fun i => blockAmplitude b n i j x

noncomputable def singleMode (b : CorrectionState.HarmonicBlock D) (j : ℤ)
    (n : ℕ) (p : D × ℝ) : ComplexVector :=
  HarmonicResidual.vectorField (fun i => AddMonoidAlgebra.single j (fun x => amplitude b j n x i))
    (b.frequency n) (b.phase n) (b.angularFrequency n) p

/-- The primitive divergence condition is imposed on each actual harmonic field. -/
def ModeSolenoidal (s : StripData D) (c : CorrectionState.Context D)
    (b : CorrectionState.HarmonicBlock D) : Prop :=
  ∀ j : ℤ, j ≠ 0 → ∀ n p, p.1 ∈ s.domain →
    cylindricalDivergence (fun q => c.operators.radius q.1)
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
      (singleMode b j n) p = 0

theorem lifted_amplitude_angularIndependent {s : StripData D} {κ α : ℝ} {P : ℕ → D → ℝ}
    (G : Geometry s κ) {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α)
    {j : ℤ} (hj : j ≠ 0) :
    AngularIndependent (liftedGeometry G) (fun n p => amplitude b j n p.1) := by
  intro n i p hp
  rcases p with ⟨x, θ⟩
  have hs := class_lift (blockAmplitude_class hb hj i)
  have hd := ((hs.smooth n).contDiffAt ((productStrip s).isOpen_domain.mem_nhds hp)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun q : D × ℝ => amplitude b j n q.1 i) (x, θ) at hd
  change along HarmonicResidual.angularDirection (fun q => amplitude b j n q.1 i) (x, θ) = 0
  rw [HarmonicResidual.along_angularDirection hd]
  simp

theorem along_fst (V : D → D) {f : D → F} {p : D × ℝ}
    (hf : DifferentiableAt ℝ f p.1) :
    along (HarmonicResidual.liftDirection V) (fun q => f q.1) p = along V f p.1 := by
  have hd := hf.hasFDerivAt.comp p (projection (D := D)).hasFDerivAt
  change HasFDerivAt (fun q : D × ℝ => f q.1) ((fderiv ℝ f p.1).comp projection) p at hd
  simp only [along, hd.fderiv]
  rfl

theorem fullPhase_hasFDerivAt (b : CorrectionState.HarmonicBlock D) (n : ℕ) {p : D × ℝ}
    (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    HasFDerivAt (fullPhase b n)
      ((fderiv ℝ (b.phase n) p.1).comp projection +
        ((b.angularFrequency n : ℝ) / b.frequency n) • ContinuousLinearMap.snd ℝ D ℝ) p := by
  exact (hΦ.hasFDerivAt.comp p (projection (D := D)).hasFDerivAt).add
    ((ContinuousLinearMap.snd ℝ D ℝ).hasFDerivAt.const_mul _)

theorem along_fullPhase_lift (b : CorrectionState.HarmonicBlock D) (n : ℕ) (V : D → D)
    {p : D × ℝ} (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    along (HarmonicResidual.liftDirection V) (fullPhase b n) p = along V (b.phase n) p.1 := by
  simp only [along, (fullPhase_hasFDerivAt b n hΦ).fderiv,
    _root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply]
  change (fderiv ℝ (b.phase n) p.1) (V p.1) + ((b.angularFrequency n : ℝ) / b.frequency n) * 0 = _
  ring

theorem along_fullPhase_angular (b : CorrectionState.HarmonicBlock D) (n : ℕ)
    {p : D × ℝ} (hΦ : DifferentiableAt ℝ (b.phase n) p.1) :
    along HarmonicResidual.angularDirection (fullPhase b n) p =
      (b.angularFrequency n : ℝ) / b.frequency n := by
  simp only [along, (fullPhase_hasFDerivAt b n hΦ).fderiv,
    _root_.add_apply, ContinuousLinearMap.comp_apply, _root_.smul_apply]
  change (fderiv ℝ (b.phase n) p.1) 0 + ((b.angularFrequency n : ℝ) / b.frequency n) * 1 = _
  simp

/-- The exact ordered coefficient from harmonic `j` advecting harmonic `l`.
The first index is carried by the first input function; `l` enters the derivatives. -/
noncomputable def orderedKernel (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp l : ℤ)
    (a b : D → ComplexVector) (x : D) (i : Fin 3) : ℂ :=
  a x 0 * derivativeCoefficient g.radial k Φ l (fun y => b y i) x +
    (a x 1 / (g.radius x : ℂ)) *
      ((((l * kp : ℤ) : ℂ) * Complex.I) * b x i + angularGenerator (b x) i) +
    a x 2 * derivativeCoefficient g.axial k Φ l (fun y => b y i) x

theorem orderedKernel_eq_fullCoefficient {s : StripData D} {κ : ℝ}
    (c : CorrectionState.Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (carrierData : CorrectionState.HarmonicBlock D) (a b : Family D) (l : ℤ) (n : ℕ)
    {x : D} (hx : x ∈ s.domain) (hk : carrierData.frequency n ≠ 0)
    (hΦ : DifferentiableAt ℝ (carrierData.phase n) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b n y i) x) (i : Fin 3) :
    orderedKernel (HarmonicResidual.contextFrame c n) (carrierData.frequency n)
      (carrierData.phase n) (carrierData.angularFrequency n) l (a n) (b n) x i =
    sameCoefficient (liftedGeometry (slowGeometry c ho hR)) (fullPhase carrierData)
      (fun n => carrierData.frequency n * (l : ℝ))
      (fun n p => a n p.1) (fun n p => b n p.1) n (x, 0) i := by
  have hp (V : D → D) := along_fullPhase_lift carrierData n V (p := (x, 0)) hΦ
  have hθ := along_fullPhase_angular carrierData n (p := (x, 0)) hΦ
  have hd (V : D → D) (j : Fin 3) := along_fst V (p := (x, 0)) (hb j)
  simp only [sameCoefficient, strippedTransport, liftedGeometry, slowGeometry, normalDot, phaseNormal]
  change orderedKernel _ _ _ _ _ _ _ _ _ =
    a n x 0 * along (HarmonicResidual.liftDirection _) (fun p => b n p.1 i) (x, 0) +
    (a n x 1 / (c.operators.radius x : ℂ)) * angularGenerator (b n x) i +
    a n x 2 * along (HarmonicResidual.liftDirection _) (fun p => b n p.1 i) (x, 0) +
    phaseFactor (carrierData.frequency n * (l : ℝ)) *
      (normalDot (phaseNormal (fun p => c.operators.radius p.1)
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
        HarmonicResidual.angularDirection
        (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
        (fullPhase carrierData n) (x, 0)) (a n x)) * b n x i
  simp only [normalDot, phaseNormal, hp, hθ, hd, WithLp.ofLp_toLp,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    orderedKernel, derivativeCoefficient, HarmonicResidual.contextFrame,
    phaseFactor, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_intCast, Int.cast_mul]
  have hkc : (carrierData.frequency n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hrc : (c.operators.radius x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hR x hx).ne'
  field_simp ; ring

/-- Oscillatory input blocks have no stored velocity at harmonic zero. -/
def ZeroMode (b : CorrectionState.HarmonicBlock D) : Prop :=
  ∀ n i, b.velocity n i 0 = 0

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem amplitude_zero {b : CorrectionState.HarmonicBlock D} (hb : ZeroMode b) (n : ℕ) :
    amplitude b 0 n = 0 := by
  ext x i
  have hzero := hb n i
  simp [amplitude, blockAmplitude, HarmonicResidual.realCoefficients_apply, hzero]

theorem orderedKernel_zero_left (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp l : ℤ) (b : D → ComplexVector) (x : D) (i : Fin 3) :
    orderedKernel g k Φ kp l 0 b x i = 0 := by
  simp [orderedKernel]

theorem orderedKernel_zero_right (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp l : ℤ) (a : D → ComplexVector) (x : D) (i : Fin 3) :
    orderedKernel g k Φ kp l a 0 x i = 0 := by
  simp only [orderedKernel, Pi.zero_apply, mul_zero]
  fin_cases i <;> simp [angularGenerator, derivativeCoefficient, along]

/-- A common finite range is fixed for the whole family, not chosen anew on
each band. This is the finiteness needed by the uniform class estimates. -/
noncomputable def harmonicRange (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem band_support_range {a : Coefficients D} {N : ℕ} (ha : BandLimited a N) :
    a.support ⊆ harmonicRange N := by
  intro j hj
  have hh := ha j hj
  simp only [harmonicRange, Finset.mem_Icc]
  omega

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem convolution_apply_finset (a b : Coefficients D) (K : Finset ℤ)
    (ha : a.support ⊆ K) (m : ℤ) (x : D) :
    (a * b) m x = ∑ j ∈ K, a j x * b (m - j) x := by
  rw [convolution_apply]
  apply Finset.sum_subset ha
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]
  simp

theorem transport_convolution (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ)
    (kp : ℤ) (a b : HarmonicResidual.VectorCoefficients D) (K : Finset ℤ)
    (ha : ∀ i, (a i).support ⊆ K) (m : ℤ) (x : D) (i : Fin 3) :
    HarmonicResidual.transport g k Φ kp a b i m x =
      ∑ j ∈ K, orderedKernel g k Φ kp (m - j)
        (fun y r => a r j y) (fun y r => b r (m - j) y) x i := by
  simp only [HarmonicResidual.transport, coeff_add]
  rw [mul_assoc, convolution_apply_finset _ _ K (ha 0),
    convolution_apply_finset _ _ K (ha 1), convolution_apply_finset _ _ K (ha 2),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [orderedKernel, constant_mul, coeff_add, angularDifferentiate_apply,
    differentiate_apply, rotate_apply, div_eq_mul_inv]
  ring

/-- Coefficients evaluated using the original label's carrier. -/
noncomputable def withCarrier (carrierData b : CorrectionState.HarmonicBlock D) :
    CorrectionState.HarmonicBlock D where
  velocity := b.velocity
  pressure := b.pressure
  frequency := carrierData.frequency
  phase := carrierData.phase
  angularFrequency := carrierData.angularFrequency

/-- The updated label retains its carrier, including its angular frequency. -/
noncomputable def addBlock (a b : CorrectionState.HarmonicBlock D) :
    CorrectionState.HarmonicBlock D where
  velocity := fun n i => a.velocity n i + b.velocity n i
  pressure := fun n => a.pressure n + b.pressure n
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_oscillation (a b : CorrectionState.HarmonicBlock D) (n : ℕ)
    (p : D × ℝ) (i : Fin 3) :
    (addBlock a b).oscillation n p i = a.oscillation n p i +
      (withCarrier a b).oscillation n p i := by
  simp only [addBlock, withCarrier, CorrectionState.HarmonicBlock.oscillation,
    HarmonicResidual.field_add, Complex.add_re]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_pressure (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (p : D × ℝ) :
    (addBlock a b).oscillatoryPressure n p = a.oscillatoryPressure n p +
      (withCarrier a b).oscillatoryPressure n p := by
  simp only [addBlock, withCarrier, CorrectionState.HarmonicBlock.oscillatoryPressure,
    HarmonicResidual.field_add, Complex.add_re]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem blockAmplitude_addBlock (a b : CorrectionState.HarmonicBlock D) (n : ℕ) :
    blockAmplitude (addBlock a b) n = blockAmplitude a n + blockAmplitude b n := by
  funext i
  exact realCoefficients_add _ _

noncomputable def blockTransport (c : CorrectionState.Context D)
    (carrierData a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  fun n => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
    (carrierData.frequency n) (carrierData.phase n) (carrierData.angularFrequency n)
    (blockAmplitude a n) (blockAmplitude b n)

/-- All three actual quadratic terms introduced by adding one wave block. -/
noncomputable def nonlinearCoefficients (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  blockTransport c a a b + blockTransport c a b a + blockTransport c a b b

noncomputable def nonlinearErrorBlock (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (nonlinearCoefficients c a b n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

theorem nonlinearErrorBlock_band (c : CorrectionState.Context D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) :
    (nonlinearErrorBlock c a b).BandLimited (max (M + N) (N + N)) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have ha' r := HarmonicResidual.band_realCoefficients (ha.1 n r)
  have hb' r := HarmonicResidual.band_realCoefficients (hb.1 n r)
  have hab := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) ha' hb' i
  have hba := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' ha' i
  have hbb := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' hb' i
  exact ((hab.mono (le_max_left _ _)).add (hba.mono (by omega))).add
    (hbb.mono (le_max_right _ _))

theorem nonlinearErrorBlock_conjugate (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((nonlinearErrorBlock c a b).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem nonlinearErrorBlock_zero (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) : ZeroMode (nonlinearErrorBlock c a b) := by
  intro n i
  simp [nonlinearErrorBlock, HarmonicResidual.nonconstant]

/-! ## Identification with the actual differentiated residual -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem coefficient_eq_of_field_eq_at (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ)
    {kp : ℤ} (hkp : kp ≠ 0) (j : ℤ) (x : D)
    (he : ∀ θ, field a k Φ kp (x, θ) = field b k Φ kp (x, θ)) : a j x = b j x := by
  rw [← HarmonicResidual.extract_field a k Φ hkp j x,
    ← HarmonicResidual.extract_field b k Φ hkp j x]
  unfold HarmonicResidual.extract
  congr 1
  funext θ
  rw [he θ]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem vectorField_add (a b : HarmonicResidual.VectorCoefficients D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) :
    HarmonicResidual.vectorField (a + b) k Φ kp =
      HarmonicResidual.vectorField a k Φ kp + HarmonicResidual.vectorField b k Φ kp := by
  ext p i
  exact HarmonicResidual.field_add (a i) (b i) k Φ kp p

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem scalarField_add (a b : Coefficients D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ) :
    field (a + b) k Φ kp = field a k Φ kp + field b k Φ kp := by
  ext p
  exact HarmonicResidual.field_add a b k Φ kp p

theorem linear_mean_difference (g : HarmonicResidual.Frame D) (k : ℝ) (Φ : D → ℝ) (kp : ℤ)
    (B m : D → ComplexVector) (a : HarmonicResidual.VectorCoefficients D) (p : Coefficients D) {x : D}
    (hB : ∀ i, DifferentiableAt ℝ (fun y => B y i) x)
    (hm : ∀ i, DifferentiableAt ℝ (fun y => m y i) x) (j : ℤ) (i : Fin 3) :
    HarmonicResidual.linearResidual g k Φ kp (HarmonicResidual.constantVector (B + m)) a p i j x -
      HarmonicResidual.linearResidual g k Φ kp (HarmonicResidual.constantVector B) a p i j x =
        crossCoefficients g k Φ kp m a i j x := by
  simp only [HarmonicResidual.linearResidual, crossCoefficients, coeff_add, coeff_sub,
    transport_constant_left, transport_constant_right, Pi.add_apply,
    along_add _ (hB i) (hm i), HarmonicResidual.Actual.angularGenerator_add]
  ring

noncomputable def linearCoefficients (c : CorrectionState.Context D)
    (carrierData b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  fun n => HarmonicResidual.linearResidual (HarmonicResidual.contextFrame c n)
    (carrierData.frequency n) (carrierData.phase n) (carrierData.angularFrequency n)
    (HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
    (blockAmplitude b n) (HarmonicResidual.realCoefficients (b.pressure n))

/-- The complete wave change before removing its zero mode. The Gaussian
increment and the alias difference remain literal coefficient fields. -/
noncomputable def waveChangeCoefficients (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) (g A₀ A₁ : HarmonicResidual.BlockCoefficients D) :
    HarmonicResidual.BlockCoefficients D :=
  linearCoefficients c a b + meanCross c u.mean (withCarrier a b) + nonlinearCoefficients c a b -
    g - (A₁ - A₀)

noncomputable def interactionCoefficients (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : HarmonicResidual.BlockCoefficients D :=
  meanCross c u.mean (withCarrier a b) + nonlinearCoefficients c a b

noncomputable def interactionBlock (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (interactionCoefficients c u a b n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

noncomputable def linearGoodBlock (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) :
    CorrectionState.HarmonicBlock D where
  velocity := fun n i => HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (linearCoefficients c a b n i - g n i))
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nonconstant_add (a b : Coefficients D) :
    HarmonicResidual.nonconstant (a + b) =
      HarmonicResidual.nonconstant a + HarmonicResidual.nonconstant b := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  simp only [nonconstant_apply_of_ne _ hj, coeff_add]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The zero-mode alias remains in the complete residual but vanishes under
the actual nonconstant projection. -/
theorem nonconstant_real_sub_axisymmetric (a b : Coefficients D) (hb : BandLimited b 0) :
    HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients (a - b)) =
      HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients a) := by
  ext j x
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  simp only [nonconstant_apply_of_ne _ hj, HarmonicResidual.realCoefficients_apply,
    coeff_sub, band_zero_coefficient hb hj, band_zero_coefficient hb (neg_ne_zero.mpr hj),
    Pi.zero_apply, sub_zero]

theorem waveChange_projection_split (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) (g A₀ A₁ : HarmonicResidual.BlockCoefficients D)
    (hA : ∀ n i, BandLimited (A₁ n i - A₀ n i) 0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.nonconstant
        (HarmonicResidual.realCoefficients (waveChangeCoefficients c u a b g A₀ A₁ n i)) =
      (linearGoodBlock c a b g).velocity n i + (interactionBlock c u a b).velocity n i := by
  change HarmonicResidual.nonconstant (HarmonicResidual.realCoefficients
      ((linearCoefficients c a b n i + meanCross c u.mean (withCarrier a b) n i +
        nonlinearCoefficients c a b n i - g n i) - (A₁ n i - A₀ n i))) = _
  rw [nonconstant_real_sub_axisymmetric _ _ (hA n i)]
  have he : linearCoefficients c a b n i + meanCross c u.mean (withCarrier a b) n i +
      nonlinearCoefficients c a b n i - g n i =
      (linearCoefficients c a b n i - g n i) + interactionCoefficients c u a b n i := by
    simp only [interactionCoefficients, Pi.add_apply]
    abel
  rw [he, realCoefficients_add, nonconstant_add]
  rfl

/-! ## Extracting the actual divergence condition -/

noncomputable def divergenceCoefficients (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (a : HarmonicResidual.VectorCoefficients D) : Coefficients D :=
  differentiate g.radial k Φ (a 0) +
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * a 0 +
    constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ) * angularDifferentiate kp (a 1) +
    differentiate g.axial k Φ (a 2)

theorem divergenceCoefficients_single (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (a : HarmonicResidual.VectorCoefficients D) (j : ℤ) :
    divergenceCoefficients g k Φ kp (fun i => AddMonoidAlgebra.single j (a i j)) =
      AddMonoidAlgebra.single j (divergenceCoefficients g k Φ kp a j) := by
  ext m x
  by_cases hm : m = j
  · subst m
    simp [divergenceCoefficients, constantCoefficient, -LaurentPolynomial.single_eq_C_mul_T]
  · simp [divergenceCoefficients, constantCoefficient, hm,
      derivativeCoefficient, along, -LaurentPolynomial.single_eq_C_mul_T]

theorem smoothCoefficients_single {U : Set D} {f : D → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    HarmonicResidual.SmoothCoefficients U (AddMonoidAlgebra.single j f) := by
  intro l
  change ContDiffOn ℝ ∞ ((Finsupp.single j f) l) U
  by_cases hl : l = j
  · subst l
    simpa only [Finsupp.single_eq_same] using hf
  · rw [Finsupp.single_eq_of_ne hl]
    exact contDiffOn_const

theorem waveBounds_smooth {s : StripData D} {P : ℕ → D → ℝ} {α : ℝ}
    {b : CorrectionState.HarmonicBlock D} (hb : b.WaveBounds s P α) (h0 : ZeroMode b)
    (n : ℕ) (i : Fin 3) : HarmonicResidual.SmoothCoefficients s.domain (b.velocity n i) := by
  intro j
  by_cases hj : j = 0
  · subst j
    rw [h0 n i]
    exact contDiffOn_const
  exact (hb i j hj).smooth n

/-! ## Finite harmonic values, realness, and actual label reconstruction -/

theorem nonlinearCoefficients_band (c : CorrectionState.Context D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) (n : ℕ) (i : Fin 3) :
    BandLimited (nonlinearCoefficients c a b n i) (max (M + N) (N + N)) := by
  have ha' r := HarmonicResidual.band_realCoefficients (ha.1 n r)
  have hb' r := HarmonicResidual.band_realCoefficients (hb.1 n r)
  have hab := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) ha' hb' i
  have hba := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' ha' i
  have hbb := HarmonicResidual.band_transport (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) hb' hb' i
  exact ((hab.mono (le_max_left _ _)).add (hba.mono (by omega))).add
    (hbb.mono (le_max_right _ _))

theorem crossCoefficients_band (g : HarmonicResidual.Frame D)
    (k : ℝ) (Φ : D → ℝ) (kp : ℤ) (m : D → ComplexVector)
    {a : HarmonicResidual.VectorCoefficients D} {N : ℕ}
    (ha : ∀ i, BandLimited (a i) N) (i : Fin 3) :
    BandLimited (crossCoefficients g k Φ kp m a i) N := by
  have hleft : BandLimited (HarmonicResidual.transport g k Φ kp
      (HarmonicResidual.constantVector m) a i) N := by
    have h := HarmonicResidual.band_transport g k Φ kp
      (fun j => band_constantCoefficient (fun x => m x j)) ha i
    simp only [zero_add] at h
    exact h
  have hright : BandLimited (HarmonicResidual.transport g k Φ kp a
      (HarmonicResidual.constantVector m) i) N := by
    have h := HarmonicResidual.band_transport g k Φ kp
      ha (fun j => band_constantCoefficient (fun x => m x j)) i
    simp only [add_zero] at h
    exact h
  exact hleft.add hright

theorem interactionBlock_band (c : CorrectionState.Context D) (u : CorrectionState.State D)
    {a b : CorrectionState.HarmonicBlock D} {M N : ℕ}
    (ha : a.BandLimited M) (hb : b.BandLimited N) :
    (interactionBlock c u a b).BandLimited (max (M + N) (N + N)) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have hcross := crossCoefficients_band (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n) (tripleField u.mean n)
    (fun r => HarmonicResidual.band_realCoefficients (hb.1 n r)) i
  exact (hcross.mono (by omega)).add (nonlinearCoefficients_band c ha hb n i)

theorem interactionBlock_conjugate (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((interactionBlock c u a b).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem interactionBlock_zero (c : CorrectionState.Context D) (u : CorrectionState.State D)
    (a b : CorrectionState.HarmonicBlock D) : ZeroMode (interactionBlock c u a b) := by
  intro n i
  simp [interactionBlock, HarmonicResidual.nonconstant]

theorem linearGoodBlock_band (c : CorrectionState.Context D) (a : CorrectionState.HarmonicBlock D)
    {b : CorrectionState.HarmonicBlock D} {g : HarmonicResidual.BlockCoefficients D} {N E : ℕ}
    (hb : b.BandLimited N) (hg : ∀ n i, BandLimited (g n i) E) :
    (linearGoodBlock c a b g).BandLimited (max N E) := by
  refine ⟨fun n i => ?_, fun _ => HarmonicResidual.band_zero _⟩
  apply HarmonicResidual.band_nonconstant
  apply HarmonicResidual.band_realCoefficients
  have hlin := HarmonicResidual.band_linearResidual (HarmonicResidual.contextFrame c n)
    (a.frequency n) (a.phase n) (a.angularFrequency n)
    (B := HarmonicResidual.constantVector (HarmonicResidual.contextBase c n))
    (fun _ => band_constantCoefficient _)
    (fun r => HarmonicResidual.band_realCoefficients (hb.1 n r))
    (HarmonicResidual.band_realCoefficients (hb.2 n)) i
  exact HarmonicResidual.band_sub (hlin.mono (le_max_left _ _)) ((hg n i).mono (le_max_right _ _))

theorem linearGoodBlock_conjugate (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) (n : ℕ) (i : Fin 3) :
    ConjugateSymmetric ((linearGoodBlock c a b g).velocity n i) :=
  HarmonicResidual.nonconstant_conjugate (HarmonicResidual.realCoefficients_conjugate _)

theorem linearGoodBlock_zero (c : CorrectionState.Context D)
    (a b : CorrectionState.HarmonicBlock D) (g : HarmonicResidual.BlockCoefficients D) :
    ZeroMode (linearGoodBlock c a b g) := by
  intro n i
  simp [linearGoodBlock, HarmonicResidual.nonconstant]

noncomputable def waveResidualDifferenceBlock (c : CorrectionState.Context D)
    (u₀ u₁ : CorrectionState.State D) (a b : CorrectionState.HarmonicBlock D)
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D) : CorrectionState.HarmonicBlock D where
  velocity := fun n i => (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).velocity n i -
    (HarmonicResidual.residualBlock c u₀ a G A₀).velocity n i
  pressure := fun _ => 0
  frequency := a.frequency
  phase := a.phase
  angularFrequency := a.angularFrequency

theorem waveResidualDifferenceBlock_field (c : CorrectionState.Context D)
    (u₀ u₁ : CorrectionState.State D) (a b : CorrectionState.HarmonicBlock D)
    (G g A₀ A₁ : HarmonicResidual.BlockCoefficients D) (n : ℕ) (x : D × ℝ) (i : Fin 3) :
    (waveResidualDifferenceBlock c u₀ u₁ a b G g A₀ A₁).oscillation n x i =
      (HarmonicResidual.residualBlock c u₁ (addBlock a b) (G + g) A₁).oscillation n x i -
      (HarmonicResidual.residualBlock c u₀ a G A₀).oscillation n x i := by
  simp only [waveResidualDifferenceBlock, CorrectionState.HarmonicBlock.oscillation,
    HarmonicResidual.field_sub, Complex.sub_re]
  rfl

end NavierStokes.HarmonicWaveInteraction
