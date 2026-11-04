import Tengoku.GeneralStochToDet.stoch_to_det.Scalar
import Tengoku.GeneralStochToDet.stoch_to_det.Cone
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.Definitions
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.ClockLaw
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.CoordinateBound
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.ReferenceLoss
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.EntropyAssembly
import Tengoku.GeneralStochToDet.stoch_to_det.SharedRace.PairClockLaw
import Tengoku.Seed.InformationTheory.KullbackLeibler.ChainRule
import Tengoku.Seed.InformationTheory.KullbackLeibler.DataProcessing
import Tengoku.Seed.Probability.ProductMeasure
import Tengoku.Seed.Probability.Kernel.CompProdEqIff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# §§7–10. The race construction

The single obligation of the continuous tier: build the actual
`RaceQuantities` for any `SeedSetup` and `Clustering` — i.e. define the
four seed-level scalars and
prove Lemmas 7.2–7.5 (grouping, winner-entropy identity, exact race law,
chain split), Theorem 8.1 (`scalar ≤ S + κd`), Theorem 10.1
(`cone · ln 2 ≤ d`), and the `I ≤ H` cell-residual link of Theorem 12.1.

Intended concrete realizations:
* `winnerEntropy := ∫ H(A_ε ∣ L₀) d(seedLaw)` — at fixed `ε` the winner
  is a finite variable, so the integrand is a finite conditional entropy
  of the joint `(winner ε ∘ ·, id)`-pushforward of `L.joint`;
* `scalar` — contexts `(g, b)` are finite and `Law(U ∣ Z=z, B=b)` is the
  explicit `clockLawGiven b z` (Lemma 7.4), so `scalar` is a finite sum
  of `klDiv`s against the true conditional mixtures;
* `seedLeak` — KLs of restricted-and-normalized seed laws;
* `cone` — the context-integrated KL of the losing vector, or the
  remainder `seedLeak − scalar` with Lemma 7.5 proved for it.
-/

namespace stoch_to_det

universe u

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Concrete realizations of the four quantities

The continuous informations are written in the finite-context KL form exposed
by `condMIcts`.  In both cases the final measure argument is the *true*
conditional mixture of the source laws, not an arbitrary reference measure.
-/

/-- `P(B=b ∣ C₀=g) = ∑_z Q_g(z) σ_b(z)`.-/
private noncomputable def scalarWinnerProb {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, K.Q g z * K.sigma b z

/-- The global mass of a scalar context `(C₀ = g, B = b)`.-/
private noncomputable def scalarContextMass {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  K.s g * scalarWinnerProb K g b

/-- The source posterior `ν_{gb}(z) ∝ Q_g(z) σ_b(z)`.-/
private noncomputable def scalarSource {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (z : α × β) : ℝ :=
  K.Q g z * K.sigma b z / scalarWinnerProb K g b

/-- The true conditional marginal law of the winning raw clock in a context
`(C₀ = g, B = b)`.-/
private noncomputable def scalarClockMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : Measure ℝ :=
  ∑ z, ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z

/-- `I(U; Z ∣ B, C₀)` in bits, expanded over the finite contexts `(g,b)`.
Lemma 7.4 supplies the conditional clock law `clockLawGiven`.-/
private noncomputable def raceScalar {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  condMIcts
    (fun z (gb : K.κ × K.κ) => K.s gb.1 * K.Q gb.1 z * K.sigma gb.2 z)
    (fun z (gb : K.κ × K.κ) => K.clockLawGiven gb.2 z)
    (fun (gb : K.κ × K.κ) => scalarClockMarginal K gb.1 gb.2)

/-! #### The exact duplicate grouping

`clusterFiber K c` is the set of labels in cluster `c`.  The grouped seed is
the within-fibre maximum of `log π + ε`; subtracting that maximum from every
coordinate records the within-cluster winner and all excesses, so no seed
information is discarded.
-/

private abbrev clusterFiber {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (c : K.κ) := {ℓ : D.L.ι // K.cl ℓ = c}

private instance clusterNonempty {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) : Nonempty K.κ :=
  Nonempty.map K.cl (Latent.nonempty_ι D.L)

private instance clusterFiberNonempty {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (c : K.κ) : Nonempty (clusterFiber K c) := by
  obtain ⟨ℓ, hℓ⟩ := K.surj c
  exact ⟨⟨ℓ, hℓ⟩⟩

/-- The within-cluster winner `W_c`.-/
private noncomputable def groupedWithinWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) (c : K.κ) :
    clusterFiber K c :=
  Classical.choose (Finite.exists_max fun u : clusterFiber K c =>
    Real.log (D.L.prior u.1 / K.s c) + ε u.1)

/-- The grouped Gumbel `G̃_c = max_{ℓ∈c}(log π_{ℓ|c}+ε_ℓ)`.-/
private noncomputable def groupedG {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) (c : K.κ) : ℝ :=
  Real.log (D.L.prior (groupedWithinWinner K ε c).1 / K.s c) +
    ε (groupedWithinWinner K ε c).1

/-- The within-cluster exponential excess coordinates
`e_u / π_{u|c} - min_v (e_v / π_{v|c})`.  The zero coordinate records the
winner; together with `groupedG` these recover the original seed.-/
private noncomputable def groupedResidual {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ)
    (c : K.κ) (u : clusterFiber K c) : ℝ :=
  Real.exp (-(Real.log (D.L.prior u.1 / K.s c) + ε u.1)) -
    Real.exp (-(groupedG K ε c))

/-- The cluster winner for a grouped seed.-/
private noncomputable def groupedClusterWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (G : K.κ → ℝ)
    (z : α × β) : K.κ :=
  Classical.choose (Finite.exists_max fun c : K.κ =>
    Real.log (K.sigma c z) + G c)

/-- The two-stage label winner `(B,W_B)`.-/
private noncomputable def groupedLabelWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ)
    (z : α × β) : D.L.ι :=
  if z ∈ support p then
    (groupedWithinWinner K ε
      (groupedClusterWinner K (groupedG K ε) z)).1
  else winner D ε z

/-- The grouped-Gumbel law conditioned on cluster `b` winning at `z`.-/
private noncomputable def clusterSeedLawGivenWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ)
    (z : α × β) : Measure (K.κ → ℝ) :=
  if K.sigma b z = 0 then seedLaw K.κ
  else (ENNReal.ofReal (K.sigma b z))⁻¹ •
    (seedLaw K.κ).restrict {G | groupedClusterWinner K G z = b}

/-- The true grouped-seed marginal in the context `(B=b,C₀=g)`.-/
private noncomputable def clusterSeedContextMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Measure (K.κ → ℝ) :=
  ∑ z, ENNReal.ofReal (scalarSource K g b z) •
    clusterSeedLawGivenWinner K b z

/-- `I(G̃;Z ∣ B,C₀)` in bits.  Lemma 7.2(c) identifies this with the
label-seed expansion `raceSeedLeak`.-/
private noncomputable def raceClusterLeak {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  condMIcts
    (fun z (bg : K.κ × K.κ) => K.s bg.2 * K.Q bg.2 z * K.sigma bg.1 z)
    (fun z (bg : K.κ × K.κ) => clusterSeedLawGivenWinner K bg.1 z)
    (fun (bg : K.κ × K.κ) => clusterSeedContextMarginal K bg.2 bg.1)

/-! #### The conditional losing-clock channel

The cone calculation keeps the whole losing vector intact.  At fixed
`(g,b,u,z)` its law is a product of shifted unit exponentials; the marginal
below is again the true source mixture used by the golden formula.
-/

private abbrev losingIndex {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (b : K.κ) := {c : K.κ // c ≠ b}

private noncomputable def losingClockLaw {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : Measure (losingIndex K b → ℝ) :=
  Measure.pi fun c : losingIndex K b =>
    (expMeasure 1).map
      (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)

private noncomputable def losingReference {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    Measure (losingIndex K b → ℝ) :=
  Measure.pi fun _ : losingIndex K b => expMeasure 1

/-- `D_{gb}(u)=∑_z Q_g(z)e^{-u/σ_b(z)}`, the density of `(B=b,U=u)`
conditional on `C₀=g`.-/
private noncomputable def coneContextDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ :=
  ∑ z, K.Q g z * Real.exp (-u / K.sigma b z)

/-- The exact source posterior `ν_{gbu}`.-/
private noncomputable def coneSource {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ)
    (z : α × β) : ℝ :=
  K.Q g z * Real.exp (-u / K.sigma b z) / coneContextDensity K g b u

/-- The true conditional output mixture of the losing vector.-/
private noncomputable def losingClockMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    Measure (losingIndex K b → ℝ) :=
  ∑ z, ENNReal.ofReal (coneSource K g b u z) • losingClockLaw K b z u

/-- The single-context losing-vector information in nats.-/
private noncomputable def coneContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ :=
  ∑ z, coneSource K g b u z *
    (klDiv (losingClockLaw K b z u)
      (losingClockMarginal K g b u)).toReal

/-- The exact integral of the conditional losing-vector channel, in nats.-/
private noncomputable def integratedConeNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  ∑ g, K.s g * ∑ b,
    ∫ u in Set.Ioi (0 : ℝ),
      coneContextDensity K g b u * coneContextInfoNats K g b u

/-- Joint mass of `(Z=z, A=a, L₀=ℓ₀)` after averaging the seed.  Winner
calibration identifies the last factor with `P(A=a ∣ Z=z)`.-/
private noncomputable def seedContextJoint {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) (z : α × β) : ℝ :=
  D.L.joint (ℓ₀, z) * D.post a z

/-- The mass of the finite conditioning context `(A=a,L₀=ℓ₀)`.-/
private noncomputable def seedContextMass {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) : ℝ :=
  ∑ z, seedContextJoint D a ℓ₀ z

/-- The seed law conditioned on the event that the race at `z` is won by
`a`.  The zero-posterior branch is irrelevant to the KL expansion and gives a
total definition on the ambient finite alphabets.-/
private noncomputable def seedLawGivenWinner {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β) : Measure (D.L.ι → ℝ) :=
  if D.post a z = 0 then seedLaw D.L.ι
  else (ENNReal.ofReal (D.post a z))⁻¹ •
    (seedLaw D.L.ι).restrict {ε | winner D ε z = a}

/-- The true conditional marginal seed law in the context `(A=a,L₀=ℓ₀)`.-/
private noncomputable def seedContextMarginal {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) : Measure (D.L.ι → ℝ) :=
  ∑ z, ENNReal.ofReal
      (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
        seedLawGivenWinner D a z

/-- `I(ε; Z ∣ A,L₀)` in bits, as KLs between normalized restrictions of
`seedLaw` and their true context mixtures.-/
private noncomputable def raceSeedLeak {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  condMIcts
    (fun z (aℓ₀ : D.L.ι × D.L.ι) => seedContextJoint D aℓ₀.1 aℓ₀.2 z)
    (fun z (aℓ₀ : D.L.ι × D.L.ι) => seedLawGivenWinner D aℓ₀.1 z)
    (fun (aℓ₀ : D.L.ι × D.L.ι) => seedContextMarginal D aℓ₀.1 aℓ₀.2)

/-- `H(A_ε ∣ L₀)` averaged over the shared-Gumbel seed.-/
private noncomputable def raceWinnerEntropy {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∫ ε, condH (fun w => winner D ε w.2) Prod.fst D.L.joint
    ∂(seedLaw D.L.ι)

/-- The cone term is the exact chain-rule remainder.  Its mathematical
content is the data-processing inequality `raceScalar ≤ raceSeedLeak` and the
orthant estimate below.-/
private noncomputable def raceCone {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  raceSeedLeak D - raceScalar K

/-- The fixed-seed integrand whose average is `Rcell D`.  Naming it here keeps
the fusion and integration parts of `rcell_le` separate.-/
private noncomputable def raceCellIntegrand {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  ∑ a, ∑ b, D.L.prior b *
    (∑ z ∈ cell D ε a, D.L.comp b z) *
    Gdef (support p) D.w (fun z =>
      if winner D ε z = a then
        D.L.comp b z / ∑ z' ∈ cell D ε a, D.L.comp b z'
      else 0)

/-! ### Elementary positivity and definitional identities -/

/-! ### Finiteness of the KL expansions

Only positive-mass summands need a finiteness assertion; all remaining
summands have zero coefficient in `condMIcts`.
-/

/-! ### Lemma 7.4: exact race-law leaves -/

/- The published `Seed` race calibration is phrased for a `SeedSetup`.  The
cluster race only needs its underlying finite positive-weight theorem, which
we derive here from the same public exponential-clock API. -/

private noncomputable def weightedWinner {κ : Type} [Fintype κ]
    [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : κ :=
  Classical.choose (Finite.exists_max fun c => Real.log (t c) + G c)

private noncomputable def weightedValue {κ : Type}
    (t : κ → ℝ) (G : κ → ℝ) (c : κ) : ℝ :=
  Real.log (t c) + G c

private noncomputable def weightedLexWinner {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : κ :=
  lexMax (fun G c => weightedValue t G c) G

private noncomputable def weightedLexScore {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : ℝ :=
  ∑ a, if weightedLexWinner t G = a then weightedValue t G a else 0

private noncomputable def weightedExcess {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) (i : κ) : ℝ :=
  Real.exp (-(weightedValue t G i)) -
    Real.exp (-(weightedLexScore t G))

private lemma expMeasure_one_tilt {t : ℝ} (ht : 0 < t) :
    (expMeasure 1).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (-((1 / t - 1) * y)))) =
      ENNReal.ofReal t • expMeasure (1 / t) := by
  have hpdf (r : ℝ) : Measurable (gammaPDF 1 r) := by
    unfold gammaPDF
    exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hweight : Measurable
      (fun y : ℝ => ENNReal.ofReal
        (Real.exp (-((1 / t - 1) * y)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [← withDensity_mul volume (hpdf 1) hweight,
    ← withDensity_smul (μ := volume) (ENNReal.ofReal t) (hpdf (1 / t))]
  apply withDensity_congr_ae
  filter_upwards [] with y
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one,
    sub_self, Real.rpow_zero, mul_one, one_mul]
  by_cases hy : 0 ≤ y
  · simp only [ite_eq_left hy]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul ht.le]
    congr 1
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring
  · simp [ite_eq_right hy]

private lemma map_div_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t)) =
      expMeasure 1 := by
  letI : IsProbabilityMeasure (expMeasure (1 / t)) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr ht)
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t))) :=
    Measure.isProbabilityMeasure_map (measurable_id.div_const t).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Set.Iic x = Set.Iic (t * x) by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure (1 / t)) (t * x),
    ← ofReal_cdf (expMeasure 1) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq (one_div_pos.mpr ht), cdf_expMeasure_eq zero_lt_one]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left (mul_nonneg ht.le hx)]
    congr 2
    field_simp [ht.ne']
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [ite_eq_right hx, ite_eq_right htx]

/- Scaling and memorylessness in the orientation used by the within-cluster
excess vector. -/
private lemma map_div_expMeasure_one {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure 1) = expMeasure t := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (expMeasure t) :=
    isProbabilityMeasure_expMeasure ht
  letI : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure 1)) :=
    Measure.isProbabilityMeasure_map (measurable_id.div_const t).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Set.Iic x = Set.Iic (t * x) by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure 1) (t * x),
    ← ofReal_cdf (expMeasure t) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq zero_lt_one, cdf_expMeasure_eq ht]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left (mul_nonneg ht.le hx)]
    congr 2
    ring
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [ite_eq_right hx, ite_eq_right htx]

private lemma map_sub_restrict_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    Measure.map (fun x : ℝ => x - a)
        ((expMeasure 1).restrict (Set.Ioi a)) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  let ν : Measure ℝ := expMeasure 1
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.ext_of_Iic
  intro x
  have hpre : (fun y : ℝ => y - a) ⁻¹' Set.Iic x = Set.Iic (x + a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre,
    Measure.restrict_apply measurableSet_Iic,
    Measure.smul_apply, smul_eq_mul]
  by_cases hx : 0 ≤ x
  · have hxa : a ≤ x + a := by linarith
    have hxapos : 0 ≤ x + a := ha.trans hxa
    have hIoc : ν (Set.Ioc a (x + a)) =
        ENNReal.ofReal (cdf ν (x + a) - cdf ν a) := by
      calc
        ν (Set.Ioc a (x + a)) = (cdf ν).measure (Set.Ioc a (x + a)) := by
          rw [measure_cdf]
        _ = ENNReal.ofReal (cdf ν (x + a) - cdf ν a) :=
          StieltjesFunction.measure_Ioc (cdf ν) a (x + a)
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      hIoc, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one]
    simp only [ite_eq_left hxapos, ite_eq_left ha, ite_eq_left hx, one_mul]
    have hnonneg : 0 ≤ 1 - Real.exp (-x) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-a))]
    congr 1
    rw [show -(x + a) = -a + -x by ring, Real.exp_add]
    ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnot : ¬a < x + a := by linarith
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      Set.Ioc_eq_empty hnot, measure_empty, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one, ite_eq_right (not_le.mpr hxneg)]
    simp

private lemma map_scaled_excess_restrict_expMeasure_one
    {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Set.Ioi (t * u))) =
      ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
  have htu : 0 ≤ t * u := mul_nonneg ht.le hu
  calc
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Set.Ioi (t * u))) =
        Measure.map ((fun y : ℝ => y / t) ∘ (fun x : ℝ => x - t * u))
          ((expMeasure 1).restrict (Set.Ioi (t * u))) := by
      congr 1
      funext x
      dsimp only [Function.comp_apply]
      field_simp [ht.ne']
    _ = Measure.map (fun y : ℝ => y / t)
        (Measure.map (fun x : ℝ => x - t * u)
          ((expMeasure 1).restrict (Set.Ioi (t * u)))) :=
      (Measure.map_map (measurable_id.div_const t)
        (measurable_id.sub_const (t * u))).symm
    _ = Measure.map (fun y : ℝ => y / t)
        (ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure 1) := by
      rw [map_sub_restrict_expMeasure_one htu]
    _ = ENNReal.ofReal (Real.exp (-(t * u))) •
        Measure.map (fun y : ℝ => y / t) (expMeasure 1) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
      rw [map_div_expMeasure_one ht]

private noncomputable def weightedLosingExcessLaw
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) : Measure ({i : κ // i ≠ a} → ℝ) :=
  Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (t i.1)

private lemma map_losing_scaled_excess
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map
        (fun E : {i : κ // i ≠ a} → ℝ =>
          fun i => E i / t i.1 - u)
        ((Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).restrict
          (Set.pi Set.univ
            (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u)))) =
      (∏ i : {i : κ // i ≠ a},
          ENNReal.ofReal (Real.exp (-(t i.1 * u)))) •
        weightedLosingExcessLaw t a := by
  let d : {i : κ // i ≠ a} → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.exp (-(t i.1 * u)))
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  have hmap :
      Measure.map
          (fun E : {i : κ // i ≠ a} → ℝ =>
            fun i => E i / t i.1 - u)
          (Measure.pi (fun i : {i : κ // i ≠ a} =>
            (expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) =
        Measure.pi (fun i : {i : κ // i ≠ a} =>
          Measure.map (fun x : ℝ => x / t i.1 - u)
            ((expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) := by
    exact Measure.pi_map_pi fun (i : {i : κ // i ≠ a}) =>
      ((measurable_id.div_const (t i.1)).sub_const u).aemeasurable
  have hcoord (i : {i : κ // i ≠ a}) :
      Measure.map (fun x : ℝ => x / t i.1 - u)
          ((expMeasure 1).restrict (Set.Ioi (t i.1 * u))) =
        d i • expMeasure (t i.1) := by
    exact map_scaled_excess_restrict_expMeasure_one (ht i.1) hu
  letI (i : {i : κ // i ≠ a}) : IsFiniteMeasure
      (d i • expMeasure (t i.1)) := ⟨by simp [d]⟩
  have hscaled :
      Measure.pi (fun i : {i : κ // i ≠ a} =>
          d i • expMeasure (t i.1)) =
        (∏ i : {i : κ // i ≠ a}, d i) •
          weightedLosingExcessLaw t a := by
    unfold weightedLosingExcessLaw
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
  rw [Measure.restrict_pi_pi, hmap]
  calc
    Measure.pi (fun i : {i : κ // i ≠ a} =>
        Measure.map (fun x : ℝ => x / t i.1 - u)
          ((expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) =
        Measure.pi (fun i : {i : κ // i ≠ a} =>
          d i • expMeasure (t i.1)) := by
      congr 1
      funext i
      exact hcoord i
    _ = (∏ i : {i : κ // i ≠ a}, d i) •
        weightedLosingExcessLaw t a := hscaled

private lemma map_eval_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun E : κ → ℝ => E a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
  letI : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hwin : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  have hcoord (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hf_none : f xy none = xy.2 := congrArg Prod.snd hf_pair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hf_none]
  have hsectionWin (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
          ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 / t a * y)) := by
    ext x
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply (x, y)
    have hf_some (i : {i : κ // i ≠ a}) : f (x, y) (some i) = x i :=
      congrFun (congrArg Prod.fst hf_pair) i
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    have he_i (i : {i : κ // i ≠ a}) : (g (f (x, y))) i.1 = x i := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hf_some]
    have he_a : (g (f (x, y))) a = y := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hf_none]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      change g (f (x, y)) a / t a < g (f (x, y)) i.1 / t i.1 at hrel
      rw [he_a, he_i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      change g (f (x, y)) a / t a < g (f (x, y)) b / t b
      have hib := he_i i
      change g (f (x, y)) b = x i at hib
      rw [he_a, hib]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hratio : (∑ i : {i : κ // i ≠ a}, t i.1 / t a) =
      1 / t a - 1 := by
    rw [← Finset.sum_div, hsubsum]
    field_simp [(ht a).ne']
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Set.Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-((1 / t a - 1) * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hratio]
  have hclock :
      Measure.map (fun E : κ → ℝ => E a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        (expMeasure 1).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) := by
    unfold clockLaw
    rw [← hmap, Measure.restrict_map (g.measurable.comp f.measurable) hwin,
      Measure.map_map (measurable_pi_apply a) (g.measurable.comp f.measurable)]
    have hmapcoord :
        Measure.map ((fun E : κ → ℝ => E a) ∘ (g ∘ f))
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) =
          Measure.map Prod.snd
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun xy => hcoord xy
    rw [hmapcoord]
    ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.restrict_apply (measurable_snd hs)]
    have hset : MeasurableSet
        (Prod.snd ⁻¹' s ∩
          (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
      (measurable_snd hs).inter (hwin.preimage (g.measurable.comp f.measurable))
    rw [Measure.prod_apply_symm hset]
    have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
        Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)
            ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
              (Prod.snd ⁻¹' s ∩
                (g ∘ f) ⁻¹'
                  {E : κ → ℝ | strictClockWin t a E})) =
          s.indicator (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) y := by
      filter_upwards [hprod] with y hpy
      by_cases hys : y ∈ s
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) =
              Set.pi Set.univ
                (fun i : {i : κ // i ≠ a} =>
                  Set.Ioi (t i.1 / t a * y)) := by
            ext x
            simp only [Set.mem_preimage, Set.mem_inter_iff]
            have hmem :
                (g ∘ f) (x, y) ∈
                    {E : κ → ℝ | strictClockWin t a E} ↔
                  x ∈ Set.pi Set.univ
                    (fun i : {i : κ // i ≠ a} =>
                      Set.Ioi (t i.1 / t a * y)) :=
              Set.ext_iff.mp (hsectionWin y) x
            simpa only [hys, true_and] using hmem
        rw [hsec, Measure.pi_pi, hpy, Set.indicator_of_mem hys]
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) = ∅ := by
            ext x
            simp [hys]
        rw [hsec, measure_empty, Set.indicator_of_notMem hys]
    rw [lintegral_congr_ae hsections, lintegral_indicator hs,
      ← withDensity_apply _ hs]
  rw [hclock, expMeasure_one_tilt (ht a)]

private noncomputable def insertWinnerZero
    {κ : Type} [DecidableEq κ] (a : κ)
    (r : {i : κ // i ≠ a} → ℝ) : κ → ℝ :=
  fun i => if h : i = a then 0 else r ⟨i, h⟩

private lemma insertWinnerZero_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (insertWinnerZero a) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i = a
  · simpa [insertWinnerZero, h] using
      (measurable_const : Measurable (fun _ : {j : κ // j ≠ a} → ℝ => (0 : ℝ)))
  · simpa [insertWinnerZero, h] using
      (measurable_pi_apply (⟨i, h⟩ : {j : κ // j ≠ a}))

/- On a fixed strict-winner cell, the scaled minimum has law
`t_a • Exp(1)` and is independent of the full excess vector. -/
private theorem clock_min_excess_restrict_factorization
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map
        (fun E : κ → ℝ =>
          (E a / t a, fun i => E i / t i - E a / t a))
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      (ENNReal.ofReal (t a) • expMeasure 1).prod
        (Measure.map (insertWinnerZero a) (weightedLosingExcessLaw t a)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let q := loseμ.prod (expMeasure 1)
  let P := (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}
  let J : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ × (κ → ℝ) :=
    fun xy =>
      (xy.2 / t a,
        insertWinnerZero a (fun i => xy.1 i / t i.1 - xy.2 / t a))
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q, loseμ]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    unfold clockLaw
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hcoordA (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hfNone]
  have hcoordNe (xy : ({i : κ // i ≠ a} → ℝ) × ℝ)
      (i : {i : κ // i ≠ a}) : (g (f xy)) i.1 = xy.1 i := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfSome : f xy (some i) = xy.1 i :=
      congrFun (congrArg Prod.fst hfPair) i
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hfSome]
  have hwin : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  have hP : MeasurableSet P :=
    hwin.preimage (g.measurable.comp f.measurable)
  have hsectionP (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} =>
            Set.Ioi (t i.1 / t a * y)) := by
    ext x
    simp only [P, Set.mem_preimage, Set.mem_ofPred_eq, strictClockWin,
      Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply,
      Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      rw [hcoordA, hcoordNe (x, y) i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      rw [hcoordA, hcoordNe (x, y) i]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  have hJ : Measurable J := by
    have hy : Measurable
        (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2) := measurable_snd
    have hlose : Measurable
        (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ =>
          fun i => xy.1 i / t i.1 - xy.2 / t a) := by
      apply measurable_pi_lambda
      intro i
      have hxi : Measurable
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      exact (hxi.div_const (t i.1)).sub (hy.div_const (t a))
    apply Measurable.prodMk
    · exact hy.div_const (t a)
    · exact (insertWinnerZero_measurable a).comp hlose
  have horig : Measurable (fun E : κ → ℝ =>
      (E a / t a, fun i => E i / t i - E a / t a)) := by
    have hea : Measurable (fun E : κ → ℝ => E a) := measurable_pi_apply a
    apply Measurable.prodMk
    · exact hea.div_const (t a)
    · apply measurable_pi_lambda
      intro i
      have hei : Measurable (fun E : κ → ℝ => E i) := measurable_pi_apply i
      exact (hei.div_const (t i)).sub (hea.div_const (t a))
  have hJcomp :
      (fun E : κ → ℝ =>
        (E a / t a, fun i => E i / t i - E a / t a)) ∘ (g ∘ f) = J := by
    funext xy
    apply Prod.ext
    · simp only [Function.comp_apply, J]
      rw [hcoordA]
    · funext i
      by_cases hi : i = a
      · subst i
        simp [J, insertWinnerZero, hcoordA]
      · simp only [Function.comp_apply, J, insertWinnerZero, hi, dite_false]
        rw [hcoordNe xy ⟨i, hi⟩, hcoordA]
  have hsplit :
      Measure.map
          (fun E : κ → ℝ =>
            (E a / t a, fun i => E i / t i - E a / t a))
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map J (q.restrict P) := by
    rw [← hmap, Measure.restrict_map
      (g.measurable.comp f.measurable) hwin,
      Measure.map_map horig (g.measurable.comp f.measurable), hJcomp]
  have hminLaw :
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    calc
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
          Measure.map (fun y : ℝ => y / t a)
            (Measure.map (fun E : κ → ℝ => E a)
              ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
        exact (Measure.map_map (measurable_id.div_const (t a))
          (measurable_pi_apply a)).symm
      _ = Measure.map (fun y : ℝ => y / t a)
          (ENNReal.ofReal (t a) • expMeasure (1 / t a)) := by
        rw [map_eval_restrict_strictClockWin t ht htotal a]
      _ = ENNReal.ofReal (t a) •
          Measure.map (fun y : ℝ => y / t a) (expMeasure (1 / t a)) := by
        rw [Measure.map_smul]
      _ = ENNReal.ofReal (t a) • expMeasure 1 := by
        rw [map_div_expMeasure (ht a)]
  have hminSplit :
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    calc
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
          Measure.map (fun E : κ → ℝ => E a / t a)
            ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
        rw [← hmap, Measure.restrict_map
          (g.measurable.comp f.measurable) hwin,
          Measure.map_map
            ((measurable_pi_apply a).div_const (t a))
            (g.measurable.comp f.measurable)]
        apply Measure.map_congr
        filter_upwards [] with xy
        dsimp only [Function.comp_apply]
        rw [hcoordA]
      _ = ENNReal.ofReal (t a) • expMeasure 1 := hminLaw
  rw [hsplit]
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := insertWinnerZero a
  let ρfull : Measure (κ → ℝ) := Measure.map embed ρ
  have hρprob : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  letI : IsProbabilityMeasure ρ := hρprob
  have hembed : Measurable embed := insertWinnerZero_measurable a
  letI : IsProbabilityMeasure ρfull := by
    dsimp [ρfull]
    exact Measure.isProbabilityMeasure_map hembed.aemeasurable
  change Measure.map J (q.restrict P) =
    (ENNReal.ofReal (t a) • expMeasure 1).prod ρfull
  apply Measure.ext_prod
  intro s r hs hr
  let first : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ :=
    fun xy => xy.2 / t a
  let B : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := first ⁻¹' s ∩ P
  let A : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := J ⁻¹' (s ×ˢ r) ∩ P
  have hfirstMeas : Measurable first := measurable_snd.div_const (t a)
  have hB : MeasurableSet B :=
    (hs.preimage hfirstMeas).inter hP
  have hA : MeasurableSet A :=
    ((hs.prod hr).preimage hJ).inter hP
  have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
      loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A) =
        ρfull r *
          loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B) := by
    filter_upwards [hone] with y hy
    by_cases hys : y / t a ∈ s
    · let u : ℝ := y / t a
      let loseMap : ({i : κ // i ≠ a} → ℝ) →
          ({i : κ // i ≠ a} → ℝ) :=
        fun x i => x i / t i.1 - u
      let orth : Set ({i : κ // i ≠ a} → ℝ) :=
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u))
      let rpre : Set ({i : κ // i ≠ a} → ℝ) := embed ⁻¹' r
      have hu : 0 ≤ u := div_nonneg hy.le (ht a).le
      have hloseMap : Measurable loseMap := by
        apply measurable_pi_lambda
        intro i
        have hxi : Measurable
            (fun x : {j : κ // j ≠ a} → ℝ => x i) := measurable_pi_apply i
        exact (hxi.div_const (t i.1)).sub_const u
      have horth : MeasurableSet orth := by
        apply MeasurableSet.univ_pi
        intro i
        exact measurableSet_Ioi
      have hrpre : MeasurableSet rpre := hr.preimage hembed
      have hPsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P = orth := by
        rw [hsectionP]
        congr 1
        funext i
        congr 1
        dsimp only [u]
        field_simp [(ht a).ne']
      have hAsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A =
            loseMap ⁻¹' rpre ∩ orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [A, Set.mem_preimage, Set.mem_inter_iff,
          Set.mem_prod, J, rpre, embed, loseMap]
        dsimp only [u]
        simpa only [hys, true_and, hpiff]
      have hBsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [B, Set.mem_preimage, Set.mem_inter_iff, first]
        simpa only [hys, true_and, hpiff]
      have hlaw := map_losing_scaled_excess t ht a hu
      change Measure.map loseMap (loseμ.restrict orth) =
          (∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u)))) • ρ at hlaw
      have hlawR := congrArg (fun μ : Measure ({i : κ // i ≠ a} → ℝ) =>
        μ rpre) hlaw
      rw [Measure.map_apply hloseMap hrpre,
        Measure.restrict_apply (hrpre.preimage hloseMap),
        Measure.smul_apply, smul_eq_mul] at hlawR
      have horthMass : loseμ orth =
          ∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u))) := by
        have hlawU := congrArg
          (fun μ : Measure ({i : κ // i ≠ a} → ℝ) => μ Set.univ) hlaw
        rw [Measure.map_apply hloseMap MeasurableSet.univ] at hlawU
        simp only [Set.preimage_univ] at hlawU
        rw [Measure.restrict_apply MeasurableSet.univ,
          Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hlawU
        simpa using hlawU
      have hρfull : ρfull r = ρ rpre := by
        dsimp only [ρfull]
        rw [Measure.map_apply hembed hr]
      rw [hAsec, hBsec, hlawR, horthMass, hρfull]
      ac_rfl
    · have hAempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A = ∅ := by
        ext x
        simp [A, J, hys]
      have hBempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = ∅ := by
        ext x
        simp [B, first, hys]
      rw [hAempty, hBempty, measure_empty, mul_zero]
  rw [Measure.map_apply hJ (hs.prod hr),
    Measure.restrict_apply ((hs.prod hr).preimage hJ)]
  change q A = _
  rw [Measure.prod_apply_symm hA, lintegral_congr_ae hsections,
    lintegral_const_mul _ (measurable_measure_prodMk_right hB),
    ← Measure.prod_apply_symm hB]
  have hqB : q B = (ENNReal.ofReal (t a) • expMeasure 1) s := by
    calc
      q B = (q.restrict P) (first ⁻¹' s) := by
        rw [Measure.restrict_apply (hs.preimage hfirstMeas)]
      _ = Measure.map first (q.restrict P) s := by
        rw [Measure.map_apply hfirstMeas hs]
      _ = (ENNReal.ofReal (t a) • expMeasure 1) s := by
        change Measure.map
            (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
            (q.restrict P) s = _
        rw [hminSplit]
  rw [Measure.prod_prod, hqB]
  ac_rfl

/- The one-block independence statement behind Lemma 7.2(a).  It is proved
by partitioning the exponential clocks according to their strict winner and
then summing the fixed-cell factorization above. -/

/-! ### Lemmas 7.2 and 7.3: grouping and winner entropy -/

private noncomputable def withinClusterWeight {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (c : K.κ)
    (u : clusterFiber K c) : ℝ :=
  D.L.prior u.1 / K.s c

/- Reindex the iid label seeds by their cluster fibres.  This is the
measure-theoretic independence input for both parts of Lemma 7.2(a). -/

private noncomputable def groupedPair {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) :
    (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ) :=
  (groupedG K ε, groupedResidual K ε)

private noncomputable def groupedReconstruct {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D)
    (q : (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ))
    (ℓ : D.L.ι) : ℝ :=
  -Real.log ((D.L.prior ℓ / K.s (K.cl ℓ)) *
    (q.2 (K.cl ℓ) ⟨ℓ, rfl⟩ + Real.exp (-q.1 (K.cl ℓ))))

private noncomputable def groupedClusterLexWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (G : K.κ → ℝ)
    (z : α × β) : K.κ :=
  weightedLexWinner (fun c => K.sigma c z) G

private def groupedClusterEvent {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    Set (K.κ → ℝ) :=
  {G | groupedClusterLexWinner K G z = b}

private def groupedResidualEvent {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (a : D.L.ι) :
    Set ((c : K.κ) → clusterFiber K c → ℝ) :=
  {R | R (K.cl a) ⟨a, rfl⟩ = 0}

private noncomputable def groupedResidualLaw {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    Measure ((c : K.κ) → clusterFiber K c → ℝ) :=
  Measure.map (groupedResidual K) (seedLaw D.L.ι)

private noncomputable def groupedResidualLawGivenLabel
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : Measure ((c : K.κ) → clusterFiber K c → ℝ) :=
  (ENNReal.ofReal (D.L.prior a / K.s (K.cl a)))⁻¹ •
    (groupedResidualLaw K).restrict (groupedResidualEvent K a)

private noncomputable def labelWithinWeight
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : ℝ :=
  D.L.prior a / K.s (K.cl a)

private noncomputable def balanceWinnerProb {p : α × β → ℝ}
    (D : SeedSetup p) (A : α × β → D.L.ι) (l₀ a : D.L.ι) : ℝ :=
  ∑ z, if A z = a then D.L.comp l₀ z else 0

private noncomputable def balanceRestrictionCostNats {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∑ a, ∑ l₀, ∑ z,
    seedContextJoint D a l₀ z * Real.log (1 / D.post a z)

private noncomputable def balanceMarginalCostNats {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∑ a, ∑ l₀, seedContextMass D a l₀ *
    (klDiv (seedContextMarginal D a l₀) (seedLaw D.L.ι)).toReal

private noncomputable def balanceDensityReal {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) : ℝ :=
  balanceWinnerProb D (lexWinner D ε) l₀ a / resamplePrior D l₀ a

private noncomputable def balanceDensity {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (balanceDensityReal D l₀ a ε)

private noncomputable def balanceTermDensity {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (z : α × β)
    (ε : D.L.ι → ℝ) : ℝ≥0∞ :=
  if lexWinner D ε z = a then
    ENNReal.ofReal (D.L.comp l₀ z / resamplePrior D l₀ a)
  else 0

/-! ### Theorem 8.1: the scalar channel -/

/-- The information in one positive `(g,b)` context, in nats.-/
private noncomputable def scalarContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    (klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b)).toReal

/-- `C_{gb}=D(ν_{gb} ‖ Q_g)` in nats.-/
private noncomputable def scalarSourceKLNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    Real.log (scalarSource K g b z / K.Q g z)

/-- The explicit conditional law of `(B,Z)` given `C₀=g`.-/
private noncomputable def scalarPosteriorJoint {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    K.κ × (α × β) → ℝ :=
  fun bz => K.Q g bz.2 * K.sigma bz.1 bz.2

private noncomputable def scalarLogExpDensity (n : ℝ) : ℝ :=
  Real.exp (n - Real.exp n)

private noncomputable def scalarDensityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

private noncomputable def scalarLogExpMeasure : Measure ℝ :=
  scalarDensityMeasure scalarLogExpDensity

private noncomputable def scalarMixtureDensity { ι : Type* } [Fintype ι]
    (r X : ι → ℝ) (w : ℝ) : ℝ :=
  ∑ i, r i * scalarLogExpDensity (w - X i)

/-! ### Lemma 7.5 and Theorem 10.1: the losing-vector cone -/

private lemma losingClockLaw_isProbability_all {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : IsProbabilityMeasure (losingClockLaw K b z u) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (c : losingIndex K b) : IsProbabilityMeasure
      ((expMeasure 1).map
        (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)) := by
    exact Measure.isProbabilityMeasure_map
      (measurable_const.add measurable_id).aemeasurable
  unfold losingClockLaw
  infer_instance

/-- The finite mismatch charge appearing after the `u` integral has been
evaluated.-/
private noncomputable def coneCharge {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  ∑ g, K.s g * ∑ z, K.Q g z * (1 - ∑ b, K.sigma b z ^ 2)

private noncomputable def clusterClockSplit {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    (K.κ → ℝ) → ℝ × (losingIndex K b → ℝ) :=
  fun G => (Real.exp (-G b), fun c => Real.exp (-G c.1))

private noncomputable def clusterClockJoin {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    (ℝ × (losingIndex K b → ℝ)) → K.κ → ℝ :=
  fun uv c => if h : c = b then -Real.log uv.1 else -Real.log (uv.2 ⟨c, h⟩)

private noncomputable def raceLosingKernel {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    Kernel ℝ (losingIndex K b → ℝ) :=
  ((Kernel.id : Kernel ℝ ℝ).prod
      (Kernel.const ℝ (losingReference K b))).map
    (fun ue c => ue.1 * (K.sigma c.1 z / K.sigma b z) + ue.2 c)

private lemma raceLosingKernel_apply {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) (u : ℝ) :
    raceLosingKernel K b z u = losingClockLaw K b z u := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (losingReference K b) := by
    unfold losingReference
    infer_instance
  let r : losingIndex K b → ℝ := fun c =>
    K.sigma c.1 z / K.sigma b z
  change
    (((Kernel.id : Kernel ℝ ℝ).prod
        (Kernel.const ℝ (Measure.pi fun _ : losingIndex K b => expMeasure 1))).map
      (fun ue c => ue.1 * r c + ue.2 c)) u =
      Measure.pi fun c : losingIndex K b =>
        (expMeasure 1).map (fun e => u * r c + e)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map (fun x c => u * r c + x c)
      (Measure.pi fun _ : losingIndex K b => expMeasure 1) = _
  rw [Measure.pi_map_pi fun c => (by fun_prop :
    AEMeasurable
      (fun e : ℝ => u * r c + e)
      (expMeasure 1))]

private lemma raceLosingKernel_isMarkov {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    IsMarkovKernel (raceLosingKernel K b z) := by
  refine ⟨fun u => ?_⟩
  rw [raceLosingKernel_apply K b z u]
  exact losingClockLaw_isProbability_all K b z u

private noncomputable def raceContextKernel {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Kernel ℝ (losingIndex K b → ℝ) :=
  letI (z : α × β) : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  Kernel.sum fun z =>
    (raceLosingKernel K b z).withDensity
      (fun u _ => ENNReal.ofReal (coneSource K g b u z))

private lemma map_mul_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => t * x) (expMeasure t) = expMeasure 1 := by
  simpa [div_eq_mul_inv, ht.ne', mul_comm] using
    (map_div_expMeasure (t := 1 / t) (one_div_pos.mpr ht))

private lemma map_weightedLosingExcess_scale
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) :
    Measure.map
        (fun R : {i : κ // i ≠ a} → ℝ => fun i => t i.1 * R i)
        (weightedLosingExcessLaw t a) =
      Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1 := by
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure (expMeasure (t i.1)) :=
    isProbabilityMeasure_expMeasure (ht i.1)
  let r : {i : κ // i ≠ a} → ℝ := fun i => t i.1
  unfold weightedLosingExcessLaw
  change Measure.map (fun R i => r i * R i)
      (Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (r i)) = _
  rw [Measure.pi_map_pi fun i => (by fun_prop :
    AEMeasurable (fun x : ℝ => r i * x) (expMeasure (r i)))]
  congr 1
  funext i
  exact map_mul_expMeasure (ht i.1)

/-- Reassemble a distinguished clock and the remaining coordinates into one
full clock vector.-/
private noncomputable def winnerClockJoin
    {κ : Type} [DecidableEq κ] (a : κ)
    (sr : ℝ × ({i : κ // i ≠ a} → ℝ)) : κ → ℝ :=
  fun i => if h : i = a then sr.1 else sr.2 ⟨i, h⟩

private lemma winnerClockJoin_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (winnerClockJoin a) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = a
  · simp only [winnerClockJoin, hi, dite_true]
    exact measurable_fst
  · simp only [winnerClockJoin, hi, dite_false]
    exact (measurable_pi_apply (⟨i, hi⟩ : {j : κ // j ≠ a})).comp measurable_snd

/-- A fresh distinguished `Exp(1)` clock together with fresh iid losing
clocks is just the original iid clock vector.-/
private lemma winnerClockJoin_law
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measure.map (winnerClockJoin a)
        ((expMeasure 1).prod
          (Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1)) =
      clockLaw κ := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  letI : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := loseμ.prod (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q, loseμ]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    unfold clockLaw
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hjoinSwap : winnerClockJoin a ∘ Prod.swap = g ∘ f := by
    funext xy i
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ a} => ℝ)).apply_symm_apply xy
    by_cases hi : i = a
    · subst i
      have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [dite_true]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hfNone]
    · have hfSome : f xy (some ⟨i, hi⟩) = xy.1 ⟨i, hi⟩ :=
        congrFun (congrArg Prod.fst hfPair) ⟨i, hi⟩
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [hi, dite_false]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne hi, hfSome]
  change Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) = _
  calc
    Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) =
        Measure.map (winnerClockJoin a) (Measure.map Prod.swap q) := by
      rw [Measure.prod_swap]
    _ = Measure.map (winnerClockJoin a ∘ Prod.swap) q :=
      Measure.map_map (winnerClockJoin_measurable a) measurable_swap
    _ = Measure.map (g ∘ f) q := by rw [hjoinSwap]
    _ = clockLaw κ := hmap

/-- On the cell where `a` wins, remove the common weighted-race minimum from
every losing raw clock and retain that minimum in coordinate `a`.-/
private noncomputable def winnerResidualClock
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : κ → ℝ :=
  fun i => if _h : i = a then E a / t a else E i - t i * (E a / t a)

private lemma winnerResidualClock_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    Measurable (winnerResidualClock t a) := by
  have hea : Measurable (fun E : κ → ℝ => E a) := measurable_pi_apply a
  have hratio : Measurable (fun E : κ → ℝ => E a / t a) :=
    hea.div measurable_const
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = a
  · simpa only [winnerResidualClock, hi, dite_true] using hratio
  · have hei : Measurable (fun E : κ → ℝ => E i) := measurable_pi_apply i
    have hmul : Measurable (fun E : κ → ℝ => t i * (E a / t a)) := by
      fun_prop
    simp only [winnerResidualClock, hi, dite_false]
    exact hei.sub hmul

/-- Fixed-winner exponential memorylessness in full-vector form.  The
residual vector consists of fresh iid `Exp(1)` clocks, with total mass equal
to the probability `t a` of the winner cell.-/
private theorem winnerResidualClock_restrict_law
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • clockLaw κ := by
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let A : Measure ℝ := ENNReal.ofReal (t a) • expMeasure 1
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := insertWinnerZero a
  let norm : (κ → ℝ) → ℝ × (κ → ℝ) := fun E =>
    (E a / t a, fun i => E i / t i - E a / t a)
  let out : (ℝ × (κ → ℝ)) → κ → ℝ := fun sr i =>
    if i = a then sr.1 else t i * sr.2 i
  let assemble : (ℝ × ({i : κ // i ≠ a} → ℝ)) → κ → ℝ := fun sr i =>
    if h : i = a then sr.1 else t i * sr.2 ⟨i, h⟩
  let loseScale : ({i : κ // i ≠ a} → ℝ) →
      ({i : κ // i ≠ a} → ℝ) := fun R i => t i.1 * R i
  let scale : (ℝ × ({i : κ // i ≠ a} → ℝ)) →
      ℝ × ({i : κ // i ≠ a} → ℝ) := Prod.map id loseScale
  have hnorm : Measurable norm := by fun_prop
  have hout : Measurable out := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = a
    · simpa only [out, hi, ite_true] using
        (measurable_fst : Measurable
          (fun sr : ℝ × (κ → ℝ) => sr.1))
    · have hcoord : Measurable
          (fun sr : ℝ × (κ → ℝ) => sr.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have hmul : Measurable (fun sr : ℝ × (κ → ℝ) => t i * sr.2 i) := by
        fun_prop
      simpa only [out, hi, ite_false] using hmul
  have hembed : Measurable embed := insertWinnerZero_measurable a
  have hassemble : Measurable assemble := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = a
    · simpa only [assemble, hi, dite_true] using
        (measurable_fst : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => sr.1))
    · have hcoord : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => sr.2 ⟨i, hi⟩) :=
        (measurable_pi_apply (⟨i, hi⟩ : {j : κ // j ≠ a})).comp measurable_snd
      have hmul : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => t i * sr.2 ⟨i, hi⟩) := by
        fun_prop
      simpa only [assemble, hi, dite_false] using hmul
  have hloseScale : Measurable loseScale := by fun_prop
  have hscale : Measurable scale := measurable_id.prodMap hloseScale
  have hresidualNorm : winnerResidualClock t a = out ∘ norm := by
    funext E i
    by_cases hi : i = a
    · subst i
      simp [winnerResidualClock, out, norm]
    · simp only [winnerResidualClock, hi, dite_false, Function.comp_apply,
        out, norm, ite_false]
      field_simp [(ht i).ne', (ht a).ne']
  have houtEmbed : out ∘ Prod.map id embed = assemble := by
    funext sr i
    by_cases hi : i = a
    · subst i
      simp [out, assemble]
    · simp [out, assemble, embed, insertWinnerZero, hi]
  have hassembleScale : assemble = winnerClockJoin a ∘ scale := by
    funext sr i
    by_cases hi : i = a
    · subst i
      simp [assemble, winnerClockJoin, scale]
    · simp [assemble, winnerClockJoin, scale, loseScale, hi]
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  letI : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  letI : SFinite A := by
    dsimp [A]
    infer_instance
  have hscaleLaw : Measure.map scale (A.prod ρ) = A.prod loseμ := by
    calc
      Measure.map scale (A.prod ρ) =
          (Measure.map id A).prod (Measure.map loseScale ρ) := by
        exact (Measure.map_prod_map A ρ measurable_id hloseScale).symm
      _ = A.prod loseμ := by
        rw [Measure.map_id]
        congr 1
        dsimp only [loseScale, ρ, loseμ]
        exact map_weightedLosingExcess_scale t ht a
  have hAprod : A.prod loseμ =
      ENNReal.ofReal (t a) • ((expMeasure 1).prod loseμ) := by
    dsimp only [A]
    rw [Measure.prod_smul_left]
  calc
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map out
          (Measure.map norm
            ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
      rw [hresidualNorm]
      exact (Measure.map_map hout hnorm).symm
    _ = Measure.map out
        (A.prod (Measure.map embed ρ)) := by
      rw [clock_min_excess_restrict_factorization t ht htotal a]
    _ = Measure.map assemble (A.prod ρ) := by
      calc
        Measure.map out (A.prod (Measure.map embed ρ)) =
            Measure.map out ((Measure.map id A).prod (Measure.map embed ρ)) := by
          rw [Measure.map_id]
        _ = Measure.map out
            (Measure.map (Prod.map id embed) (A.prod ρ)) := by
          rw [← Measure.map_prod_map A ρ measurable_id hembed]
        _ = Measure.map (out ∘ Prod.map id embed) (A.prod ρ) :=
          Measure.map_map hout (measurable_id.prodMap hembed)
        _ = Measure.map assemble (A.prod ρ) := by rw [houtEmbed]
    _ = Measure.map (winnerClockJoin a) (Measure.map scale (A.prod ρ)) := by
      rw [hassembleScale]
      exact (Measure.map_map (winnerClockJoin_measurable a) hscale).symm
    _ = Measure.map (winnerClockJoin a) (A.prod loseμ) := by
      rw [hscaleLaw]
    _ = Measure.map (winnerClockJoin a)
        (ENNReal.ofReal (t a) • ((expMeasure 1).prod loseμ)) := by
      rw [hAprod]
    _ = ENNReal.ofReal (t a) •
        Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (t a) • clockLaw κ := by
      rw [show Measure.map (winnerClockJoin a)
          ((expMeasure 1).prod loseμ) = clockLaw κ by
        dsimp only [loseμ]
        exact winnerClockJoin_law a]

@[simp] private lemma winnerResidualClock_apply_winner
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ) (E : κ → ℝ) :
    winnerResidualClock t a E a = E a / t a := by
  simp [winnerResidualClock]

private lemma winnerResidualClock_apply_loser
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a i : κ)
    (hi : i ≠ a) (E : κ → ℝ) :
    winnerResidualClock t a E i = E i - t i * (E a / t a) := by
  simp [winnerResidualClock, hi]

/-- Raw-clock reconstruction from the fresh residual vector.-/
private lemma winnerResidualClock_reconstruct
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (E : κ → ℝ) :
    E i = t i * winnerResidualClock t a E a +
      if i = a then 0 else winnerResidualClock t a E i := by
  by_cases hi : i = a
  · subst i
    rw [winnerResidualClock_apply_winner]
    simp
    field_simp [(ht a).ne']
  · rw [winnerResidualClock_apply_winner,
      winnerResidualClock_apply_loser t a i hi E]
    simp [hi]

/-- The residual transformation preserves the total raw clock.  Hence every
simplex-normalized coordinate may use the same denominator before and after
conditioning on the winner.-/
private lemma sum_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    ∑ i, winnerResidualClock t a E i = ∑ i, E i := by
  let W : κ → ℝ := winnerResidualClock t a E
  let m : ℝ := E a / t a
  have hWwinner : W a = m := by
    dsimp only [W, m]
    exact winnerResidualClock_apply_winner t a E
  have hWloser (i : κ) (hi : i ∈ (univ : Finset κ).erase a) :
      W i = E i - t i * m := by
    have hne : i ≠ a := by
      simpa using (Finset.mem_erase.mp hi).1
    dsimp only [W, m]
    exact winnerResidualClock_apply_loser t a i hne E
  have htErase : (∑ i ∈ (univ : Finset κ).erase a, t i) = 1 - t a := by
    have h := Finset.sum_erase_add (univ : Finset κ) t (Finset.mem_univ a)
    rw [htotal] at h
    linarith
  have hEa : t a * m = E a := by
    dsimp only [m]
    field_simp [(ht a).ne']
  have hWErase := Finset.sum_erase_add (univ : Finset κ) W
    (Finset.mem_univ a)
  have hEErase := Finset.sum_erase_add (univ : Finset κ) E
    (Finset.mem_univ a)
  calc
    (∑ i, winnerResidualClock t a E i) =
        (∑ i ∈ (univ : Finset κ).erase a, W i) + W a := by
      change (∑ i, W i) = _
      exact hWErase.symm
    _ = (∑ i ∈ (univ : Finset κ).erase a, (E i - t i * m)) + m := by
      rw [hWwinner]
      apply congrArg (fun x : ℝ => x + m)
      apply Finset.sum_congr rfl
      exact hWloser
    _ = (∑ i ∈ (univ : Finset κ).erase a, E i) -
          (∑ i ∈ (univ : Finset κ).erase a, t i) * m + m := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ i ∈ (univ : Finset κ).erase a, E i) + E a := by
      rw [htErase, ← hEa]
      ring
    _ = ∑ i, E i := hEErase

private lemma normalized_winner_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    E a / (∑ i, E i) =
      t a * (winnerResidualClock t a E a /
        ∑ i, winnerResidualClock t a E i) := by
  have hEa : E a = t a * winnerResidualClock t a E a := by
    simpa using winnerResidualClock_reconstruct t ht a a E
  rw [hEa, ← sum_winnerResidualClock t ht htotal a E]
  ring

private lemma normalized_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    E i / (∑ j, E j) =
      (t i * winnerResidualClock t a E a + winnerResidualClock t a E i) /
        ∑ j, winnerResidualClock t a E j := by
  have hEi := winnerResidualClock_reconstruct t ht a i E
  simp only [hi, ite_false] at hEi
  rw [hEi, ← sum_winnerResidualClock t ht htotal a E]

private lemma weighted_ratio_loser_eq_residual
    {κ : Type} [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    (E a / t a) * t i / E i =
      t i * winnerResidualClock t a E a /
        (t i * winnerResidualClock t a E a + winnerResidualClock t a E i) := by
  have hEi := winnerResidualClock_reconstruct t ht a i E
  simp only [hi, ite_false] at hEi
  rw [hEi, winnerResidualClock_apply_winner]
  ring

/-! ### Normalized clock moments on the fixed-winner cells -/

/-- A strict weighted-clock winner is also the lexicographic minimizer used
by the normalized shared-race quantities. Strictness makes the tie-break
irrelevant.-/
private lemma clockArgmin_eq_of_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (a : κ) (ha : strictClockWin t a E) :
    SharedRace.clockArgmin t E = a := by
  by_contra hne
  have hmax := lexMax_max (fun E i => -(E i / t i)) E a
  have hstrict := ha (SharedRace.clockArgmin t E) hne
  change -(E a / t a) ≤
    -(E (SharedRace.clockArgmin t E) /
      t (SharedRace.clockArgmin t E)) at hmax
  linarith

private lemma rawRaceMin_eq_of_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (a : κ) (ha : strictClockWin t a E) :
    SharedRace.rawRaceMin t E = E a / t a := by
  unfold SharedRace.rawRaceMin
  rw [clockArgmin_eq_of_strictClockWin t E a ha]

/-- On a fixed winner cell, the normalized race minimum is the normalized
winner coordinate of the fresh residual clock.-/
private lemma normRaceMin_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) (ha : strictClockWin t a E) :
    SharedRace.normRaceMin t E =
      SharedRace.normClock (winnerResidualClock t a E) a := by
  unfold SharedRace.normRaceMin SharedRace.normClock SharedRace.clockTotal
  rw [rawRaceMin_eq_of_strictClockWin t E a ha,
    winnerResidualClock_apply_winner,
    sum_winnerResidualClock t ht htotal a E]

/-- The original winning normalized coordinate is its prior mass times the
fresh residual normalized coordinate.-/
private lemma normClock_winner_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    SharedRace.normClock E a =
      t a * SharedRace.normClock (winnerResidualClock t a E) a := by
  unfold SharedRace.normClock SharedRace.clockTotal
  exact normalized_winner_eq_residual t ht htotal a E

/-- The original losing normalized coordinate after removing the common
race minimum.-/
private lemma normClock_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    SharedRace.normClock E i =
      (t i * winnerResidualClock t a E a +
          winnerResidualClock t a E i) /
        SharedRace.clockTotal (winnerResidualClock t a E) := by
  unfold SharedRace.normClock SharedRace.clockTotal
  exact normalized_loser_eq_residual t ht htotal a i hi E

/-- The shared-race ratio on a losing coordinate, written in the
fresh residual clocks.-/
private lemma raceRatio_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ)
    (ha : strictClockWin t a E) :
    SharedRace.raceRatio t E i =
      t i * winnerResidualClock t a E a /
        (t i * winnerResidualClock t a E a +
          winnerResidualClock t a E i) := by
  unfold SharedRace.raceRatio
  rw [rawRaceMin_eq_of_strictClockWin t E a ha]
  exact weighted_ratio_loser_eq_residual t ht a i hi E

private lemma measurable_clockArgmin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (t : κ → ℝ) : Measurable (SharedRace.clockArgmin t) := by
  unfold SharedRace.clockArgmin
  apply measurable_lexMax
  intro i
  change Measurable (fun E : κ → ℝ => -(E i / t i))
  fun_prop

private lemma measurable_rawRaceMin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (SharedRace.rawRaceMin t) := by
  letI : MeasurableSpace κ := ⊤
  let a : (κ → ℝ) → κ := SharedRace.clockArgmin t
  let v : (κ → ℝ) → ℝ := fun E =>
    ∑ i, if a E = i then E i / t i else 0
  have ha : Measurable a := measurable_clockArgmin_fixed t
  have hv : Measurable v := by
    dsimp only [v]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite
      (measurableSet_singleton i |>.preimage ha)
      (by
        change Measurable (fun E : κ → ℝ => E i / t i)
        fun_prop)
      measurable_const
  have heq : SharedRace.rawRaceMin t = v := by
    funext E
    unfold SharedRace.rawRaceMin
    dsimp only [v, a]
    simp
  rw [heq]
  exact hv

private lemma measurable_normRaceMin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (SharedRace.normRaceMin t) := by
  unfold SharedRace.normRaceMin
  exact (measurable_rawRaceMin_fixed t).div SharedRace.measurable_clockTotal

private lemma measurable_raceRatio_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) : Measurable (fun E => SharedRace.raceRatio t E i) := by
  unfold SharedRace.raceRatio
  exact ((measurable_rawRaceMin_fixed t).mul measurable_const).div
    (measurable_pi_apply i)

namespace SharedRace

/-- The one-coordinate moment whose finite sum controls the normalized race
partition function.-/
noncomputable def clockCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) (E : κ → ℝ) : ℝ :=
  raceRatio t E i ^ 2 *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
      (normClock E i - normRaceMin t E))

/--
@isnad1 id=measurab.0h3v.s5.875cda0d4c1b from=translated src=- shape=1a1ee15a vocab=a409103e
-/
lemma measurable_clockCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) : Measurable (clockCoordinateIntegrand t i) := by
  unfold clockCoordinateIntegrand normClock
  exact ((measurable_raceRatio_fixed t i).pow_const 2).mul
    (Real.measurable_exp.comp
      (measurable_const.mul
        (((measurable_pi_apply i).div measurable_clockTotal).sub
          (measurable_normRaceMin_fixed t))))

/-- The one-coordinate normalized race moment is integrable.  The proof uses
only positivity of the clocks and the uniform bounds `raceRatio ≤ 1` and
`normClock ≤ 1`.
@isnad1 id=integrab.1h3v.s6.4c0289004c37 from=translated src=- shape=b28bf69e vocab=74d6b053
-/
theorem clockCoordinateIntegrand_integrable
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (i : κ) :
    Integrable (clockCoordinateIntegrand t i) (clockLaw κ) := by
  let C : ℝ := Real.exp
    ((Fintype.card κ : ℝ) * SharedRace.logTwo)
  have hstrong : AEStronglyMeasurable
      (clockCoordinateIntegrand t i) (clockLaw κ) :=
    (measurable_clockCoordinateIntegrand t i).aestronglyMeasurable
  apply Integrable.of_bound hstrong C
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hratio0 : 0 < raceRatio t E i := raceRatio_pos t E ht hE i
  have hratio1 : raceRatio t E i ≤ 1 := raceRatio_le_one t E ht hE i
  have hsq : raceRatio t E i ^ 2 ≤ 1 := by nlinarith
  have hmin0 : 0 ≤ normRaceMin t E := by
    unfold normRaceMin
    exact div_nonneg (rawRaceMin_pos t E ht hE).le (clockTotal_pos E hE).le
  have hcoord1 : normClock E i ≤ 1 := normClock_le_one E hE i
  have hdiff : normClock E i - normRaceMin t E ≤ 1 := by linarith
  have hc0 : 0 ≤ (Fintype.card κ : ℝ) * SharedRace.logTwo :=
    mul_nonneg (by positivity) SharedRace.L_pos.le
  have hexp :
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
          (normClock E i - normRaceMin t E)) ≤ C := by
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right hc0 hdiff
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)).trans
      (by simpa only [one_mul] using hexp)
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)

end SharedRace

private lemma strictClockWin_measurableSet
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
  unfold strictClockWin
  measurability

private lemma strictClockWin_pairwise_disjoint
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) : Pairwise fun a b : κ => Disjoint
      {E : κ → ℝ | strictClockWin t a E}
      {E : κ → ℝ | strictClockWin t b E} := by
  intro a b hab
  rw [Set.disjoint_left]
  intro E ha hb
  have hab' := ha b hab.symm
  have hba' := hb a hab
  linarith

/-- The strict winner cells exhaust iid exponential clocks up to a null set.
This is the measure-level partition used by all subsequent cellwise moment
identities.-/
private theorem clockLaw_eq_sum_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1) :
    clockLaw κ = Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin t a E} := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (clockLaw κ) := by
    unfold clockLaw
    infer_instance
  let S : κ → Set (κ → ℝ) := fun a => {E | strictClockWin t a E}
  have hS (a : κ) : MeasurableSet (S a) :=
    strictClockWin_measurableSet t a
  have hdisj : Pairwise fun a b => Disjoint (S a) (S b) :=
    strictClockWin_pairwise_disjoint t
  have hcell (a : κ) : clockLaw κ (S a) = ENNReal.ofReal (t a) := by
    unfold clockLaw S
    exact pi_exp_strictClockWin t ht htotal a
  have hmass : clockLaw κ (⋃ a, S a) = 1 := by
    rw [measure_iUnion hdisj hS, tsum_fintype]
    simp_rw [hcell]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (ht a).le), htotal]
    norm_num
  have hUnion : ∀ᵐ E ∂(clockLaw κ), E ∈ ⋃ a, S a :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hS)).2 hmass
  calc
    clockLaw κ = (clockLaw κ).restrict (⋃ a, S a) :=
      (Measure.restrict_eq_self_of_ae_mem hUnion).symm
    _ = Measure.sum fun a : κ => (clockLaw κ).restrict (S a) :=
      Measure.restrict_iUnion hdisj hS

private lemma integral_clock_eq_sum_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (f : (κ → ℝ) → ℝ) (hf : Integrable f (clockLaw κ)) :
    (∫ E, f E ∂(clockLaw κ)) =
      ∑ a, ∫ E, f E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E}) := by
  have hdecomp := clockLaw_eq_sum_restrict_strictClockWin t ht htotal
  have hsumInt : Integrable f (Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin t a E}) := by
    rw [← hdecomp]
    exact hf
  calc
    (∫ E, f E ∂(clockLaw κ)) =
        ∫ E, f E ∂(Measure.sum fun a : κ =>
          (clockLaw κ).restrict {E | strictClockWin t a E}) :=
      congrArg (fun μ : Measure (κ → ℝ) => ∫ E, f E ∂μ) hdecomp
    _ = ∑ a, ∫ E, f E
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) := by
      simpa only [tsum_fintype] using integral_sum_measure hsumInt

/-- Integrating a measurable residual-clock statistic on one strict winner
cell gives the winner mass times its expectation under fresh iid clocks.-/
private lemma integral_comp_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (f : (κ → ℝ) → ℝ) (hf : Measurable f) :
    (∫ E, f (winnerResidualClock t a E)
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * ∫ W, f W ∂(clockLaw κ) := by
  have hmap := winnerResidualClock_restrict_law t ht htotal a
  calc
    (∫ E, f (winnerResidualClock t a E)
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ W, f W ∂Measure.map (winnerResidualClock t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      (integral_map (winnerResidualClock_measurable t a).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = ∫ W, f W ∂ENNReal.ofReal (t a) • clockLaw κ := by rw [hmap]
    _ = (ENNReal.ofReal (t a)).toReal • ∫ W, f W ∂clockLaw κ := by
      rw [integral_smul_measure]
    _ = t a * ∫ W, f W ∂clockLaw κ := by
      rw [ENNReal.toReal_ofReal (ht a).le]
      rfl

/-- Integrability companion to `integral_comp_winnerResidualClock`.-/
private lemma integrable_comp_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (f : (κ → ℝ) → ℝ) (hf : Integrable f (clockLaw κ)) :
    Integrable (fun E => f (winnerResidualClock t a E))
      ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
  have hmap := winnerResidualClock_restrict_law t ht htotal a
  have hscaled : Integrable f (ENNReal.ofReal (t a) • clockLaw κ) :=
    hf.smul_measure (by simp)
  rw [← hmap] at hscaled
  exact hscaled.comp_measurable (winnerResidualClock_measurable t a)

private lemma clockCoordinateIntegrand_winner_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) (hE : ∀ i, 0 < E i)
    (ha : strictClockWin t a E) :
    SharedRace.clockCoordinateIntegrand t a E =
      Real.exp ((-SharedRace.logTwo * (1 - t a)) *
        ((Fintype.card κ : ℝ) *
          SharedRace.normClock (winnerResidualClock t a E) a)) := by
  have hratio : SharedRace.raceRatio t E a = 1 := by
    unfold SharedRace.raceRatio
    rw [rawRaceMin_eq_of_strictClockWin t E a ha]
    field_simp [(ht a).ne', (hE a).ne']
  rw [SharedRace.clockCoordinateIntegrand, hratio, one_pow, one_mul,
    normClock_winner_eq_residual t ht htotal a E,
    normRaceMin_eq_residual t ht htotal a E ha]
  congr 1
  ring

/-- Exact winning-cell contribution to the one-coordinate moment.-/
private theorem clockCoordinate_winnerCell_integral_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E, SharedRace.clockCoordinateIntegrand t a E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * SharedRace.betaOneExpMoment (Fintype.card κ)
        (-SharedRace.logTwo * (1 - t a)) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    Real.exp ((-SharedRace.logTwo * (1 - t a)) *
      ((Fintype.card κ : ℝ) * SharedRace.normClock W a))
  have hf : Measurable f := by
    dsimp only [f]
    exact Real.measurable_exp.comp
      (measurable_const.mul
        (measurable_const.mul (SharedRace.measurable_normClock a)))
  have hpoint :
      (fun E => SharedRace.clockCoordinateIntegrand t a E) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => f (winnerResidualClock t a E) := by
    filter_upwards [ae_restrict_of_ae (SharedRace.ae_clockLaw_pos (κ := κ)),
      ae_restrict_mem (strictClockWin_measurableSet t a)] with E hE ha
    exact clockCoordinateIntegrand_winner_eq t ht htotal a E hE ha
  calc
    (∫ E, SharedRace.clockCoordinateIntegrand t a E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, f (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a f hf
    _ = t a * SharedRace.betaOneExpMoment (Fintype.card κ)
          (-SharedRace.logTwo * (1 - t a)) := by
      congr 1
      exact SharedRace.clockLaw_scaledNormClock_expMoment_eq a hk
        (-SharedRace.logTwo * (1 - t a))

/-- Exact winning normalized-clock first moment on one strict winner cell.
This is retained for the later row identity
`E[U_argmin] = (sum_i t_i^2) / k`.-/
private theorem normClock_winnerCell_integral_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    (∫ E, SharedRace.normClock E a
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a ^ 2 / (Fintype.card κ : ℝ) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    t a * SharedRace.normClock W a
  have hf : Measurable f :=
    measurable_const.mul (SharedRace.measurable_normClock a)
  have hpoint :
      (fun E => SharedRace.normClock E a) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => f (winnerResidualClock t a E) := by
    filter_upwards [] with E
    exact normClock_winner_eq_residual t ht htotal a E
  calc
    (∫ E, SharedRace.normClock E a
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, f (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a f hf
    _ = t a * (t a * ∫ W, SharedRace.normClock W a ∂clockLaw κ) := by
      rw [integral_const_mul]
    _ = t a * (t a * (1 / (Fintype.card κ : ℝ))) := by
      rw [SharedRace.integral_normClock a]
    _ = t a ^ 2 / (Fintype.card κ : ℝ) := by ring

private lemma measurable_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable
      (fun E : κ → ℝ =>
        SharedRace.normClock E (SharedRace.clockArgmin t E)) := by
  letI : MeasurableSpace κ := ⊤
  let a : (κ → ℝ) → κ := SharedRace.clockArgmin t
  let f : (κ → ℝ) → ℝ := fun E =>
    ∑ i, if a E = i then SharedRace.normClock E i else 0
  have ha : Measurable a := measurable_clockArgmin_fixed t
  have hf : Measurable f := by
    dsimp only [f]
    apply Finset.measurable_sum
    intro i _hi
    exact Measurable.ite
      (measurableSet_singleton i |>.preimage ha)
      (SharedRace.measurable_normClock i) measurable_const
  have heq : (fun E : κ → ℝ =>
      SharedRace.normClock E (SharedRace.clockArgmin t E)) = f := by
    funext E
    dsimp only [f, a]
    simp
  rw [heq]
  exact hf

private lemma integrable_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Integrable
      (fun E : κ → ℝ =>
        SharedRace.normClock E (SharedRace.clockArgmin t E))
      (clockLaw κ) := by
  apply Integrable.of_bound
    (measurable_normClock_clockArgmin t).aestronglyMeasurable 1
  filter_upwards [SharedRace.ae_clockLaw_pos (κ := κ)] with E hE
  have hnonneg : 0 ≤
      SharedRace.normClock E (SharedRace.clockArgmin t E) :=
    SharedRace.normClock_nonneg E hE (SharedRace.clockArgmin t E)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact SharedRace.normClock_le_one E hE (SharedRace.clockArgmin t E)

namespace SharedRace

/-- The normalized clock selected by a positive PMF race has first moment
`(sum_i r_i^2) / k`.  This is the row moment needed by the reference-loss
assembly.
@isnad1 id=eq.2h2v.s7.1185822dfe99 from=translated src=- shape=5c1b18e4 vocab=8c768feb
-/
theorem integral_normClock_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1) :
    (∫ E : κ → ℝ, normClock E (clockArgmin r E) ∂clockLaw κ) =
      (∑ i, r i ^ 2) / (Fintype.card κ : ℝ) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => normClock E (clockArgmin r E))
    (integrable_normClock_clockArgmin r)]
  apply (Finset.sum_congr rfl fun a _ => ?_).trans
    (Finset.sum_div (s := (univ : Finset κ))
      (f := fun a => r a ^ 2) (Fintype.card κ : ℝ)).symm
  calc
    (∫ E : κ → ℝ, normClock E (clockArgmin r E)
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ E : κ → ℝ, normClock E a
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin]
    _ = r a ^ 2 / (Fintype.card κ : ℝ) :=
      normClock_winnerCell_integral_eq r hr hrtotal a

private lemma integrable_normRaceMin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a : κ) :
    Integrable (normRaceMin π)
      ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
  have hcomp := integrable_comp_winnerResidualClock π hπ hπtotal a
    (fun W : κ → ℝ => normClock W a) (integrable_normClock a)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
    with E hwin
  rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]

private theorem integral_normRaceMin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a : κ) :
    (∫ E : κ → ℝ, normRaceMin π E
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
      π a / (Fintype.card κ : ℝ) := by
  calc
    (∫ E : κ → ℝ, normRaceMin π E
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
        ∫ E : κ → ℝ, normClock (winnerResidualClock π a E) a
          ∂((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
        with E hwin
      rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]
    _ = π a * ∫ W : κ → ℝ, normClock W a ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a
        (fun W : κ → ℝ => normClock W a) (measurable_normClock a)
    _ = π a * (1 / (Fintype.card κ : ℝ)) := by
      rw [integral_normClock a]
    _ = π a / (Fintype.card κ : ℝ) := by ring

/-- Integrability and exact mean of the normalized weighted race minimum.
@isnad1 id=integrab.2h2v.s6.9d355b72610b from=translated src=- shape=549bc01c vocab=c23f6d1c
-/
theorem integrable_normRaceMin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    Integrable (normRaceMin π) (clockLaw κ) := by
  have hsum : Integrable (normRaceMin π)
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin π a E}) :=
    integrable_sum_measure
      (fun a => integrable_normRaceMin_cell π hπ hπtotal a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin π hπ hπtotal] at hsum
  exact hsum

/--
@isnad1 id=eq.2h2v.s6.309adb9e30b8 from=translated src=- shape=3996f718 vocab=405049c4
-/
theorem integral_normRaceMin_eq_inv_card
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, normRaceMin π E ∂clockLaw κ) =
      1 / (Fintype.card κ : ℝ) := by
  rw [integral_clock_eq_sum_strictClockWin π hπ hπtotal
    (normRaceMin π) (integrable_normRaceMin π hπ hπtotal)]
  simp_rw [integral_normRaceMin_cell_eq π hπ hπtotal]
  rw [← Finset.sum_div, hπtotal]

private lemma integrable_log_normRaceMin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
  have hcomp := integrable_comp_winnerResidualClock π hπ hπtotal a
    (fun W : κ → ℝ => Real.log (normClock W a))
    (integrable_log_normClock a hk)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
    with E hwin
  rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]

private theorem integral_log_normRaceMin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E : κ → ℝ, Real.log (normRaceMin π E)
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
      π a * normClockLogIntegral (Fintype.card κ) := by
  calc
    (∫ E : κ → ℝ, Real.log (normRaceMin π E)
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
        ∫ E : κ → ℝ,
          Real.log (normClock (winnerResidualClock π a E) a)
          ∂((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
        with E hwin
      rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]
    _ = π a * ∫ W : κ → ℝ, Real.log (normClock W a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a
        (fun W : κ → ℝ => Real.log (normClock W a))
        (Real.measurable_log.comp (measurable_normClock a))
    _ = π a * normClockLogIntegral (Fintype.card κ) := by
      rw [integral_log_normClock_eq_normClockLogIntegral a hk]

/-- The normalized minimum of a positive PMF race has the same logarithmic
mean as any normalized iid clock coordinate.
@isnad1 id=integrab.3h2v.s6.53f887d608e8 from=translated src=- shape=69fc97b8 vocab=b8490cd5
-/
theorem integrable_log_normRaceMin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      (clockLaw κ) := by
  have hsum : Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin π a E}) :=
    integrable_sum_measure
      (fun a => integrable_log_normRaceMin_cell π hπ hπtotal hk a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin π hπ hπtotal] at hsum
  exact hsum

/--
@isnad1 id=eq.3h2v.s6.c45ea1b4ee74 from=translated src=- shape=f03f7425 vocab=25063366
-/
theorem integral_log_normRaceMin_eq_normClockLogIntegral
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normRaceMin π E) ∂clockLaw κ) =
      normClockLogIntegral (Fintype.card κ) := by
  rw [integral_clock_eq_sum_strictClockWin π hπ hπtotal
    (fun E : κ → ℝ => Real.log (normRaceMin π E))
    (integrable_log_normRaceMin π hπ hπtotal hk)]
  simp_rw [integral_log_normRaceMin_cell_eq π hπ hπtotal hk]
  rw [← Finset.sum_mul, hπtotal, one_mul]

private lemma integrable_log_mul_normClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (c : ℝ) (hc : 0 < c) (a : κ) (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun W : κ → ℝ => Real.log (c * normClock W a))
      (clockLaw κ) := by
  have heq : (fun W : κ → ℝ => Real.log (c * normClock W a)) =ᵐ[clockLaw κ]
      fun W => Real.log c + Real.log (normClock W a) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
    rw [Real.log_mul hc.ne'
      ((normClock_nonneg W hW a).lt_of_ne' (by
        unfold normClock
        exact div_ne_zero (hW a).ne' (clockTotal_pos W hW).ne')).ne']
  have hconst : Integrable (fun _ : κ → ℝ => Real.log c) (clockLaw κ) :=
    integrable_const (Real.log c)
  exact (hconst.add (integrable_log_normClock a hk)).congr heq.symm

private lemma integral_log_mul_normClock_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (c : ℝ) (hc : 0 < c) (a : κ) (hk : 2 ≤ Fintype.card κ) :
    (∫ W : κ → ℝ, Real.log (c * normClock W a) ∂clockLaw κ) =
      Real.log c + normClockLogIntegral (Fintype.card κ) := by
  have heq : (fun W : κ → ℝ => Real.log (c * normClock W a)) =ᵐ[clockLaw κ]
      fun W => Real.log c + Real.log (normClock W a) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
    rw [Real.log_mul hc.ne'
      ((normClock_nonneg W hW a).lt_of_ne' (by
        unfold normClock
        exact div_ne_zero (hW a).ne' (clockTotal_pos W hW).ne')).ne']
  have hconst : Integrable (fun _ : κ → ℝ => Real.log c) (clockLaw κ) :=
    integrable_const (Real.log c)
  rw [integral_congr_ae heq,
    integral_add hconst (integrable_log_normClock a hk),
    integral_const,
    integral_log_normClock_eq_normClockLogIntegral a hk]
  simp [Measure.real]

private lemma integrable_log_normClock_argmin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      ((clockLaw κ).restrict {E | strictClockWin r a E}) := by
  have hcomp := integrable_comp_winnerResidualClock r hr hrtotal a
    (fun W : κ → ℝ => Real.log (r a * normClock W a))
    (integrable_log_mul_normClock (r a) (hr a) a hk)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
    with E hwin
  rw [clockArgmin_eq_of_strictClockWin r E a hwin,
    normClock_winner_eq_residual r hr hrtotal a E]

private theorem integral_log_normClock_argmin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
      r a * (Real.log (r a) +
        normClockLogIntegral (Fintype.card κ)) := by
  calc
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ E : κ → ℝ,
          Real.log (r a * normClock (winnerResidualClock r a E) a)
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin,
        normClock_winner_eq_residual r hr hrtotal a E]
    _ = r a * ∫ W : κ → ℝ,
        Real.log (r a * normClock W a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock r hr hrtotal a
        (fun W : κ → ℝ => Real.log (r a * normClock W a))
        (Real.measurable_log.comp
          (measurable_const.mul (measurable_normClock a)))
    _ = r a * (Real.log (r a) +
        normClockLogIntegral (Fintype.card κ)) := by
      rw [integral_log_mul_normClock_eq (r a) (hr a) a hk]

/-- Integrability of the logarithmic normalized winning coordinate.
@isnad1 id=integrab.3h2v.s6.128f44125f16 from=translated src=- shape=de341622 vocab=f38637e4
-/
theorem integrable_log_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      (clockLaw κ) := by
  have hsum : Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin r a E}) :=
    integrable_sum_measure
      (fun a => integrable_log_normClock_argmin_cell r hr hrtotal hk a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin r hr hrtotal] at hsum
  exact hsum

/-- The logarithmic winning-clock row moment.  The universal common clock
moment is left symbolic because it cancels against the normalized race
minimum in the reference ratio.
@isnad1 id=eq.3h2v.s7.84b7e04be716 from=translated src=- shape=8a2712a7 vocab=279d9151
-/
theorem integral_log_normClock_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂clockLaw κ) =
      ∑ i, r i * (Real.log (r i) +
        normClockLogIntegral (Fintype.card κ)) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
    (integrable_log_normClock_clockArgmin r hr hrtotal hk)]
  exact Finset.sum_congr rfl fun a _ =>
    integral_log_normClock_argmin_cell_eq r hr hrtotal hk a

private lemma measurable_log_coordinate_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) : Measurable
      (fun E : κ → ℝ => Real.log (π (clockArgmin r E))) := by
  letI : MeasurableSpace κ := ⊤
  exact (measurable_of_finite fun i : κ => Real.log (π i)).comp
    (measurable_clockArgmin_fixed r)

private lemma integrable_log_coordinate_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) : Integrable
      (fun E : κ → ℝ => Real.log (π (clockArgmin r E)))
      (clockLaw κ) := by
  let C : ℝ := ∑ i, |Real.log (π i)|
  apply Integrable.of_bound
    (measurable_log_coordinate_clockArgmin π r).aestronglyMeasurable C
  filter_upwards [] with E
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (Real.log (π i)))
    (Finset.mem_univ (clockArgmin r E))

private theorem integral_log_coordinate_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1) :
    (∫ E : κ → ℝ, Real.log (π (clockArgmin r E)) ∂clockLaw κ) =
      ∑ i, r i * Real.log (π i) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => Real.log (π (clockArgmin r E)))
    (integrable_log_coordinate_clockArgmin π r)]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∫ E : κ → ℝ, Real.log (π (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ _E : κ → ℝ, Real.log (π a)
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin]
    _ = r a * ∫ _W : κ → ℝ, Real.log (π a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock r hr hrtotal a
        (fun _W : κ → ℝ => Real.log (π a)) measurable_const
    _ = r a * Real.log (π a) := by simp [Measure.real]

private lemma log_raceRatio_clockArgmin_identity
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r E : κ → ℝ) (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    Real.log (raceRatio π E (clockArgmin r E)) =
      Real.log (normRaceMin π E) +
        Real.log (π (clockArgmin r E)) -
          Real.log (normClock E (clockArgmin r E)) := by
  let a : κ := clockArgmin r E
  have hraw : 0 < rawRaceMin π E := rawRaceMin_pos π E hπ hE
  have htotal : 0 < clockTotal E := clockTotal_pos E hE
  have hcoord : 0 < E a := hE a
  have hprior : 0 < π a := hπ a
  change Real.log (raceRatio π E a) =
    Real.log (normRaceMin π E) + Real.log (π a) -
      Real.log (normClock E a)
  unfold raceRatio normRaceMin normClock
  rw [Real.log_div (mul_ne_zero hraw.ne' hprior.ne') hcoord.ne',
    Real.log_mul hraw.ne' hprior.ne',
    Real.log_div hraw.ne' htotal.ne',
    Real.log_div hcoord.ne' htotal.ne']
  ring

/-- The logarithmic reference ratio at the winner of an independent positive
row race is integrable.
@isnad1 id=integrab.5h3v.s7.2fbdef22598a from=translated src=- shape=7805c549 vocab=ebc93f3a
-/
theorem integrable_log_raceRatio_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (raceRatio π E (clockArgmin r E)))
      (clockLaw κ) := by
  have hmin := integrable_log_normRaceMin π hπ hπtotal hk
  have hprior := integrable_log_coordinate_clockArgmin π r
  have hwin := integrable_log_normClock_clockArgmin r hr hrtotal hk
  have hrhs : Integrable (fun E : κ → ℝ =>
      Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E)) -
        Real.log (normClock E (clockArgmin r E))) (clockLaw κ) :=
    (hmin.add hprior).sub hwin
  apply hrhs.congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_raceRatio_clockArgmin_identity π r E hπ hE).symm

/-- Exact row identity for the logarithmic winning reference ratio.  The
common normalized-clock logarithmic moment cancels, leaving the finite
cross-entropy expression.
@isnad1 id=eq.5h3v.s7.c14ccf1ae902 from=translated src=- shape=53d3e9dd vocab=ec521e74
-/
theorem integral_log_raceRatio_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ,
      Real.log (raceRatio π E (clockArgmin r E)) ∂clockLaw κ) =
      ∑ i, r i * Real.log (π i / r i) := by
  have hmin := integrable_log_normRaceMin π hπ hπtotal hk
  have hprior := integrable_log_coordinate_clockArgmin π r
  have hwin := integrable_log_normClock_clockArgmin r hr hrtotal hk
  have hpoint : (fun E : κ → ℝ =>
      Real.log (raceRatio π E (clockArgmin r E))) =ᵐ[clockLaw κ]
      fun E => Real.log (normRaceMin π E) +
        Real.log (π (clockArgmin r E)) -
          Real.log (normClock E (clockArgmin r E)) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    exact log_raceRatio_clockArgmin_identity π r E hπ hE
  have houter :
      (∫ E : κ → ℝ,
        (Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))) -
          Real.log (normClock E (clockArgmin r E)) ∂clockLaw κ) =
        (∫ E : κ → ℝ,
          Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))
          ∂clockLaw κ) -
        ∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
          ∂clockLaw κ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_sub (hmin.add hprior) hwin
  have hinner :
      (∫ E : κ → ℝ,
        Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))
        ∂clockLaw κ) =
        (∫ E : κ → ℝ, Real.log (normRaceMin π E) ∂clockLaw κ) +
        ∫ E : κ → ℝ, Real.log (π (clockArgmin r E)) ∂clockLaw κ := by
    simpa only [Pi.add_apply] using integral_add hmin hprior
  rw [integral_congr_ae hpoint, houter, hinner,
    integral_log_normRaceMin_eq_normClockLogIntegral π hπ hπtotal hk,
    integral_log_coordinate_clockArgmin_eq π r hr hrtotal,
    integral_log_normClock_clockArgmin_eq r hr hrtotal hk]
  have hlog (i : κ) : Real.log (π i / r i) =
      Real.log (π i) - Real.log (r i) :=
    Real.log_div (hπ i).ne' (hr i).ne'
  simp_rw [hlog, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hrtotal, one_mul]
  ring

/-- Measurability of the normalized race partition function.
@isnad1 id=measurab.0h2v.s5.f66554b22080 from=translated src=- shape=52fb1c9f vocab=5e066415
-/
theorem measurable_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) : Measurable (normRaceZ π) := by
  unfold normRaceZ
  apply Finset.measurable_sum
  intro i _hi
  exact ((measurable_raceRatio_fixed π i).pow_const 2).mul
    (Real.measurable_exp.comp
      (measurable_const.mul (measurable_normClock i)))

private lemma one_le_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π E : κ → ℝ) (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    1 ≤ normRaceZ π E := by
  let a : κ := clockArgmin π E
  have hterm : 1 ≤ (raceRatio π E a) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
        normClock E a) := by
    rw [raceRatio_argmin π E hπ hE, one_pow, one_mul]
    apply Real.one_le_exp
    exact mul_nonneg
      (mul_nonneg (by positivity) SharedRace.L_pos.le)
      (normClock_nonneg E hE a)
  exact hterm.trans (Finset.single_le_sum
    (f := fun i => (raceRatio π E i) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
        normClock E i))
    (fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    (Finset.mem_univ a))

/-- The normalized partition-function logarithm is integrable under iid
exponential clocks.
@isnad1 id=integrab.1h2v.s6.b53cf5eb69f2 from=translated src=- shape=7307d1b4 vocab=81193f23
-/
theorem integrable_log_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceZ π E))
      (clockLaw κ) := by
  let B : ℝ := (Fintype.card κ : ℝ) *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo)
  let C : ℝ := Real.log B
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  apply Integrable.of_bound
    (Real.measurable_log.comp (measurable_normRaceZ π)).aestronglyMeasurable C
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hZone : 1 ≤ normRaceZ π E := one_le_normRaceZ π E hπ hE
  have hZpos : 0 < normRaceZ π E := zero_lt_one.trans_le hZone
  have hZle : normRaceZ π E ≤ B := by
    simpa only [B] using normRaceZ_le π E hπ hE
  have hlogle : Real.log (normRaceZ π E) ≤ C := by
    dsimp only [C]
    exact Real.strictMonoOn_log.monotoneOn hZpos hBpos hZle
  change |Real.log (normRaceZ π E)| ≤ C
  rw [abs_of_nonneg (Real.log_nonneg hZone)]
  exact hlogle

/-- Clock-law specialization of the logarithmic tangent, conditional only on
the coordinate estimates supplied by the winner/loser analysis.
@isnad1 id=le.4h2v.s7.c526f0265cf3 from=translated src=- shape=bab09300 vocab=c925fc2d
-/
theorem normalizedRaceLogIntegral_le_of_coordinate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i) :
    (∫ E : κ → ℝ, Real.log (normRaceZ π E) ∂clockLaw κ) ≤
      SharedRace.logTwo := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have htint := integrable_normRaceMin π hπpos hπtotal
  have htmean :
      (∫ E : κ → ℝ, (Fintype.card κ : ℝ) *
        SharedRace.logTwo * normRaceMin π E ∂clockLaw κ) =
        SharedRace.logTwo := by
    rw [integral_const_mul,
      integral_normRaceMin_eq_inv_card π hπpos hπtotal]
    have hkne : (Fintype.card κ : ℝ) ≠ 0 := by positivity
    field_simp [hkne]
  apply normalizedRaceLogIntegral_le (clockLaw κ) π hπ
    (fun E i => raceRatio π E i) (fun E i => normClock E i)
    (normRaceMin π)
  · filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    simpa only [normRaceZ] using normRaceZ_pos π E hπpos hE
  · simpa only [normRaceZ] using integrable_log_normRaceZ π hπpos
  · exact htint
  · exact htmean
  · intro i
    change Integrable (clockCoordinateIntegrand π i) (clockLaw κ)
    exact clockCoordinateIntegrand_integrable π hπpos i
  · intro i
    change (∫ E : κ → ℝ,
      clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i
    exact hcoord i

/-- Integrability of the clock-row reference loss at the row winner.
@isnad1 id=integrab.5h3v.s7.8fa28d3f4c80 from=translated src=- shape=d640e8e8 vocab=1dd7dcc4
-/
theorem integrable_log_inv_referencePMF_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hr : IsPMF r) (hrpos : ∀ i, 0 < r i)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ =>
      Real.log (1 / referencePMF π E (clockArgmin r E)))
      (clockLaw κ) := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have hrtotal : ∑ i, r i = 1 := by simpa [mass] using hr.total
  have hZ := integrable_log_normRaceZ π hπpos
  have hratio := integrable_log_raceRatio_clockArgmin
    π r hπpos hπtotal hrpos hrtotal hk
  have hclock := integrable_normClock_clockArgmin r
  have hrhs : Integrable (fun E : κ → ℝ =>
      Real.log (normRaceZ π E) -
        2 * Real.log (raceRatio π E (clockArgmin r E)) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo *
            normClock E (clockArgmin r E)) (clockLaw κ) :=
    (hZ.sub (hratio.const_mul 2)).sub
      (hclock.const_mul
        ((Fintype.card κ : ℝ) * SharedRace.logTwo))
  apply hrhs.congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_inv_referencePMF π E hπpos hE (clockArgmin r E)).symm

/-- Row-wise reference-loss bound, conditional only on the coordinate
moments.  All logarithmic and winning-clock identities are discharged by the
literal clock law.
@isnad1 id=le.6h3v.s8.2921df663bce from=translated src=- shape=293b38c6 vocab=c7f1092b
-/
theorem referenceLossIntegral_le_of_coordinate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hr : IsPMF r) (hrpos : ∀ i, 0 < r i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i) :
    (∫ E : κ → ℝ,
      Real.log (1 / referencePMF π E (clockArgmin r E)) ∂clockLaw κ) ≤
      2 * (∑ i, r i * Real.log (r i / π i)) +
        SharedRace.logTwo * (1 - ∑ i, r i ^ 2) := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have hrtotal : ∑ i, r i = 1 := by simpa [mass] using hr.total
  apply referenceLossIntegral_le (clockLaw κ) π r id (clockArgmin r)
    hπpos (ae_clockLaw_pos (κ := κ))
    (integrable_log_normRaceZ π hπpos)
    (integrable_log_raceRatio_clockArgmin
      π r hπpos hπtotal hrpos hrtotal hk)
    (integrable_normClock_clockArgmin r)
    (normalizedRaceLogIntegral_le_of_coordinate π hπ hπpos hk hcoord)
  · simpa only [id_eq] using
      integral_log_raceRatio_clockArgmin_eq
        π r hπpos hπtotal hrpos hrtotal hk
  · simpa only [id_eq] using
      integral_normClock_clockArgmin_eq r hrpos hrtotal

private lemma lexMax_eq_of_le_iff
    {Ω Ω' ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Ω → ι → ℝ) (G : Ω' → ι → ℝ) (ω : Ω) (ω' : Ω')
    (hord : ∀ a b, F ω a ≤ F ω b ↔ G ω' a ≤ G ω' b) :
    lexMax F ω = lexMax G ω' := by
  let a : ι := lexMax G ω'
  apply (lexMax_eq_iff F ω a).2
  have ha : List.argmax (G ω') Finset.univ.toList = some a :=
    (lexMax_eq_iff G ω' a).1 rfl
  rw [List.argmax_eq_some_iff] at ha ⊢
  refine ⟨ha.1, ?_, ?_⟩
  · intro b hb
    exact (hord b a).2 (ha.2.1 b hb)
  · intro b hb hFab
    exact ha.2.2 b hb ((hord a b).1 hFab)

/-- The shared lexicographic tie-break is preserved exactly by the
exponential-clock/Gumbel change of variables.
@isnad1 id=eq.2h3v.s6.5be70813d23b from=translated src=- shape=a3bcb253 vocab=28de09b8
-/
theorem weightedLexWinner_clock_eq_argmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (ht : ∀ i, 0 < t i) (hE : ∀ i, 0 < E i) :
    weightedLexWinner t (fun i => -Real.log (E i)) = clockArgmin t E := by
  let Fs : (κ → ℝ) → κ → ℝ := fun G i => Real.log (t i) + G i
  let Fc : (κ → ℝ) → κ → ℝ := fun W i => -(W i / t i)
  change lexMax Fs (fun i => -Real.log (E i)) = lexMax Fc E
  apply lexMax_eq_of_le_iff Fs Fc (fun i => -Real.log (E i)) E
  intro a b
  have hscore (i : κ) :
      Fs (fun j => -Real.log (E j)) i = -Real.log (E i / t i) := by
    dsimp only [Fs]
    rw [Real.log_div (hE i).ne' (ht i).ne']
    ring
  have hra (i : κ) : 0 < E i / t i := div_pos (hE i) (ht i)
  rw [hscore a, hscore b]
  change -Real.log (E a / t a) ≤ -Real.log (E b / t b) ↔
    -(E a / t a) ≤ -(E b / t b)
  rw [neg_le_neg_iff, neg_le_neg_iff]
  exact Real.strictMonoOn_log.le_iff_le (hra b) (hra a)

private lemma measurable_sharedEntropy_integrand
    {Ω : Type u} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (μ : Ω → ℝ) (r : Ω → κ → ℝ) :
    Measurable (fun G : κ → ℝ => H (push (sharedWinner r G) μ)) := by
  letI : MeasurableSpace κ := ⊤
  let A : (κ → ℝ) → (Ω → κ) := fun G z => sharedWinner r G z
  let F : (Ω → κ) → ℝ := fun a => H (push a μ)
  have hA : Measurable A := by
    apply measurable_pi_lambda
    intro z
    dsimp only [A, sharedWinner, weightedLexWinner]
    apply measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  have hF : Measurable F := measurable_of_finite F
  exact hF.comp hA

/-- The Gumbel and exponential-clock formulations of shared-race entropy
agree.  Positivity is needed only on posterior rows in the source support.
@isnad1 id=eq.1h4v.s6.4ec59b201644 from=translated src=- shape=c5d3ebf7 vocab=494327f5
-/
theorem sharedRaceEntropy_eq_clockSharedRaceEntropy
    {Ω : Type u} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r = clockSharedRaceEntropy μ r := by
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hg : AEStronglyMeasurable
      (fun G : κ → ℝ => H (push (sharedWinner r G) μ)) (seedLaw κ) :=
    (measurable_sharedEntropy_integrand μ r).aestronglyMeasurable
  have hpush : ∀ᵐ E ∂clockLaw κ,
      push (sharedWinner r (F E)) μ =
        push (fun z => clockArgmin (r z) E) μ := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    funext i
    unfold push
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hz : μ z = 0
    · simp [hz]
    · have hw := weightedLexWinner_clock_eq_argmin
        (r z) E (hrpos z hz) hE
      have heq : sharedWinner r (F E) z = clockArgmin (r z) E := by
        simpa only [sharedWinner, F] using hw
      rw [heq]
  unfold sharedRaceEntropy clockSharedRaceEntropy seedLaw
  rw [integral_map hF.aemeasurable hg]
  apply integral_congr_ae
  filter_upwards [hpush] with E hE
  rw [hE]

end SharedRace

private lemma winnerResidualClock_pos
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) (E : κ → ℝ)
    (hE : ∀ i, 0 < E i) (ha : strictClockWin t a E) :
    ∀ i, 0 < winnerResidualClock t a E i := by
  intro i
  by_cases hi : i = a
  · subst i
    rw [winnerResidualClock_apply_winner]
    exact div_pos (hE a) (ht a)
  · have hstrict := ha i hi
    have hscaled : (E a / t a) * t i < E i :=
      (lt_div_iff₀ (ht i)).mp hstrict
    rw [winnerResidualClock_apply_loser t a i hi E]
    nlinarith

private lemma pmf_coordinate_lt_one_of_ne
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (i a : κ) (hia : a ≠ i) : t i < 1 := by
  have haMem : a ∈ (univ : Finset κ).erase i := by simp [hia]
  have haLe : t a ≤ ∑ b ∈ (univ : Finset κ).erase i, t b :=
    Finset.single_le_sum (fun b _ => (ht b).le) haMem
  have hrest : 0 < ∑ b ∈ (univ : Finset κ).erase i, t b :=
    (ht a).trans_le haLe
  have hsplit := Finset.sum_erase_add (univ : Finset κ) t
    (Finset.mem_univ i)
  rw [htotal] at hsplit
  linarith

private lemma mobius_pairRatio
    {p u v : ℝ} (hp : 0 < p) (hu : 0 < u) (hv : 0 < v) :
    SharedRace.mobius p (u / (u + v)) =
      p * u / (p * u + v) := by
  have huv : 0 < u + v := add_pos hu hv
  have hpv : 0 < p * u + v := add_pos (mul_pos hp hu) hv
  have hforward :
      p * (u / (u + v)) + 1 - u / (u + v) =
        (p * u + v) / (u + v) := by
    field_simp [huv.ne']
    ring
  unfold SharedRace.mobius
  rw [hforward]
  field_simp [huv.ne', hpv.ne']

private lemma loser_normalized_difference_identity
    {p u v s : ℝ} (hp : 0 < p) (hu : 0 < u) (hv : 0 < v)
    (hs : 0 < s) :
    (p * u + v) / s - u / s =
      ((u + v) / s) *
        ((p - p * u / (p * u + v)) /
          (p + (1 - p) * (p * u / (p * u + v)))) := by
  have huv : 0 < u + v := add_pos hu hv
  have hpv : 0 < p * u + v := add_pos (mul_pos hp hu) hv
  have hqden :
      p + (1 - p) * (p * u / (p * u + v)) =
        p * (u + v) / (p * u + v) := by
    field_simp [hpv.ne']
    ring
  have hqdenPos : 0 < p + (1 - p) * (p * u / (p * u + v)) := by
    rw [hqden]
    positivity
  rw [hqden]
  field_simp [hs.ne', hpv.ne', huv.ne', hp.ne']

/-- Pointwise form of a losing coordinate after the fixed-winner residual
transformation.  The split of the two distinguished fresh clocks is sent
through the Möbius map, while their normalized sum carries the shape-two
beta exponent.-/
private lemma clockCoordinateIntegrand_loser_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hai : a ≠ i) (E : κ → ℝ) (hE : ∀ j, 0 < E j)
    (ha : strictClockWin t a E) :
    SharedRace.clockCoordinateIntegrand t i E =
      let W := winnerResidualClock t a E
      let v := W a / (W a + W i)
      let x := SharedRace.mobius (t i) v
      x ^ 2 * Real.exp
        ((Fintype.card κ : ℝ) *
          ((W a + W i) / SharedRace.clockTotal W) *
            SharedRace.loserExponent (t i) x) := by
  let W : κ → ℝ := winnerResidualClock t a E
  let v : ℝ := W a / (W a + W i)
  let x : ℝ := SharedRace.mobius (t i) v
  have hW : ∀ j, 0 < W j :=
    winnerResidualClock_pos t ht a E hE ha
  have hx : x = t i * W a / (t i * W a + W i) := by
    dsimp only [x, v]
    exact mobius_pairRatio (ht i) (hW a) (hW i)
  have hratio : SharedRace.raceRatio t E i = x := by
    rw [raceRatio_loser_eq_residual t ht a i hai.symm E ha]
    exact hx.symm
  have htotalW : 0 < SharedRace.clockTotal W :=
    SharedRace.clockTotal_pos W hW
  have hdiff :
      SharedRace.normClock E i - SharedRace.normRaceMin t E =
        ((W a + W i) / SharedRace.clockTotal W) *
          ((t i - x) / (t i + (1 - t i) * x)) := by
    rw [normClock_loser_eq_residual t ht htotal a i hai.symm E,
      normRaceMin_eq_residual t ht htotal a E ha]
    unfold SharedRace.normClock
    change
      (t i * W a + W i) / SharedRace.clockTotal W -
          W a / SharedRace.clockTotal W = _
    calc
      (t i * W a + W i) / SharedRace.clockTotal W -
          W a / SharedRace.clockTotal W =
          ((W a + W i) / SharedRace.clockTotal W) *
            ((t i - t i * W a / (t i * W a + W i)) /
              (t i + (1 - t i) *
                (t i * W a / (t i * W a + W i)))) :=
        loser_normalized_difference_identity (ht i) (hW a) (hW i) htotalW
      _ = ((W a + W i) / SharedRace.clockTotal W) *
          ((t i - x) / (t i + (1 - t i) * x)) := by rw [hx]
  dsimp only
  rw [SharedRace.clockCoordinateIntegrand, hratio, hdiff]
  unfold SharedRace.loserExponent
  congr 2
  ring

/-- Fresh-clock integrand common to every losing winner cell for a fixed
target coordinate.-/
private noncomputable def freshLoserCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (W : κ → ℝ) : ℝ :=
  let v := W a / (W a + W i)
  let x := SharedRace.mobius p v
  x ^ 2 * Real.exp
    ((Fintype.card κ : ℝ) *
      ((W a + W i) / SharedRace.clockTotal W) *
        SharedRace.loserExponent p x)

private lemma pairMobiusIntegrand_comp_eq_freshLoser
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (W : κ → ℝ) :
    SharedRace.pairMobiusIntegrand p
        ((Fintype.card κ : ℝ) * (W a + W i) /
            SharedRace.clockTotal W,
          W a / (W a + W i)) =
      freshLoserCoordinateIntegrand p a i W := by
  unfold SharedRace.pairMobiusIntegrand
    freshLoserCoordinateIntegrand
  dsimp only
  congr 2
  ring

private lemma measurable_freshLoserCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) : Measurable (freshLoserCoordinateIntegrand p a i) := by
  let v : (κ → ℝ) → ℝ := fun W => W a / (W a + W i)
  let x : (κ → ℝ) → ℝ := fun W => SharedRace.mobius p (v W)
  have hv : Measurable v := by
    dsimp only [v]
    fun_prop
  have hx : Measurable x := by
    dsimp only [x]
    unfold SharedRace.mobius
    fun_prop
  have hpair : Measurable (fun W : κ → ℝ =>
      (W a + W i) / SharedRace.clockTotal W) :=
    ((measurable_pi_apply a).add (measurable_pi_apply i)).div
      SharedRace.measurable_clockTotal
  have hloser : Measurable (fun W =>
      SharedRace.loserExponent p (x W)) := by
    unfold SharedRace.loserExponent
    fun_prop
  have hexponent : Measurable (fun W =>
      (Fintype.card κ : ℝ) *
        ((W a + W i) / SharedRace.clockTotal W) *
          SharedRace.loserExponent p (x W)) :=
    (measurable_const.mul hpair).mul hloser
  unfold freshLoserCoordinateIntegrand
  change Measurable (fun W => x W ^ 2 * Real.exp
    ((Fintype.card κ : ℝ) *
      ((W a + W i) / SharedRace.clockTotal W) *
        SharedRace.loserExponent p (x W)))
  exact (hx.pow_const 2).mul (Real.measurable_exp.comp hexponent)

/-- Exact fresh losing-pair moment in the nondegenerate `k ≥ 3` branch.-/
private theorem integral_freshLoserCoordinate_eq_beta
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (a i : κ) (hai : a ≠ i) (hk : 3 ≤ Fintype.card κ) :
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserBetaIntegrand (Fintype.card κ) p
          (SharedRace.mobius p v) := by
  calc
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
        ∫ W, SharedRace.pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W i) /
              SharedRace.clockTotal W,
            W a / (W a + W i)) ∂clockLaw κ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun W =>
        (pairMobiusIntegrand_comp_eq_freshLoser p a i W).symm
    _ = _ :=
      SharedRace.integral_pairMobiusIntegrand_clockLaw_eq_beta
        a i hai hk hp0 hp1

/-- Exact fresh losing-pair moment in the degenerate two-label branch.-/
private theorem integral_freshLoserCoordinate_eq_degenerate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (hai : a ≠ i) (hk : Fintype.card κ = 2) :
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserDegenerateIntegrand p
          (SharedRace.mobius p v) := by
  calc
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
        ∫ W, SharedRace.pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W i) /
              SharedRace.clockTotal W,
            W a / (W a + W i)) ∂clockLaw κ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun W =>
        (pairMobiusIntegrand_comp_eq_freshLoser p a i W).symm
    _ = _ :=
      SharedRace.integral_pairMobiusIntegrand_clockLaw_eq_degenerate
        a i hai hk p

private theorem clockCoordinate_loserCell_integral_eq_fresh
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hai : a ≠ i) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * ∫ W, freshLoserCoordinateIntegrand (t i) a i W
        ∂clockLaw κ := by
  have hpoint :
      (fun E => SharedRace.clockCoordinateIntegrand t i E) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => freshLoserCoordinateIntegrand (t i) a i
        (winnerResidualClock t a E) := by
    filter_upwards [ae_restrict_of_ae (SharedRace.ae_clockLaw_pos (κ := κ)),
      ae_restrict_mem (strictClockWin_measurableSet t a)] with E hE ha
    simpa only [freshLoserCoordinateIntegrand] using
      clockCoordinateIntegrand_loser_eq t ht htotal a i hai E hE ha
  calc
    (∫ E, SharedRace.clockCoordinateIntegrand t i E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, freshLoserCoordinateIntegrand (t i) a i
            (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, freshLoserCoordinateIntegrand (t i) a i W
          ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a
        (freshLoserCoordinateIntegrand (t i) a i)
        (measurable_freshLoserCoordinateIntegrand (t i) a i)

/-- Finite winner-cell bookkeeping for a coordinate, once the common fresh
loser moment has been identified.-/
private theorem clockCoordinate_integral_eq_of_loserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 2 ≤ Fintype.card κ) (i : κ) (J : ℝ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) = J) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) =
      t i * SharedRace.betaOneExpMoment (Fintype.card κ)
          (-SharedRace.logTwo * (1 - t i)) +
        (1 - t i) * J := by
  have hpartition := integral_clock_eq_sum_strictClockWin t ht htotal
    (SharedRace.clockCoordinateIntegrand t i)
    (SharedRace.clockCoordinateIntegrand_integrable t ht i)
  have hiMem : i ∈ (univ : Finset κ) := Finset.mem_univ i
  have hsplit := Finset.sum_erase_add (univ : Finset κ)
    (fun a => ∫ E, SharedRace.clockCoordinateIntegrand t i E
      ∂((clockLaw κ).restrict {E | strictClockWin t a E})) hiMem
  have hloserSum :
      (∑ a ∈ (univ : Finset κ).erase i,
        ∫ E, SharedRace.clockCoordinateIntegrand t i E
          ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        (∑ a ∈ (univ : Finset κ).erase i, t a) * J := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp ha).1
    rw [clockCoordinate_loserCell_integral_eq_fresh t ht htotal a i hai,
      hJ a hai]
  have htErase : (∑ a ∈ (univ : Finset κ).erase i, t a) = 1 - t i := by
    have h := Finset.sum_erase_add (univ : Finset κ) t hiMem
    rw [htotal] at h
    linarith
  rw [hpartition, ← hsplit, hloserSum, htErase,
    clockCoordinate_winnerCell_integral_eq t ht htotal hk i]
  ring

/-- Once the fresh losing pair has the shape-two beta integral, the scalar
allocation theorem closes the coordinate estimate for `k ≥ 3`.-/
private theorem clockCoordinate_integral_le_of_betaLoserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 3 ≤ Fintype.card κ) (i : κ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) =
        ∫ v : ℝ in 0..1,
          SharedRace.loserBetaIntegrand (Fintype.card κ) (t i)
            (SharedRace.mobius (t i) v)) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) ≤
      t i := by
  have hkTwo : 2 ≤ Fintype.card κ := by omega
  obtain ⟨a, hai⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card κ by omega) i
  have htiOne : t i < 1 :=
    pmf_coordinate_lt_one_of_ne t ht htotal i a hai
  rw [clockCoordinate_integral_eq_of_loserMoment t ht htotal hkTwo i
    (∫ v : ℝ in 0..1,
      SharedRace.loserBetaIntegrand (Fintype.card κ) (t i)
        (SharedRace.mobius (t i) v)) hJ]
  exact SharedRace.betaCoordinateContribution_le
    (Fintype.card κ) hk (ht i) htiOne

/-- Degenerate two-coordinate companion of
`clockCoordinate_integral_le_of_betaLoserMoment`.-/
private theorem clockCoordinate_integral_le_of_twoLoserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : Fintype.card κ = 2) (i : κ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) =
        ∫ v : ℝ in 0..1,
          SharedRace.loserDegenerateIntegrand (t i)
            (SharedRace.mobius (t i) v)) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) ≤
      t i := by
  have hkTwo : 2 ≤ Fintype.card κ := hk.ge
  obtain ⟨a, hai⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card κ by omega) i
  have htiOne : t i < 1 :=
    pmf_coordinate_lt_one_of_ne t ht htotal i a hai
  rw [clockCoordinate_integral_eq_of_loserMoment t ht htotal hkTwo i
    (∫ v : ℝ in 0..1,
      SharedRace.loserDegenerateIntegrand (t i)
        (SharedRace.mobius (t i) v)) hJ, hk]
  exact SharedRace.twoCoordinateContribution_le (ht i) htiOne

namespace SharedRace

/-- The normalized shared-race reference moment is bounded by its PMF
coordinate.  The proof partitions by the winning clock, evaluates the common
fresh losing pair through the exact pair-clock law, and invokes the scalar
beta allocation theorem (including its separate two-label branch).
@isnad1 id=le.3h3v.s6.57f437a45fd7 from=translated src=- shape=a3be5fb5 vocab=397b728a
-/
theorem clockCoordinateIntegral_le
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : IsPMF t) (htpos : ∀ i, 0 < t i)
    (hk : 2 ≤ Fintype.card κ) (i : κ) :
    (∫ E : κ → ℝ, clockCoordinateIntegrand t i E ∂clockLaw κ) ≤ t i := by
  have htotal : ∑ j, t j = 1 := by
    simpa only [mass] using ht.total
  by_cases hkTwo : Fintype.card κ = 2
  · apply clockCoordinate_integral_le_of_twoLoserMoment
      t htpos htotal hkTwo i
    intro a hai
    exact integral_freshLoserCoordinate_eq_degenerate
      (t i) a i hai hkTwo
  · have hkThree : 3 ≤ Fintype.card κ := by omega
    apply clockCoordinate_integral_le_of_betaLoserMoment
      t htpos htotal hkThree i
    intro a hai
    have htiOne : t i < 1 :=
      pmf_coordinate_lt_one_of_ne t htpos htotal i a hai
    exact integral_freshLoserCoordinate_eq_beta
      (t i) (htpos i) htiOne a i hai hkThree

end SharedRace

private noncomputable def raceClockTilt {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-((1 / K.sigma b z - 1) * u)))

private noncomputable def raceContextClockDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
    raceClockTilt K b z u

private noncomputable def clusterContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    (klDiv (clusterSeedLawGivenWinner K b z)
      (clusterSeedContextMarginal K g b)).toReal

private noncomputable def losingContextKLNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (z : α × β) (u : ℝ) : ℝ :=
  (klDiv (losingClockLaw K b z u)
    (losingClockMarginal K g b u)).toReal

/-! ### The fixed-seed cell-residual link -/

/-- The deterministic winner partition of one contact component.  Zero-mass
cells use the totalized `componentCellLaw`; their prior coefficient is zero.-/
private noncomputable def componentPartitionLatent {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (b : D.L.ι) :
    Latent (D.L.comp b) where
  ι := D.L.ι
  fin := D.L.fin
  dec := D.L.dec
  prior := fun a => componentCellMass D ε a b
  comp := fun a => componentCellLaw D ε a b
  prior_isPMF := by
    constructor
    · exact fun a => componentCellMass_nonneg D ε a b
    · unfold mass componentCellMass cell
      calc
        (∑ a, ∑ z ∈ univ.filter (fun z => winner D ε z = a),
            D.L.comp b z) = ∑ z, D.L.comp b z :=
          Finset.sum_fiberwise univ (winner D ε) (D.L.comp b)
        _ = 1 := by simpa [mass] using (D.L.comp_isPMF b).total
  comp_isPMF := fun a => (cellSourceLatent D ε a).comp_isPMF b
  mixture := by
    intro z
    let a₀ := winner D ε z
    calc
      (∑ a, componentCellMass D ε a b * componentCellLaw D ε a b z) =
          componentCellMass D ε a₀ b * componentCellLaw D ε a₀ b z := by
        apply Finset.sum_eq_single a₀
        · intro a _ ha
          by_cases hm : componentCellMass D ε a b = 0
          · simp [hm]
          · have hwin : winner D ε z ≠ a := by
              exact fun h => ha h.symm
            simp [componentCellLaw, componentCellRaw, hm, hwin]
        · intro ha
          exact (ha (Finset.mem_univ a₀)).elim
      _ = D.L.comp b z := by
        by_cases hm : componentCellMass D ε a₀ b = 0
        · have hzmem : z ∈ cell D ε a₀ := by simp [cell, a₀]
          have hz0 : D.L.comp b z = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg
              (fun z _ => (D.L.comp_isPMF b).nonneg z)).1 hm z hzmem
          simp [hm, hz0]
        · simp only [componentCellLaw, componentCellRaw, hm, ite_false, a₀,
            ite_true]
          have hm' : componentCellMass D ε (winner D ε z) b ≠ 0 := by
            simpa only [a₀] using hm
          field_simp [hm']

private noncomputable def fixedWinnerIZ {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2) Prod.fst D.L.joint

private noncomputable def fixedWinnerIX {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2.1) Prod.fst D.L.joint

private noncomputable def fixedWinnerIY {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2.2) Prod.fst D.L.joint

/-! ### Direct bridge from the all-label shared-race bound

The analytic theorem is stated for one finite source law and one posterior
vector at each source atom.  The duplicate quotient supplies exactly such a
problem in every `C₀ = g` context.  The lemmas below transport its shared
cluster race back to the original label race, without passing through the
scalar/cone KL decomposition.
-/

end stoch_to_det
