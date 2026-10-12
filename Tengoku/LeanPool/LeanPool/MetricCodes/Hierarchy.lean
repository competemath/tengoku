/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/
module

public import Tengoku.LeanPool.LeanPool.MetricCodes.HarmonicAnalysis

/-!
# Spherical-code hierarchy

General spectral bounds, localization, compactification, and strict hierarchy estimates.
-/

@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open Filter Topology
open scoped Topology

theorem variationalRate_lt_classical
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    variationalRate s <
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  obtain ⟨a, b, hf, hcost⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact lt_of_le_of_lt (variationalRate_le_of_feasible hf) hcost

theorem rateSet_nonempty_of_interior
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (rateSet s).Nonempty := by
  obtain ⟨a, b, hf, _⟩ :=
    exists_strict_improving_spherical_feasible hs hs'
  exact ⟨MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b,
    a, b, hf, rfl⟩

end

section

open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace

namespace GeneralSpectral

/-- The longitudinal degree used in the spherical-code argument. -/
def longitudinalDegree (a : ℝ) (n : ℕ) : ℕ :=
  ⌊a * (n : ℝ)⌋₊

/-- The transverse degree used in the spherical-code argument. -/
def transverseDegree (b : ℝ) (n : ℕ) : ℕ :=
  ⌊b * (n : ℝ)⌋₊

theorem tendsto_longitudinal_ratio {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ =>
      (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  exact SpherePacking.SpectralAsymptotics.tendsto_floored_ratio ha

theorem tendsto_transverse_ratio {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ =>
      (transverseDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  exact SpherePacking.SpectralAsymptotics.tendsto_floored_ratio hb

theorem tendsto_longitudinalDegree_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (longitudinalDegree a) atTop atTop := by
  exact tendsto_nat_floor_mul_atTop a ha

theorem tendsto_terminal_degree_ratio {a : ℝ}
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset :
      Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [
    (tendsto_longitudinalDegree_atTop ha).eventually
      (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring

theorem normalizedCoefficient_eq_Gamma
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    SpherePacking.SpectralAsymptotics.normalizedCoefficient a b 0 =
      MetricCodes.Gamma a b := by
  have hfactor : 0 ≤ a * (1 + a) := by positivity
  have hlin : 0 ≤ 1 + 2 * a := by positivity
  unfold SpherePacking.SpectralAsymptotics.normalizedCoefficient
    MetricCodes.Gamma
  have hrad :
      Real.sqrt
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) =
        (1 + 2 * a) * Real.sqrt (a * (1 + a)) := by
    have hpoly :
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) =
          (a * (1 + a)) * (1 + 2 * a) ^ 2 := by
      ring
    rw [hpoly, Real.sqrt_mul hfactor, Real.sqrt_sq hlin]
    ring
  rw [hrad]
  congr 1
  ring

theorem tendsto_terminal_coefficient {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n) (longitudinalDegree a n - r))
      atTop (nhds (MetricCodes.Gamma a b)) := by
  have hx := tendsto_terminal_degree_ratio ha r
  have hy := tendsto_transverse_ratio hb
  have hz : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hnum := ((hx.sub hy).add hz).mul
    (((hx.add hy).add hone).sub (htwo.mul hz))
  have hrad := (((hx.add hz).mul
    ((hx.add hone).sub (htwo.mul hz))).mul
      (((htwo.mul hx).add hone).sub (htwo.mul hz))).mul
        ((htwo.mul hx).add hone)
  have hroot := hrad.sqrt
  have hrootne :
      Real.sqrt
        ((a + 0) * (a + 1 - 2 * 0) *
          (2 * a + 1 - 2 * 0) * (2 * a + 1)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    have hone : 0 < a + 1 := by linarith
    have htwo : 0 < 2 * a + 1 := by linarith
    simpa only [add_zero, mul_zero, sub_zero,
      gt_iff_lt] using mul_pos (mul_pos (mul_pos ha hone) htwo) htwo
  have hnorm := hnum.div hroot hrootne
  have pointwise_div {f g : ℕ → ℝ} {l : ℝ}
      (h : Tendsto (f / g) atTop (nhds l)) :
      Tendsto (fun n => f n / g n) atTop (nhds l) :=
    h.congr' (Filter.Eventually.of_forall (fun _ => rfl))
  have hnorm' :
      Tendsto
        (fun n : ℕ =>
          SpherePacking.SpectralAsymptotics.normalizedCoefficient
            (((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
            ((transverseDegree b n : ℝ) / (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (SpherePacking.SpectralAsymptotics.normalizedCoefficient a b 0)) := by
    simpa only [SpherePacking.SpectralAsymptotics.normalizedCoefficient, one_div, add_zero,
      mul_zero, sub_zero] using pointwise_div hnorm
  rw [normalizedCoefficient_eq_Gamma ha b] at hnorm'
  refine hnorm'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact
    (SpherePacking.SpectralAsymptotics.jacobiCoefficient_eq_normalized
      n (transverseDegree b n) (longitudinalDegree a n - r) hn).symm

theorem eventually_transverse_add_le_longitudinal
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      transverseDegree b n + m ≤ longitudinalDegree a n := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  let δ : ℝ := (a - b) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδlt : δ < a - b := by
    dsimp [δ]
    linarith
  have hratio :=
    ((tendsto_longitudinal_ratio ha.le).sub
      (tendsto_transverse_ratio hb)).eventually
        (lt_mem_nhds hδlt)
  have hgrowth :
      Tendsto (fun n : ℕ => δ * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hδ
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hgrowth.eventually
    (eventually_ge_atTop (m : ℝ))
  filter_upwards [hratio, hlarge, eventually_gt_atTop (0 : ℕ)]
    with n hnratio hnlarge hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hnratio hnreal
  have hidentity :
      (((longitudinalDegree a n : ℝ) / (n : ℝ) -
        (transverseDegree b n : ℝ) / (n : ℝ)) * (n : ℝ)) =
        (longitudinalDegree a n : ℝ) -
          (transverseDegree b n : ℝ) := by
    field_simp [ne_of_gt hnreal]
  rw [hidentity] at hmul
  have hreal :
      (transverseDegree b n : ℝ) + (m : ℝ) ≤
        (longitudinalDegree a n : ℝ) := by
    linarith
  exact_mod_cast hreal

/-- The terminal edge rayleigh used in the spherical-code argument. -/
def terminalEdgeRayleigh (a b : ℝ) (m n : ℕ) : ℝ :=
  (2 * ∑ r ∈ Finset.range m,
    SpherePacking.Gegenbauer.jacobiCoefficient
      n (transverseDegree b n)
      (longitudinalDegree a n - (m - r))) /
        ((m : ℝ) + 1)

theorem tendsto_terminalEdgeRayleigh {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    Tendsto (terminalEdgeRayleigh a b m) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b))) := by
  have hsum :
      Tendsto
        (fun n : ℕ => ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - (m - r)))
        atTop
        (nhds (∑ _r ∈ Finset.range m, MetricCodes.Gamma a b)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_terminal_coefficient ha hb (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (htwo.mul hsum).div_const ((m : ℝ) + 1)
  change
    Tendsto (fun n : ℕ => terminalEdgeRayleigh a b m n) atTop
      (nhds
        (((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b)))
  simpa only [terminalEdgeRayleigh, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hquot

theorem terminalEdgeRayleigh_le_top
    (a b : ℝ) (m n : ℕ)
    (hfit : transverseDegree b n + m ≤ longitudinalDegree a n) :
    terminalEdgeRayleigh a b m n ≤
      SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have hkl : transverseDegree b n ≤ longitudinalDegree a n := by omega
  have hm : m ≤ longitudinalDegree a n - transverseDegree b n := by omega
  have hsum :
      (∑ r ∈ Finset.range m,
        SpherePacking.Gegenbauer.jacobiCoefficient
          n (transverseDegree b n)
          (longitudinalDegree a n - (m - r))) =
        ∑ r ∈ Finset.range m,
          SpherePacking.Gegenbauer.jacobiCoefficient
            n (transverseDegree b n)
            (longitudinalDegree a n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    omega
  unfold terminalEdgeRayleigh
  rw [hsum]
  exact SpherePacking.SpectralAsymptotics.terminal_edge_sum_le_top
    n (transverseDegree b n) (longitudinalDegree a n) m hkl hm

theorem eventually_topEigenvalue_gt {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s < SpherePacking.Jacobi.topEigenvalue
        n (transverseDegree b n) (longitudinalDegree a n) := by
  have ha : 0 < a := lt_of_le_of_lt hb hba
  have hgamma : 0 < 2 * MetricCodes.Gamma a b := by
    exact mul_pos (by norm_num) (MetricCodes.Gamma_pos hb hba)
  let g : ℝ := 2 * MetricCodes.Gamma a b
  let ε : ℝ := (g - s) / 2
  have hε : 0 < ε := by
    dsimp [ε, g]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (g / ε)
  have hprod : g < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : g / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).2
    nlinarith [hgamma]
  have hidentity :
      ((m : ℝ) / ((m : ℝ) + 1)) * g =
        g - g / ((m : ℝ) + 1) := by
    field_simp [hden.ne']; ring
  have hbelow :
      s < ((m : ℝ) / ((m : ℝ) + 1)) * g := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot :=
    (tendsto_terminalEdgeRayleigh ha hb m).eventually
      (lt_mem_nhds (show
        s < ((m : ℝ) / ((m : ℝ) + 1)) *
          (2 * MetricCodes.Gamma a b) by
        simpa only [g] using hbelow))
  filter_upwards [hquot,
    eventually_transverse_add_le_longitudinal hb hba m]
      with n hn hfit
  exact hn.trans_le (terminalEdgeRayleigh_le_top a b m n hfit)

/-- The spectral gap used in the spherical-code argument. -/
def spectralGap (s a b : ℝ) : ℝ :=
  (2 * MetricCodes.Gamma a b - s) / 2

theorem spectralGap_pos {s a b : ℝ}
    (h : s < 2 * MetricCodes.Gamma a b) :
    0 < spectralGap s a b := by
  unfold spectralGap
  linarith

theorem eventually_topEigenvalue_uniform_gap {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s + spectralGap s a b <
        SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) := by
  apply eventually_topEigenvalue_gt hb hba
  unfold spectralGap
  linarith

/-- The spectral prefactor used in the spherical-code argument. -/
def spectralPrefactor (s a b : ℝ) : ℝ :=
  (1 - s) / spectralGap s a b

theorem spectralPrefactor_pos {s a b : ℝ}
    (hs : s < 1) (hgap : s < 2 * MetricCodes.Gamma a b) :
    0 < spectralPrefactor s a b := by
  unfold spectralPrefactor
  exact div_pos (sub_pos.mpr hs) (spectralGap_pos hgap)

theorem legacy_binaryEntropy_eq_sphericalEntropy (u : ℝ) :
    SpherePacking.NumericalCertificate.binaryEntropy u =
      MetricCodes.sphericalEntropy u := by
  unfold SpherePacking.NumericalCertificate.binaryEntropy
    MetricCodes.sphericalEntropy Real.logb
  ring

theorem tendsto_log_spectral_harmonicQuotient
    {s a b : ℝ} (hs : s < 1)
    (hb : 0 < b) (hba : b < a)
    (hspectral : s < 2 * MetricCodes.Gamma a b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log
          (spectralPrefactor s a b *
            SpherePacking.harmonicDimensionQuotient a b n) /
          (n : ℝ)) / Real.log 2)
      atTop
      (nhds (MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b)) := by
  have ha : 0 < a := hb.trans hba
  have h := SpherePacking.tendsto_log_const_mul_harmonicDimensionQuotient
    a b (spectralPrefactor s a b) ha hb
    (spectralPrefactor_pos hs hspectral)
  rw [legacy_binaryEntropy_eq_sphericalEntropy a,
    legacy_binaryEntropy_eq_sphericalEntropy b] at h
  exact h

end GeneralSpectral

end

end Spherical

end MetricCodes

section

open scoped InnerProductSpace

namespace SpherePacking

/-- The inclusion of unit sphere points into the ambient Euclidean space. -/
def spherePointEmbedding (n : ℕ) : MetricCodes.Sphere n ↪
  Euclidean n :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The embedding of a spherical code's attached point set into the unit sphere. -/
def attachedSphereEmbedding {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    {x : Euclidean n // x ∈ C.points} ↪ MetricCodes.Sphere n where
  toFun x := ⟨x.1, C.unit_norm x.1 x.2⟩
  inj' := by
    intro x y h
    exact Subtype.ext
      (congrArg (fun z : MetricCodes.Sphere n => (z : Euclidean n)) h)

private theorem sphericalCode_ext_metriccodes2_d60650ef {n : ℕ} {s : ℝ}
    {C D : SphericalCode n s} (h : C.points = D.points) : C = D := by
  cases C
  cases D
  simpa only [SphericalCode.mk.injEq] using h

private theorem codesSphericalCode_ext_metriccodes2_d60650ef {n : ℕ} {s : ℝ}
    {C D : MetricCodes.SphericalCode n s} (h : C.points = D.points) : C = D := by
  cases C
  cases D
  simpa only [MetricCodes.SphericalCode.mk.injEq] using h

/-- The to codes used in the spherical-code argument. -/
def SphericalCode.toCodes {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) : MetricCodes.SphericalCode n s where
  points := C.points.attach.map (attachedSphereEmbedding C)
  inner_le := by
    intro x hx y hy hxy
    obtain ⟨x', _, hx'⟩ := Finset.mem_map.mp hx
    obtain ⟨y', _, hy'⟩ := Finset.mem_map.mp hy
    subst x
    subst y
    apply C.inner_le x'.1 x'.2 y'.1 y'.2
    intro h
    apply hxy
    exact Subtype.ext h

/-- The of codes used in the spherical-code argument. -/
def SphericalCode.ofCodes {n : ℕ} {s : ℝ}
    (C : MetricCodes.SphericalCode n s) : SphericalCode n s where
  points := C.points.map (spherePointEmbedding n)
  unit_norm := by
    intro x hx
    obtain ⟨x', _, rfl⟩ := Finset.mem_map.mp hx
    exact x'.property
  inner_le := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    apply C.inner_le hx' hy'
    intro h
    apply hxy
    exact congrArg Subtype.val h

@[simp] theorem SphericalCode.toCodes_card {n : ℕ} {s : ℝ}
    (C : SphericalCode n s) :
    C.toCodes.points.card = C.points.card := by
  simp only [toCodes, Finset.card_map, Finset.card_attach]

@[simp] theorem SphericalCode.ofCodes_card {n : ℕ} {s : ℝ}
    (C : MetricCodes.SphericalCode n s) :
    (SphericalCode.ofCodes C).points.card = C.points.card := by
  simp only [ofCodes, Finset.card_map]

private def sphericalCodeEquiv (n : ℕ) (s : ℝ) :
    SphericalCode n s ≃ MetricCodes.SphericalCode n s where
  toFun := SphericalCode.toCodes
  invFun := SphericalCode.ofCodes
  left_inv := by
    intro C
    apply sphericalCode_ext_metriccodes2_d60650ef
    change (C.toCodes.points.map (spherePointEmbedding n)) = C.points
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
      obtain ⟨w, _hw, hwz⟩ := Finset.mem_map.mp hz
      have hwx : (w : Euclidean n) = x :=
        (congrArg Subtype.val hwz).trans hzx
      simpa only [hwx] using w.property
    · intro hx
      let w : {u : Euclidean n // u ∈ C.points} := ⟨x, hx⟩
      let z : MetricCodes.Sphere n :=
        attachedSphereEmbedding C w
      exact Finset.mem_map.mpr ⟨z,
        Finset.mem_map.mpr ⟨w, Finset.mem_attach _ _, rfl⟩, rfl⟩
  right_inv := by
    intro C
    apply codesSphericalCode_ext_metriccodes2_d60650ef
    ext x
    change
      x ∈ (SphericalCode.ofCodes C).points.attach.map
        (attachedSphereEmbedding (SphericalCode.ofCodes C)) ↔
        x ∈ C.points
    constructor
    · intro hx
      obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hx
      obtain ⟨w, hw, hwz⟩ :=
        Finset.mem_map.mp (show z.1 ∈ (SphericalCode.ofCodes C).points from z.2)
      have hval : (w : Euclidean n) = (z : Euclidean n) := hwz
      have hxw : x = w := by
        apply Subtype.ext
        exact (congrArg Subtype.val hz).symm.trans hval.symm
      simpa [hxw] using hw
    · intro hx
      let z : {u : Euclidean n // u ∈ (SphericalCode.ofCodes C).points} :=
        ⟨(x : Euclidean n), Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
      exact Finset.mem_map.mpr
        ⟨z, Finset.mem_attach _ _, Subtype.ext rfl⟩

/-- The spherical code number used in the spherical-code argument. -/
def sphericalCodeNumber (n : ℕ) (s : ℝ) : ℕ∞ :=
  ⨆ C : SphericalCode n s, (C.points.card : ℕ∞)

end SpherePacking

end

namespace MetricCodes

namespace Spherical

section

open Filter Topology

namespace MaximalCodeBounds

end MaximalCodeBounds

end

section

open Filter Topology
open scoped Topology

namespace HigherHierarchy

end HigherHierarchy

end

section

open Filter Topology
open scoped Topology

/-- The boundary rate set used in the spherical-code argument. -/
def boundaryRateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
    r = MetricCodes.sphericalEntropy a -
      MetricCodes.sphericalEntropy (boundaryDegree s a)}

/-- The boundary variational rate used in the spherical-code argument. -/
def boundaryVariationalRate (s : ℝ) : ℝ :=
  sInf (boundaryRateSet s)

end

section

open Filter Topology
open scoped Topology

end

section

open scoped InnerProductSpace Topology

namespace SidelnikovLocalization

/-- The slice cost used in the spherical-code argument. -/
def sliceCost (s t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 ((1 - t) / (1 - s))

@[simp] theorem sliceCost_self {s : ℝ} (hs : s < 1) :
    sliceCost s s = 0 := by
  unfold sliceCost
  rw [div_self (by linarith : 1 - s ≠ 0)]
  simp only [one_div, Real.logb_one, mul_zero]

/-- The localized envelope used in the spherical-code argument. -/
def localizedEnvelope (κ : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf ((fun t => κ t + sliceCost s t) '' Set.Icc 0 s)

end SidelnikovLocalization

end

namespace HigherHierarchy

section

open Filter Topology
open scoped BigOperators Topology

/-- Extend the ambient parameter row by appending a zero coordinate. -/
def appendAmbient {r : ℕ} (a : Fin (r + 1) → ℝ) : Fin (r + 2) → ℝ :=
  Fin.snoc a 0

/-- Extend the stabilizer parameter row by appending the coordinate `ε`. -/
def appendStabilizer {r : ℕ} (b : Fin r → ℝ) (ε : ℝ) : Fin (r + 1) → ℝ :=
  Fin.snoc b ε

/-- The weighted spectral loss coefficient associated with appending a stabilizer parameter. -/
def appendSpectralLoss {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i * spectralAtom (a i) /
      ((a i) * (1 + (a i)))

/-- The square-root coordinate change that scales the quadratic weight `u * (1 + u)` by `c`. -/
def scaleCoordinate (c u : ℝ) : ℝ :=
  (Real.sqrt (1 + 4 * c * (u * (1 + u))) - 1) / 2

theorem scaleCoordinate_nonneg {c u : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) : 0 ≤ scaleCoordinate c u := by
  have hx : 0 ≤ (u * (1 + u)) := by
    positivity
  have hrad : 0 ≤ 1 + 4 * c * (u * (1 + u)) := by positivity
  have hsquare := Real.sq_sqrt hrad
  have hsqrt := Real.sqrt_nonneg (1 + 4 * c * (u * (1 + u)))
  unfold scaleCoordinate
  nlinarith [mul_nonneg hc hx]

theorem quadraticCoordinate_scaleCoordinate {c u : ℝ}
    (hc : 0 ≤ c) (hu : 0 ≤ u) :
    ((scaleCoordinate c u) * (1 + (scaleCoordinate c u))) =
      c * (u * (1 + u)) := by
  have hx : 0 ≤ (u * (1 + u)) := by
    positivity
  have hrad : 0 ≤ 1 + 4 * c * (u * (1 + u)) := by positivity
  have hsquare := Real.sq_sqrt hrad
  unfold scaleCoordinate at *
  nlinarith

@[simp] theorem scaleCoordinate_one {u : ℝ} (hu : 0 ≤ u) :
    scaleCoordinate 1 u = u := by
  apply quadraticCoordinate_strictMonoOn.injOn
    (scaleCoordinate_nonneg (by norm_num) hu) hu
  simpa only [one_mul] using quadraticCoordinate_scaleCoordinate (by norm_num : (0 : ℝ) ≤ 1) hu

@[simp] theorem scaleCoordinate_zero (c : ℝ) : scaleCoordinate c 0 = 0 := by
  simp only [scaleCoordinate, add_zero, mul_one, mul_zero, Real.sqrt_one,
    sub_self, zero_div]

/-- Apply the quadratic-weight scaling coordinate change to every ambient parameter. -/
def scaleAmbient {r : ℕ} (c : ℝ) (a : Fin (r + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun i => scaleCoordinate c (a i)

/-- Apply the quadratic-weight scaling coordinate change to every stabilizer parameter. -/
def scaleStabilizer {r : ℕ} (c : ℝ) (b : Fin r → ℝ) : Fin r → ℝ :=
  fun i => scaleCoordinate c (b i)

/-- The positive weighted coefficient controlling the spectral gain under parameter scaling. -/
def scalingGainCoefficient {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i *
      (((a i) * (1 + (a i))) /
        ((1 + 8 * ((a i) * (1 + (a i)))) *
          (1 + 4 * ((a i) * (1 + (a i))))))

/-- The reciprocal quadratic-weight sum bounding the spectral loss from appending a parameter. -/
def appendSpectralLossUpper {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ i : Fin (r + 1),
    lagrangeWeight a b i / (2 * ((a i) * (1 + (a i))))

/-- The scaling slope chosen to exceed the upper bound on the appended spectral loss. -/
def compensatedScalingSlope {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (appendSpectralLossUpper a b + 1) / scalingGainCoefficient a b

/-- The parameter scaling factor compensating for an appended stabilizer coordinate `ε`. -/
def compensatedScalingFactor {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) : ℝ :=
  1 + compensatedScalingSlope a b * (ε * (1 + ε))

@[simp] theorem compensatedScalingFactor_zero {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    compensatedScalingFactor a b 0 = 1 := by
  simp only [compensatedScalingFactor, add_zero, mul_one, mul_zero]

/-- The entropy objective evaluated along the compensated parameter-scaling path. -/
def compensatedPhiPath {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (ε : ℝ) : ℝ :=
  Phi (scaleAmbient (compensatedScalingFactor a b ε) a)
    (scaleStabilizer (compensatedScalingFactor a b ε) b)

@[simp] theorem compensatedPhiPath_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    compensatedPhiPath a b 0 = Phi a b := by
  unfold compensatedPhiPath Phi scaleAmbient scaleStabilizer
  simp_rw [compensatedScalingFactor_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [scaleCoordinate_one (h.ambient_nonneg i)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [scaleCoordinate_one (h.stabilizer_pos i).le]

/-- The entropy values of rank-`r` interlacing certificates whose spectral value strictly
exceeds `s`. -/
def levelRateSet (r : ℕ) (s : ℝ) : Set ℝ :=
  {R | ∃ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ R = Phi a b}

/-- The level rate used in the spherical-code argument. -/
def levelRate (r : ℕ) (s : ℝ) : ℝ := sInf (levelRateSet r s)

/-- Subtract `x` from the first ambient entry, then set the last ambient entry to `z`. -/
def openingAmbient {r : ℕ}
    (a : Fin (r + 1) → ℝ) (x z : ℝ) : Fin (r + 1) → ℝ :=
  Function.update
    (Function.update a 0 (a 0 - x)) (Fin.last r) z

@[simp] theorem openingAmbient_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ}
    (hzero : a (Fin.last r) = 0) : openingAmbient a 0 0 = a := by
  unfold openingAmbient
  simp only [sub_zero, Function.update_eq_self, Function.update_eq_self_iff, hzero]

/-- Equality of initial values together with derivatives at zero related by the factor `η`. -/
def ScaledOpeningDerivative (η : ℝ) (f g : ℝ → ℝ) : Prop :=
  f 0 = g 0 ∧ ∃ d : ℝ, HasDerivAt f (η * d) 0 ∧ HasDerivAt g d 0

/-- The spectral sum over the regular ambient entries along the boundary-opening path. -/
def openingRegularGamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (η t : ℝ) : ℝ :=
  ∑ i : Fin r,
    lagrangeWeight (openingAmbient a (η * t) (t ^ 2)) b i.castSucc *
      spectralAtom (openingAmbient a (η * t) (t ^ 2) i.castSucc)

/-- The positive opening speed bounded using the derivative of the regular spectral sum. -/
def openingContractionSpeed {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  lagrangeWeight a b (Fin.last r) /
    (2 * (|deriv (openingRegularGamma a b 1) 0| + 1))

end

section

end

section

open Set Filter Topology

end

section

open Filter
open scoped BigOperators Topology

namespace CompactificationEntropy

/-- The boundary quadratic expressed in the reciprocal-scale parameter used for
compactification. -/
def normalizedBoundaryQuadratic (s u : ℝ) : ℝ :=
  1 + u - (s / 2) * (u + 2) * Real.sqrt (1 + u)

/-- The square-root solution of the normalized boundary quadratic equation. -/
def normalizedBoundaryDegree (s u : ℝ) : ℝ :=
  (Real.sqrt (u ^ 2 + 4 * normalizedBoundaryQuadratic s u) - u) / 2

end CompactificationEntropy

end

section

open Filter Topology
open scoped BigOperators Topology

/-- The compactifying coordinate transformation `u ↦ 1 / (1 + u)`. -/
def compactifiedHierarchyCoordinate (u : ℝ) : ℝ := (1 + u)⁻¹

/-- The combined index type for the ambient and stabilizer coordinates of a fixed hierarchy
level. -/
abbrev HierarchyCompactIndex (r : ℕ) := Fin (r + 1) ⊕ Fin r

/-- The tuple obtained by compactifying all ambient and stabilizer parameters. -/
def compactifiedHierarchyTuple {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) :
    HierarchyCompactIndex r → ℝ :=
  Sum.elim (fun i => compactifiedHierarchyCoordinate (a i))
    (fun i => compactifiedHierarchyCoordinate (b i))

/-- The unit cube containing the compactified ambient and stabilizer parameter tuples. -/
def hierarchyCompactCube (r : ℕ) : Set (HierarchyCompactIndex r → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)

end

section

open Set Filter Topology

/-- Closure of the fixed-level rate bound under convergent spectral thresholds and entropy upper
bounds. -/
def FixedLevelCompactifiedCertificateClosure (r : ℕ) : Prop :=
  ∀ {s R : ℝ}, 0 < s → s < 1 →
    ∀ (u : ℕ → ℝ)
      (a : ℕ → Fin (r + 1) → ℝ)
      (b : ℕ → Fin r → ℝ),
      Tendsto u atTop (nhds s) →
      (∀ n, Interlacing (a n) (b n)) →
      (∀ n, u n < 2 * Gamma (a n) (b n)) →
      (∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) →
      levelRate r s ≤ R

end

section

open Filter Topology
open scoped BigOperators Topology

/-- Extend the ambient parameter row by prepending `u`. -/
def prependAmbient {r : ℕ} (u : ℝ) (a : Fin (r + 1) → ℝ) :
    Fin (r + 2) → ℝ :=
  Fin.cons u a

/-- Extend the stabilizer parameter row by prepending `v`. -/
def prependStabilizer {r : ℕ} (v : ℝ) (b : Fin r → ℝ) :
    Fin (r + 1) → ℝ :=
  Fin.cons v b

end

section

open Filter Topology
open scoped Topology

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open scoped BigOperators

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open Filter Topology
open scoped Topology

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open MeasureTheory
open scoped BigOperators Interval

end

section

open scoped BigOperators

/-- Interlacing with non-strict inequalities and a nonnegative final ambient coordinate. -/
def WeakInterlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, b i ≤ a i.castSucc ∧ a i.succ ≤ b i

theorem WeakInterlacing.antitone_ambient {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) : Antitone a := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

theorem WeakInterlacing.ambient_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : WeakInterlacing a b) (i : Fin (r + 1)) : 0 ≤ a i :=
  h.1.trans (h.antitone_ambient i.le_last)

/-- The ratio of stabilizer and ambient products of shifted quadratic weights. -/
def hierarchyStieltjesRatio {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
    (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open Set Filter Topology
open scoped BigOperators Topology

/-- The ambient suffix remaining after the first `k` compactified coordinates are removed. -/
def compactifiedAmbientSuffix {r k j : ℕ}
    (h : k + j = r) (A : Fin (r + 1) → ℝ) :
    Fin (j + 1) → ℝ :=
  fun i => A ⟨k + i.val, by omega⟩

/-- The stabilizer suffix remaining after the first `k` compactified coordinates are removed. -/
def compactifiedStabilizerSuffix {r k j : ℕ}
    (h : k + j = r) (B : Fin r → ℝ) :
    Fin j → ℝ :=
  fun i => B ⟨k + i.val, by omega⟩

end

section

open Filter Topology
open scoped Topology

end

section

open Set Filter Topology
open scoped BigOperators Topology

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open scoped BigOperators

/-- The product of the first `k` compactified escaping-coordinate ratios. -/
def compactifiedEscapingRatioProduct {r k j : ℕ}
    (hkj : k + j = r) (d : Fin r → ℝ) : ℝ :=
  ∏ i : Fin k, d ⟨i.val, by omega⟩

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators Topology

private abbrev compactificationArcsineMeasure_metriccodes2_275785c2 : Measure ℝ :=
  (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)

end

section

open Filter Topology
open scoped BigOperators Topology

end

section

open Filter Topology
open scoped Topology

/-- Subsequential compactification of fixed-level families with bounded entropy into a residual
hierarchy. -/
def FixedLevelForwardCompactifiedResidualLimit (r : ℕ) : Prop :=
  ∀ {C : ℝ}
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ),
    (∀ n, Interlacing (a n) (b n)) →
    (∀ n, Phi (a n) (b n) ≤ C) →
    ∃ (j : ℕ) (c : ℝ)
      (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ)
      (φ : ℕ → ℕ),
      StrictMono φ ∧ 0 < c ∧ c ≤ 1 ∧ Interlacing A B ∧
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) ∧
      Tendsto (fun n => Gamma (a (φ n)) (b (φ n)))
        atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B)) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
        atTop (nhds (Phi A B - Real.logb 2 c))

end

section

end

section

end

section

end

section

open Filter Topology
open scoped Topology

/-- The one-row boundary entropy difference between the ambient and boundary degrees. -/
def oneRowBoundaryObjective (s a : ℝ) : ℝ :=
  MetricCodes.sphericalEntropy a -
    MetricCodes.sphericalEntropy (MetricCodes.Spherical.boundaryDegree s a)

end

section

end

section

open Filter Topology
open scoped Topology

namespace CompactificationEntropy

end CompactificationEntropy

end

section

open Set Filter Topology
open scoped Topology

end

section

open Filter Topology
open scoped BigOperators Topology

/-- The entropy values of interlacing certificates at any rank satisfying the closed spectral
constraint. -/
def closedHierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s ≤ 2 * Gamma a b ∧ z = Phi a b}

/-- The closed hierarchy variational rate used in the spherical-code argument. -/
def closedHierarchyVariationalRate (s : ℝ) : ℝ :=
  sInf (closedHierarchyRateSet s)

/-- The spherical code rate used in the spherical-code argument. -/
def sphericalCodeRate (s : ℝ) : ℝ :=
  Filter.limsup
    (fun n : ℕ =>
      Real.logb 2
        ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) / (n : ℝ))
    Filter.atTop

/-- The fixed level hierarchy code bound used in the spherical-code argument. -/
def FixedLevelHierarchyCodeBound : Prop :=
  ∀ {r : ℕ} {s R : ℝ},
    0 < s → s < 1 →
    ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b → s < 2 * Gamma a b → Phi a b < R →
        ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
          (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))

end

section

/-- The square-root contraction factor comparing the cap thresholds `s` and `t`. -/
def compactificationCapFactor (s t : ℝ) : ℝ :=
  Real.sqrt ((1 - s) / (1 - t))

end

section

open Set Filter Topology
open scoped BigOperators Topology

end

section

/-- Transfer of a finite hierarchy certificate to the variational bound after cap contraction. -/
def GenuineCompactifiedHierarchyTransfer : Prop :=
  ∀ {r : ℕ} {s c : ℝ},
    0 < c → c < 1 →
    ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
      Interlacing a b →
        s < 1 - c ^ 2 * (1 - 2 * Gamma a b) →
          hierarchyVariationalRate s ≤ Phi a b - Real.logb 2 c

end

section

/-- The localized level rate used in the spherical-code argument. -/
def localizedLevelRate (r : ℕ) (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (levelRate r) s

/-- The localized hierarchy rate used in the spherical-code argument. -/
def localizedHierarchyRate (s : ℝ) : ℝ :=
  sInf (Set.range fun r : ℕ => localizedLevelRate r s)

/-- The localized row rate used in the spherical-code argument. -/
def localizedRowRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    MetricCodes.Spherical.variationalRate s

/-- The classical localized rate used in the spherical-code argument. -/
def classicalLocalizedRate (s : ℝ) : ℝ :=
  MetricCodes.Spherical.SidelnikovLocalization.localizedEnvelope
    (fun t => MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold t)) s

end

section

end

section

open Filter Topology
open scoped Topology

end

end HigherHierarchy

end Spherical

end MetricCodes

end MetricCodesNoncomputable
