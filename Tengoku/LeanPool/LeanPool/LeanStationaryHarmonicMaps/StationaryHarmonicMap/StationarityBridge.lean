/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
module

public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.SobolevBridge
public import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.FirstVariationBridge
import Tengoku.LeanPool.LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Monotonicity
public import Tengoku

/-!
# Stationarity bridge for the monotonicity theorem

This module provides a paper-facing package name for stationary Sobolev maps.
Its first-variation field is now the paper-facing
`DomainVariationStationaryIn u Du Ω`, whose vector-field variations are bundled
compactly supported `C¹` tests. It bridges to the custom `WeakStationaryIn Du Ω`
interface used by the proved monotonicity theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Paper-facing stationary Sobolev map package.

It consists of the local Sobolev bridge package together with vanishing
domain-variation first variation. -/
structure StationarySobolevMapIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop where
  sobolev : SobolevW12LocIn u Du Ω
  firstVariation_zero : DomainVariationStationaryIn u Du Ω

/-- Constructor for the final stationary Sobolev package from the five natural
inputs used by the monotonicity proof: local `L²` control of the map, a.e.
measurability and local `L²` control of the weak gradient, the distributional
weak-gradient identity, and vanishing domain first variation.
@isnad1 id=stationa.5h5v.s6.29dcbe7850ff from=translated src=- shape=2d8e9b82 vocab=0b4aad6c
-/
theorem stationarySobolevMapIn_of_components {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω) :
    StationarySobolevMapIn u Du Ω :=
  ⟨sobolevW12LocIn_of_components hu_memLp hDu_aesm hDu_memLp hweakGradient,
    hfirstVariation⟩

/-- A stationary Sobolev map is a Sobolev weak stationary map in the bridge
interface.
@isnad1 id=sobolevw.1h5v.s5.13d44bd89e15 from=translated src=- shape=c66f79f5 vocab=2c0a6ea6
-/
theorem StationarySobolevMapIn.toSobolevWeakStationaryMapIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : StationarySobolevMapIn u Du Ω) :
    SobolevWeakStationaryMapIn u Du Ω :=
  ⟨h.sobolev, h.firstVariation_zero.toWeakStationaryIn⟩

/-- A stationary Sobolev map is a custom weak stationary map, after unpacking
the bundled Sobolev and first-variation bridge data.
@isnad1 id=weakstat.1h5v.s5.29e789bdb22e from=translated src=- shape=c66f79f5 vocab=93a7acb3
-/
theorem StationarySobolevMapIn.toWeakStationaryMapIn {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)}
    (h : StationarySobolevMapIn u Du Ω) :
    WeakStationaryMapIn u Du Ω :=
  h.toSobolevWeakStationaryMapIn.toWeakStationaryMapIn

/-- Final paper-facing arbitrary-center Euclidean monotonicity theorem for the
current stationary Sobolev bridge package.
@isnad1 id=le.6h9v.s7.aab705613c3d from=translated src=- shape=2dbd2e80 vocab=a3e22ad3
-/
theorem weakTheta_le_of_stationary_sobolev_map_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : StationarySobolevMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r :=
  weakTheta_le_of_arbitrary_center_W12Loc_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    hmap.toWeakStationaryMapIn hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final paper-facing arbitrary-center Euclidean monotonicity formula for the
current stationary Sobolev bridge package.
@isnad1 id=eq.6h9v.s7.a57a756f3233 from=translated src=- shape=f13211e0 vocab=3de757fc
-/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hmap : StationarySobolevMapIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_arbitrary_center_W12Loc_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    hmap.toWeakStationaryMapIn hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final componentwise entry point: the monotonicity theorem stated directly
from the five stationary `W^{1,2}_{loc}` hypotheses, without asking callers to
manually assemble the intermediate packages.
@isnad1 id=le.10h9v.s7.930b8f0b9286 from=translated src=- shape=bcf94f42 vocab=42e6ea9c
-/
theorem weakTheta_le_of_stationary_sobolev_map_components_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s ≤ r)
    (hr_lt : r < R0) :
    weakTheta Du a s ≤ weakTheta Du a r :=
  weakTheta_le_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    (stationarySobolevMapIn_of_components
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

/-- Final componentwise entry point for the monotonicity increment formula,
stated directly from the five stationary `W^{1,2}_{loc}` hypotheses.
@isnad1 id=eq.10h9v.s8.da917d5e58ea from=translated src=- shape=f0945b1e vocab=96ba24e6
-/
theorem weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_components_euclidean
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {a : Domain n} {R0 s r : ℝ}
    (hu_memLp : LocallyMemLpTwoIn u Ω)
    (hDu_aesm : GradientAEStronglyMeasurableIn Du Ω)
    (hDu_memLp : LocallyMemLpTwoIn Du Ω)
    (hweakGradient : DistributionalWeakGradientIn u Du Ω)
    (hfirstVariation : DomainVariationStationaryIn u Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hclosedBall_subset : Metric.closedBall a R0 ⊆ Ω)
    (hs_pos : 0 < s)
    (hsr : s < r)
    (hr_lt : r < R0) :
    weakTheta Du a r - weakTheta Du a s =
      weakMonotonicityRhs Du a s r :=
  weakTheta_increment_eq_weakMonotonicityRhs_of_stationary_sobolev_map_euclidean
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (a := a) (R0 := R0)
    (s := s) (r := r)
    (stationarySobolevMapIn_of_components
      hu_memLp hDu_aesm hDu_memLp hweakGradient hfirstVariation)
    hΩ_meas hclosedBall_subset hs_pos hsr hr_lt

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
