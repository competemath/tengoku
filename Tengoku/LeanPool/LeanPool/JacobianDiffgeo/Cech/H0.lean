/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Cech.Cochains
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.Gluing
public import Tengoku

/-!
# `H⁰(𝒰,D) ≃ L(D)` (CC8, proof plan §6.1)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.3).

* `toC0`: restriction of a relative section to the cover, landing in `ker d0`.
* `h0EquivLinSysOn`: `H⁰(𝒰,D) ≃ Γ(Ω, O_D)` — CC8's "definitionally easy" `H⁰ = L(D)`.
* `h0Equiv`: the global form `H⁰(𝒰,D) ≃ L(D)` for covers of `X`.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable (D : RS.Divisor X) {Ω : Opens X} (𝒰 : FinCover Ω)

/-- Restriction of a relative section to the cover. -/
noncomputable def toC0 : RS.LinSysOn D (Ω : Set X) →ₗ[ℂ] C0 D 𝒰 :=
  LinearMap.pi fun i => LinSysOn.restrictL D (𝒰.le_base i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem toC0_mem_ker (φ : RS.LinSysOn D (Ω : Set X)) :
    toC0 D 𝒰 φ ∈ LinearMap.ker (d0 D 𝒰) := by
  rw [LinearMap.mem_ker]
  funext p
  change LinSysOn.restrictL D inf_le_right (LinSysOn.restrictL D (𝒰.le_base p.2) φ) -
      LinSysOn.restrictL D inf_le_left (LinSysOn.restrictL D (𝒰.le_base p.1) φ) = 0
  rw [restrictL_restrictL D (𝒰.le_base p.2) inf_le_right (inf_le_right.trans (𝒰.le_base p.2)),
    restrictL_restrictL D (𝒰.le_base p.1) inf_le_left (inf_le_left.trans (𝒰.le_base p.1))]
  exact sub_self _

/-- `toC0`, corestricted to land in `ker d0`. -/
noncomputable def toC0' : RS.LinSysOn D (Ω : Set X) →ₗ[ℂ] LinearMap.ker (d0 D 𝒰) :=
  LinearMap.codRestrict _ (toC0 D 𝒰) (toC0_mem_ker D 𝒰)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The absolute `LinSysOn D univ` and `LinSys D` are the same submodule (`Opens.coe_top` is
`rfl`, so only the `IsOpen`-gate needs unfolding). -/
theorem linSysOn_top_eq_linSys : RS.LinSysOn D ((⊤ : Opens X) : Set X) = RS.LinSys D := by
  apply Submodule.ext
  intro φ
  constructor
  · intro h x
    exact (RS.mem_linSysOn_iff_of_isOpen isOpen_univ).1 h x (Set.mem_univ x)
  · intro h
    exact (RS.mem_linSysOn_iff_of_isOpen isOpen_univ).2 (fun x _ => h x)

end RS.Cech
