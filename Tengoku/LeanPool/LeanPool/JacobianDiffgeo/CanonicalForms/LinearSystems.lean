/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.CanonicalForms.OneDimensional
public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.Genus
public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.LinearSystem
public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.ResidueCalculus.MittagLeffler
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Forms.OfCoeffs
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Identity
public import Tengoku

/-!
# `Ω(D)`, the `L(D+K)` bridge, holomorphic forms, and ML form data (D11/D12/D13)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D11–D13, §4.5, proof plan §5 P6).

* `MForm.OmegaSpace D : Submodule ℂ (MForm X)` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X,Ω_D)`):
  meromorphic 1-forms with `-D ≤` order everywhere, defined order-wise on the QUOTIENT (mirrors
  `LinSys`'s primary definition); `MForm.i D` (index of speciality). Instance-free (the order-wise
  carrier needs no topology), strictly more general than the design's listing.
* **D11** `ΩIsoLinSys : OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf θ₀)` (Forster 17.4 /
  Miranda `Ω_D ≅ O_{D+K}`), via D8's one-dimensionality (`LinearEquiv.ofBijective` of
  `h ↦ h • θ₀`, membership transported by the pointwise `smul_mem_omegaSpace_iff` dictionary);
  `i_eq_l_add_canonicalDivisorOf`.
* **D12** `holomorphicMFormsEquiv : Form1 X ≃ₗ[ℂ] OmegaSpace (0 : Divisor X)`: forward is
  `Form1.toMForm` (analytic coefficients have `0 ≤ ord`); injectivity is continuity at chart
  centers; surjectivity REPAIRS a representative via the mero unit's canonical `holoRepr` pattern
  — for a class with `0 ≤ ord` everywhere, the chart-local coefficient germs
  `MeroGermOn.mk (θ.coeffAt x ∘ chartAt ℂ x)` have honest analytic `holoRepr`s
  (`ord_eq_meromorphicOrderAt_of_mem_source` bridges center-orders to target-orders), whose
  chart reads assemble into a `Form1CoeffData` and a genuine `Form1` via `Form1.ofCoeffs`.
  Needs NO topological instances (the design's `[T1][T2][Compact]` are unnecessary here).
  Corollary `genus_eq_finrank_omegaSpace_zero` (the cech-h1-genus/riemann-roch export).
* **D13** `MLFormData`/`Realizes` (against `MForm.laurentCoeffAt`, on classes)/`totalRes`/
  `Realizes.resAt_eq`: a thin `X`-level wrapper around residue-calculus's `PrincipalPartData`.
-/

@[expose] public section

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Order arithmetic (junk-robust; data layer, then descended) -/

namespace MFormData

theorem ord_add (θ η : MFormData X) (x : X) : min (θ.ord x) (η.ord x) ≤ (θ + η).ord x := by
  have hf : (θ + η).coeffAt x = θ.coeffAt x + η.coeffAt x := funext fun z => coeffAt_add θ η x z
  change min (θ.ord x) (η.ord x) ≤ meromorphicOrderAt ((θ + η).coeffAt x) (chartAt ℂ x x)
  rw [hf]
  exact meromorphicOrderAt_add (θ.meromorphicAt_coeffAt x) (η.meromorphicAt_coeffAt x)

theorem ord_smul {c : ℂ} (hc : c ≠ 0) (θ : MFormData X) (x : X) : (c • θ).ord x = θ.ord x := by
  have hf : (c • θ).coeffAt x = c • θ.coeffAt x := funext fun z => by
    rw [coeffAt_smul]; rfl
  change meromorphicOrderAt ((c • θ).coeffAt x) (chartAt ℂ x x) = θ.ord x
  rw [hf]
  exact meromorphicOrderAt_smul_of_ne_zero analyticAt_const hc

end MFormData

namespace MForm

theorem ord_add (Θ H : MForm X) (x : X) : min (Θ.ord x) (H.ord x) ≤ (Θ + H).ord x :=
  Quotient.inductionOn₂ Θ H fun θ η => MFormData.ord_add θ η x

theorem ord_smul {c : ℂ} (hc : c ≠ 0) (Θ : MForm X) (x : X) : (c • Θ).ord x = Θ.ord x := by
  obtain ⟨θ, rfl⟩ := exists_rep Θ
  exact MFormData.ord_smul hc θ x

/-! ### `MForm.OmegaSpace` (D11) -/

/-- Meromorphic 1-forms with divisor `≥ -D` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X, Ω_D)`), defined
order-wise on the quotient (mirrors `LinSys`'s own primary definition). -/
def OmegaSpace (D : Divisor X) : Submodule ℂ (MForm X) where
  carrier := {Θ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ Θ.ord x}
  zero_mem' := fun x => by rw [ord_zero]; exact le_top
  add_mem' := by
    intro Θ H hΘ hH x
    exact le_trans (le_min (hΘ x) (hH x)) (ord_add Θ H x)
  smul_mem' := by
    intro c Θ hΘ x
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul, ord_zero]; exact le_top
    · rw [ord_smul hc]; exact hΘ x

theorem mem_omegaSpace_iff {D : Divisor X} {Θ : MForm X} :
    Θ ∈ OmegaSpace D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ Θ.ord x := Iff.rfl

/-- Index of speciality: `dim Ω(D)`. -/
noncomputable def i (D : Divisor X) : ℕ := Module.finrank ℂ (OmegaSpace D)

end MForm

/-! ### D11: the `Ω(D) ≅ L(D+K)` bridge -/

section OmegaLinSys

variable [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]

end OmegaLinSys

/-! ### D12: `Form1 ≃ₗ Ω(0)` (the holomorphic forms bridge) -/

/-- The forward leg of D12: a holomorphic 1-form as an element of `Ω(0)`. -/
noncomputable def form1ToOmega : Form1 X →ₗ[ℂ] MForm.OmegaSpace (0 : Divisor X) where
  toFun η := ⟨MForm.ofForm1 η, fun x => by
    have h0 : ((0 : Divisor X) x) = 0 := rfl
    rw [h0]
    simpa using MForm.ofForm1_ord_nonneg η x⟩
  map_add' η η' := Subtype.ext (congrArg MForm.mk (MFormData.ofForm1_add η η'))
  map_smul' c η := Subtype.ext (congrArg MForm.mk (MFormData.ofForm1_smul c η))

/-! ### `MLFormData` (D13, Forster §17.1–17.2) -/

/-- A form-level Mittag-Leffler datum: at finitely many points of `X`, a principal part read in
the preferred chart. A thin wrapper around residue-calculus's already-built `PrincipalPartData`. -/
structure MLFormData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  /-- The finite set of points carrying prescribed principal parts. -/
  pts : Finset X
  /-- The principal part prescribed at each marked point, read in that point's chart. -/
  data : ∀ x ∈ pts, PrincipalPartData (chartAt ℂ x).target

/-- `μ` realizes the principal parts of `Θ` at every point of `μ.pts` (read in each point's own
preferred chart; stated on classes via the lifted `MForm.laurentCoeffAt`). -/
def MLFormData.Realizes (μ : MLFormData X) (Θ : MForm X) : Prop :=
  ∀ x (hx : x ∈ μ.pts), ∀ k < 0,
    Θ.laurentCoeffAt x k = (μ.data x hx).coeff (chartAt ℂ x x) k

/-- The total residue prescribed by the datum. -/
noncomputable def MLFormData.totalRes (μ : MLFormData X) : ℂ :=
  ∑ x ∈ μ.pts.attach, (μ.data x.1 x.2).coeff (chartAt ℂ x.1 x.1) (-1)

end RS
