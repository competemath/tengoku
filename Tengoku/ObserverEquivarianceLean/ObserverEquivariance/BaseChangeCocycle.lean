import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.BaseChange
import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Cocycles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Changing parallel normalization and the class in `H¹(H,G)` (paper `sec:normalization`)

Bridge between `BaseChange` (the datum-level `prop:basechange`) and `Cocycles` (pure nonabelian
group cohomology of the fixed split extension `G ⋊_θ H`).

Paper labels covered (paragraph after `prop:basechange` and the cocycle paragraph of
`sec:normalization`):

* `baseChange_twistFactor_eq_coboundary`: the factor `z_c(A) = c θ_A(c⁻¹)` of `prop:basechange`
  is `OECocycle.coboundary θ c A`, so its cocycle identity is `OECocycle.coboundary_mul`;
* `liftHomθOver_rebase_conj_ker`: "The conjugacy class of the canonical section under the kernel
  is independent of parallel normalization" — the new canonical section, transported back along
  `autBoxGθOverCongr`, is conjugate to the old one by ONE element of `(ΦθOver d H θ).ker`,
  uniformly in `A` (namely `Λ_c`);
* `liftHomθOver_rebase_semidirect`: read in the FIXED semidirect coordinates
  `autBoxGθOverMulEquivSemidirect d` of the old normalization, the new canonical section is the
  cocycle section `A ↦ (z_c(A), A)` of the coboundary `z_c` (with `c`, not `c⁻¹`);
* `liftHomθOver_rebase_sectionConj`: in those coordinates it is conjugate to the old canonical
  section `inr` by `(c, 1)`;
* `liftHomθOver_rebase_class`: its class in `H¹(H,G)` (via `OECocycle.H1EquivSectionClasses`) is
  the distinguished trivial class, i.e. "changing parallel normalization conjugates the canonical
  section without changing its class in `H¹(H,G)`".  The extension `G ⋊_θ H` itself is fixed
  throughout (it is the target of `autBoxGθOverMulEquivSemidirect d`), so the underlying extension
  does not change either.

As in `BaseChange`, `hact`/`hreind` fix the right action and the transport, and
`hc : ∀ s, d'.base s = d.act (d.base s) c` records the change of parallel basepoints.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G] {p : O ⥤ S}

/-- The factor `z_c(A) = c θ_A(c⁻¹)` of `prop:basechange` is the nonabelian `1`-coboundary
    `OECocycle.coboundary θ c A` (paper `sec:normalization`, cocycle paragraph); hence
    `baseChange_twistFactor_mul` is `OECocycle.coboundary_mul`.-/
theorem _root_.Tengoku.ObserverEquivarianceLean.baseChange_twistFactor_eq_coboundary {H : Type*} [Group H] (θ : H →* MulAut G) (c : G)
    (A : H) : c * θ A c⁻¹ = OECocycle.coboundary θ c A := rfl

section Rebase

variable (d d' : OEData G p) (hact : ∀ x g, d'.act x g = d.act x g)
  (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    d'.reind u y hy = d.reind u y hy)
  {c : G} (hc : ∀ s, d'.base s = d.act (d.base s) c)
  (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)

variable [IsConnected S]

/-- The new canonical twisted section `Ã'_θ`, read in the fixed semidirect coordinates of the
    old normalization, as a section of `rightHom : G ⋊_θ H →* H` (paper `sec:normalization`,
    paragraph after `prop:basechange`): `A ↦ ψ_d((autBoxGθOverCongr)⁻¹ Ã'_θ)`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftHomθOverRebaseSection : OECocycle.SemidirectSection θ :=
  ⟨(autBoxGθOverMulEquivSemidirect d H θ).toMonoidHom.comp
      ((autBoxGθOverCongr d d' hact hreind H θ).symm.toMonoidHom.comp (liftHomθOver d' H θ)),
    fun A => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        autBoxGθOverMulEquivSemidirect_apply_right]
      rfl⟩

end Rebase
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
