/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.Algebra.Ring.Hom.Defs
import Tengoku.Seed.Algebra.Group.Hom.Instances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# K-theoretic specialization along a deformation, abstractly

* `KSpecialization.Data`: Fulton's specialization `σ : G₀(X) → G₀(M₀)` for a family over `𝔸¹`
  (pull back to `X × 𝔾ₘ`, extend by localisation, apply the Gysin map of the special fibre),
  with `sigma_eq` and naturality `Hom.sigma_comm`.
* `fibre_restrictions_eq`: rigidity of the fibre restrictions of `K₀(ℙ¹_Z)`.
* `adams_transport`: the Fulton–Lang deformation argument transporting Adams–Riemann–Roch from
  the zero section `Z ↪ ℙ(N ⊕ 1)` to an arbitrary regular closed immersion `Z ↪ X`, with every
  geometric input an explicit hypothesis. See `notes/agents/arch-K-specialization.md`.
-/

noncomputable section

universe u

namespace KSpecialization

/-! ### Fulton's specialization map, abstractly -/

/-- Specialization data for a family `ρ : M → 𝔸¹` with special fibre `M₀` and generic part
`U = M ∖ M₀ ≅ X × 𝔾ₘ`: `GM, G0, GU, GX` stand for `G₀(M), G₀(M₀), G₀(U), G₀(X)`.-/
structure Data (GX GM GU G0 : Type*) [AddCommGroup GX] [AddCommGroup GM] [AddCommGroup GU]
    [AddCommGroup G0] where
  /-- open restriction `G₀(M) → G₀(U)`-/
  restrict : GM →+ GU
  /-- localisation, surjectivity (coherent sheaves extend from `U` to `M`)-/
  restrict_surjective : Function.Surjective restrict
  /-- pushforward from the special fibre-/
  push0 : G0 →+ GM
  /-- localisation, exactness in the middle-/
  ker_le_range : restrict.ker ≤ push0.range
  /-- Gysin restriction `j₀^!` to the special fibre-/
  gysin0 : GM →+ G0
  /-- `j₀^! j₀_* = 0` (trivial normal bundle; `PrincipalGysin.gysin_comp_pushDivisor`)-/
  gysin_push : gysin0.comp push0 = 0
  /-- flat pullback `G₀(X) → G₀(X × 𝔾ₘ)`-/
  pullGm : GX →+ GU

namespace Data

variable {GX GM GU G0 : Type*} [AddCommGroup GX] [AddCommGroup GM] [AddCommGroup GU]
  [AddCommGroup G0] (D : Data GX GM GU G0)

/--
@isnad1 id=eq.1h6v.s7.9fe4be61498b from=translated src=- shape=7da5df27 vocab=9ac76256
-/
theorem gysin_eq_zero_of_restrict {m : GM} (hm : D.restrict m = 0) : D.gysin0 m = 0 := by
  obtain ⟨z, rfl⟩ := D.ker_le_range hm
  exact DFunLike.congr_fun D.gysin_push z

/--
@isnad1 id=le.0h5v.s6.cbfbe9b68e89 from=translated src=- shape=30b136a7 vocab=44f4707c
-/
theorem ker_restrict_le_ker_gysin : D.restrict.ker ≤ D.gysin0.ker := fun _ hm =>
  D.gysin_eq_zero_of_restrict hm

/-- `j₀^!` descended to `G₀(U)`.-/
def descend : GU →+ G0 :=
  (QuotientAddGroup.lift D.restrict.ker D.gysin0 D.ker_restrict_le_ker_gysin).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective D.restrict D.restrict_surjective).symm.toAddMonoidHom

/--
@isnad1 id=eq.0h6v.s7.79a5efc59534 from=translated src=- shape=d176735a vocab=d0acb8ae
-/
@[simp]
theorem descend_restrict (m : GM) : D.descend (D.restrict m) = D.gysin0 m := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective D.restrict D.restrict_surjective).symm
      (D.restrict m) = QuotientAddGroup.mk m := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [descend, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, h]
  rfl

/-- **Fulton's specialization** `σ : G₀(X) → G₀(M₀)`: pull back to `X × 𝔾ₘ`, extend to `M`,
restrict to the special fibre by `j₀^!`.-/
def sigma : GX →+ G0 := D.descend.comp D.pullGm

/--
@isnad1 id=eq.1h7v.s8.e13379cfcc25 from=translated src=- shape=557c46b7 vocab=50513bcf
-/
theorem sigma_eq {x : GX} {m : GM} (hm : D.restrict m = D.pullGm x) :
    D.sigma x = D.gysin0 m := by
  simp [sigma, ← hm]

end Data

/-- A morphism of specialization data (e.g. induced by a proper map of families, or by the
closed immersion `Z × 𝔸¹ ↪ M°_Z X`): compatible maps on all four groups.-/
structure Hom {GX GM GU G0 GX' GM' GU' G0' : Type*} [AddCommGroup GX] [AddCommGroup GM]
    [AddCommGroup GU] [AddCommGroup G0] [AddCommGroup GX'] [AddCommGroup GM']
    [AddCommGroup GU'] [AddCommGroup G0'] (D : Data GX GM GU G0) (D' : Data GX' GM' GU' G0') where
  /-- map on `G₀(X)`-/
  fX : GX →+ GX'
  /-- map on `G₀(M)`-/
  fM : GM →+ GM'
  /-- map on `G₀(U)`-/
  fU : GU →+ GU'
  /-- map on `G₀(M₀)`-/
  f0 : G0 →+ G0'
  /-- compatibility with open restriction-/
  restrict_comm : ∀ m, D'.restrict (fM m) = fU (D.restrict m)
  /-- compatibility with the special-fibre Gysin map-/
  gysin_comm : ∀ m, D'.gysin0 (fM m) = f0 (D.gysin0 m)
  /-- compatibility with pullback to `X × 𝔾ₘ`-/
  pull_comm : ∀ x, D'.pullGm (fX x) = fU (D.pullGm x)

/-- **Specialization is natural**: `σ' ∘ f_X = f₀ ∘ σ`.
@isnad1 id=eq.0h12v.s8.72cd680b9a7b from=translated src=- shape=0520f0e3 vocab=40044ee7
-/
theorem Hom.sigma_comm {GX GM GU G0 GX' GM' GU' G0' : Type*} [AddCommGroup GX] [AddCommGroup GM]
    [AddCommGroup GU] [AddCommGroup G0] [AddCommGroup GX'] [AddCommGroup GM']
    [AddCommGroup GU'] [AddCommGroup G0'] {D : Data GX GM GU G0} {D' : Data GX' GM' GU' G0'}
    (f : Hom D D') (x : GX) : D'.sigma (f.fX x) = f.f0 (D.sigma x) := by
  obtain ⟨m, hm⟩ := D.restrict_surjective (D.pullGm x)
  rw [D.sigma_eq hm, D'.sigma_eq (m := f.fM m), f.gysin_comm]
  rw [f.restrict_comm, hm, f.pull_comm]

/-! ### Transport of the Adams–Riemann–Roch identity along the deformation (ℙ¹ route) -/

/-- Rigidity of `K₀(ℙ¹_Z)`: if every class is `a + b·h` with `a, b` pulled back from `Z`, then any
two ring retractions of the pullback sending `h ↦ 1` (restrictions to the fibres `0` and `∞`)
coincide.
@isnad1 id=eq.5h6v.s8.e0bc4cf7225a from=translated src=- shape=5db54c99 vocab=ab124287
-/
theorem fibre_restrictions_eq {KZ KW : Type*} [CommRing KZ] [CommRing KW] (pr : KZ →+* KW)
    (h : KW) (hspan : ∀ w, ∃ a b, w = pr a + pr b * h) (r₀ r₁ : KW →+* KZ)
    (h₀ : ∀ a, r₀ (pr a) = a) (h₁ : ∀ a, r₁ (pr a) = a) (hh₀ : r₀ h = 1) (hh₁ : r₁ h = 1) :
    r₀ = r₁ := by
  ext w
  obtain ⟨a, b, rfl⟩ := hspan w
  simp [h₀, h₁, hh₀, hh₁]

/-- **Deformation transport** (Fulton–Lang VI, `M = Bl_{Z×∞}(X × ℙ¹)`, `W = Z × ℙ¹ ↪ M`,
`X = M₀`, `P = ℙ(N ⊕ 1) ⊂ M_∞`). All maps are additive, so the statement applies verbatim after
inverting `j` (`KLoc`). Hypotheses:
* `hsupp`: localisation on `M` — a class vanishing on `M ∖ W` is pushed forward from `W`;
* `hresψ, hresF`: `ψ` commutes with open restriction and `res ∘ F_* = 0`;
* `hbc₀, hbcP`: Tor-independent base change `j₀^* F_* = i_* r₀`, `j_P^* F_* = s_* r_∞`;
* `hψ₀, hψP, hψr₀, hψr₁`: naturality of `ψ` for the four restrictions;
* `hθ₀, hθ₁`: the normal bundle of `W` restricts to `N` at both ends;
* `hkoszul`: Adams–RR for the zero section `s : Z ↪ P` (`adams_push_zeroSection`);
* `hπs`: `π_* s_* = id` (`π : P → Z` proper, `s` a section);
* `hrigid`: `r₀ = r_∞` (`fibre_restrictions_eq`).
Conclusion: Adams–RR for `i : Z ↪ X`.
@isnad1 id=eq.16h25v.s11.4804e8cc3494 from=translated src=- shape=a6f17ccc vocab=71e78412
-/
theorem adams_transport
    {KM KX KP KU KW KZ : Type*} [AddCommGroup KM] [AddCommGroup KX] [AddCommGroup KP]
    [AddCommGroup KU] [CommRing KW] [CommRing KZ]
    (Fp : KW →+ KM) (ip : KZ →+ KX) (sp : KZ →+ KP) (πp : KP →+ KZ)
    (res : KM →+ KU) (j₀ : KM →+ KX) (jP : KM →+ KP) (r₀ r₁ : KW →+* KZ) (pr : KZ →+* KW)
    (ψM : KM →+ KM) (ψX : KX →+ KX) (ψP : KP →+ KP) (ψU : KU →+ KU)
    (ψW : KW →+ KW) (ψZ : KZ →+ KZ) (θW : KW) (θZ : KZ)
    (hsupp : ∀ m, res m = 0 → ∃ w, Fp w = m)
    (hresψ : ∀ m, res (ψM m) = ψU (res m)) (hresF : ∀ w, res (Fp w) = 0)
    (hbc₀ : ∀ w, j₀ (Fp w) = ip (r₀ w)) (hbcP : ∀ w, jP (Fp w) = sp (r₁ w))
    (hψ₀ : ∀ m, j₀ (ψM m) = ψX (j₀ m)) (hψP : ∀ m, jP (ψM m) = ψP (jP m))
    (hψr₀ : ∀ w, r₀ (ψW w) = ψZ (r₀ w)) (hψr₁ : ∀ w, r₁ (ψW w) = ψZ (r₁ w))
    (hθ₀ : r₀ θW = θZ) (hθ₁ : r₁ θW = θZ)
    (hpr₀ : ∀ a, r₀ (pr a) = a) (hpr₁ : ∀ a, r₁ (pr a) = a)
    (hkoszul : ∀ z, ψP (sp z) = sp (θZ * ψZ z))
    (hπs : ∀ z, πp (sp z) = z) (hrigid : r₀ = r₁) (x : KZ) :
    ψX (ip x) = ip (θZ * ψZ x) := by
  set y := pr x
  set e := ψM (Fp y) - Fp (θW * ψW y) with he
  have hres : res e = 0 := by
    rw [he, map_sub, hresψ, hresF, hresF, map_zero, sub_zero]
  obtain ⟨w, hw⟩ := hsupp e hres
  -- restriction of `e` to `P` vanishes: the Koszul case
  have hP : jP e = 0 := by
    rw [he, map_sub, hψP, hbcP, hbcP, hkoszul, map_mul r₁, hθ₁, hψr₁, hpr₁, sub_self]
  have hw₁ : r₁ w = 0 := by
    have : sp (r₁ w) = 0 := by rw [← hbcP, hw, hP]
    rw [← hπs (r₁ w), this, map_zero]
  -- restriction of `e` to `X = M₀`
  have hX : j₀ e = ψX (ip x) - ip (θZ * ψZ x) := by
    rw [he, map_sub, hψ₀, hbc₀, hbc₀, map_mul r₀, hθ₀, hψr₀, hpr₀]
  have : j₀ e = 0 := by rw [← hw, hbc₀, hrigid, hw₁, map_zero]
  rw [← sub_eq_zero, ← hX, this]

end KSpecialization
