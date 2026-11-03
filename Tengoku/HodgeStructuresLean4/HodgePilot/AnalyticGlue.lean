import Tengoku.HodgeStructuresLean4.HodgePilot.Analytic
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.Topology.Algebra.GroupWithZero
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.AlgebraicGeometry.OpenImmersion
import Tengoku.Seed.AlgebraicGeometry.AlgClosed.Basic
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The analytic topology on the ℂ-points of a scheme over ℂ

`HodgePilot.Analytic` equips the ℂ-points `CPoints A = (A →ₐ[ℂ] ℂ)` of an affine
scheme `Spec A` with their analytic (euclidean) topology.  This file extends the
construction beyond the affine case, to the ℂ-points of an arbitrary scheme `X`
over ℂ — in particular to quasi-projective varieties — glued from affine charts.

Throughout, `X` is a scheme with a fixed structure morphism
`sX : X ⟶ Spec (CommRingCat.of ℂ)`, and its ℂ-points are the scheme-theoretic
sections `SPoints sX = {p : Spec (.of ℂ) ⟶ X // p ≫ sX = 𝟙}`.

* `awayHomeomorph` — **localization compatibility** (the affine seed of the gluing):
  for `f : A` and any localization `S` of `A` away from `f`, restriction along
  `A → S` is a homeomorphism from `CPoints S` onto the open subspace
  `{φ : CPoints A | φ f ≠ 0}`; in particular it is an open embedding
  (`isOpenEmbedding_awayRes`, `range_awayRes`).
* `Chart`, `probe`, `instTopSPoints` — an (affine) *chart* of `X` over ℂ is an open
  immersion `Spec A ⟶ X` of ℂ-schemes; each chart probes `CPoints A → SPoints sX`,
  and `SPoints sX` carries the **final topology from all charts**.  No cover is
  chosen: the topology is defined by the (large) family of all charts at once,
  so no cover-independence statement is needed to make it canonical.
* `continuous_probe` — the **key continuity lemma**: the map on points induced by an
  *arbitrary* morphism `Spec B ⟶ X` over ℂ (no open-immersion hypothesis) is
  continuous.  This is the Zariski-local argument of the classical construction:
  locally the morphism factors through a chart after inverting one element, and
  localization compatibility plus affine functoriality finish.
* `isOpenEmbedding_probeChart` — charts are open embeddings on points: the analytic
  space of ℂ-points of an affine open sits as an open subspace of `SPoints sX`.
* `affineSPointsHomeomorph` — the **affine comparison**: for `X = Spec A` the
  identification `bridge` of `CPoints A` with the scheme-theoretic ℂ-points is a
  homeomorphism for the two constructions.
* `affineOpenChart`, `exists_chart_mem` — every affine open of `X` is a chart (with
  the ℂ-algebra structure on its sections induced by `sX`), and the charts cover `X`.
* `mapSPoints`, `continuous_mapSPoints` — functoriality: a morphism of ℂ-schemes
  induces a continuous map on analytic spaces of ℂ-points.
* `toSpace`, `continuous_toSpace` — the comparison map from the analytic space of
  ℂ-points to the underlying (Zariski) space of `X` is continuous.

This is the topological layer only, the scheme-level germ of the classical
construction of Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst.
Fourier 6 (1956), §§1–2.  No analytic-space or manifold structure is put on the
point space, and no comparison theorem of any kind is claimed or provided.
-/

open Topology HodgePilot.Analytic AlgebraicGeometry CategoryTheory

noncomputable section

namespace HodgePilot.Analytic

/-! ## Localization compatibility

For `f : A`, the ℂ-points of a localization of `A` away from `f` form the open
subspace `{φ | φ f ≠ 0}` of the ℂ-points of `A`. -/

section Away

universe u v

variable {A : Type u} [CommRing A] [Algebra ℂ A] (f : A)
variable (S : Type v) [CommRing S] [Algebra ℂ S] [Algebra A S] [IsScalarTower ℂ A S]
  [IsLocalization.Away f S]

variable (A) in
/-- Restriction of a ℂ-point of the localization to `A`.-/
def awayRes : CPoints S → CPoints A := comap (IsScalarTower.toAlgHom ℂ A S)

/--
@isnad1 id=eq.0h4v.s7.f6a6b852da6a from=translated src=- shape=24d4e9c0 vocab=27b66c61
-/
lemma awayRes_apply (ψ : CPoints S) (a : A) : awayRes A S ψ a = ψ (algebraMap A S a) := rfl

/--
@isnad1 id=ne.0h4v.s7.bc0410b0c93c from=translated src=- shape=e0c51b76 vocab=cd8b7139
-/
lemma awayRes_ne_zero (ψ : CPoints S) : awayRes A S ψ f ≠ 0 :=
  (IsUnit.map ψ (IsLocalization.map_units S
    (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f))).ne_zero

/--
@isnad1 id=isunit.1h4v.s7.61186a940e2c from=translated src=- shape=9369742c vocab=d4aba260
-/
lemma isUnit_apply_powers (φ : CPoints A) (hφ : φ f ≠ 0) (y : Submonoid.powers f) :
    IsUnit (φ y) := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn, map_pow]
  exact (pow_ne_zero n hφ).isUnit

/-- A ℂ-point of `A` not vanishing at `f` lifts to the localization away from `f`.-/
def awayLift (φ : CPoints A) (hφ : φ f ≠ 0) : CPoints S :=
  IsLocalization.liftAlgHom (M := Submonoid.powers f) (S := S)
    (f := φ) (fun y => isUnit_apply_powers f φ hφ y)

/--
@isnad1 id=eq.1h5v.s7.1d6d7cf4298f from=translated src=- shape=eefbfe25 vocab=f4d1bf47
-/
@[simp]
lemma awayLift_algebraMap (φ : CPoints A) (hφ : φ f ≠ 0) (a : A) :
    awayLift f S φ hφ (algebraMap A S a) = φ a :=
  IsLocalization.lift_eq _ a

/--
@isnad1 id=eq.1h4v.s7.6bb564dc15ac from=translated src=- shape=ac22b9d5 vocab=f8c60f68
-/
lemma awayRes_awayLift (φ : CPoints A) (hφ : φ f ≠ 0) :
    awayRes A S (awayLift f S φ hφ) = φ :=
  AlgHom.ext fun a => awayLift_algebraMap f S φ hφ a

/-- The ℂ-points of a localization of `A` away from `f` are exactly the ℂ-points of `A`
not vanishing at `f`.-/
def awayEquiv : CPoints S ≃ {φ : CPoints A // φ f ≠ 0} where
  toFun ψ := ⟨awayRes A S ψ, awayRes_ne_zero f S ψ⟩
  invFun s := awayLift f S s.1 s.2
  left_inv ψ := by
    apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a => ?_)
    show awayLift f S (awayRes A S ψ) (awayRes_ne_zero f S ψ) (algebraMap A S a) =
      ψ (algebraMap A S a)
    rw [awayLift_algebraMap]
    rfl
  right_inv s := Subtype.ext (awayRes_awayLift f S s.1 s.2)

/--
@isnad1 id=continuo.0h2v.s6.9344b5ce17a1 from=translated src=- shape=f373645a vocab=f9c37cfb
-/
lemma continuous_awayRes : Continuous (awayRes A S) := continuous_comap _

/--
@isnad1 id=continuo.0h3v.s8.2500b6b26cea from=translated src=- shape=cb2c4e0d vocab=a07b7c49
-/
lemma continuous_awayEquiv : Continuous (awayEquiv f S) := by
  exact Continuous.subtype_mk (continuous_awayRes S) _

/--
@isnad1 id=continuo.0h3v.s8.129a66a44522 from=translated src=- shape=7ea3e6c5 vocab=46530e53
-/
lemma continuous_awayLift :
    Continuous fun s : {φ : CPoints A // φ f ≠ 0} => awayLift f S s.1 s.2 := by
  refine continuous_induced_rng.2 (continuous_pi fun x => ?_)
  show Continuous fun s : {φ : CPoints A // φ f ≠ 0} => awayLift f S s.1 s.2 x
  obtain ⟨⟨a, y⟩, hxy⟩ := IsLocalization.surj (M := Submonoid.powers f) (S := S) x
  dsimp only at hxy
  obtain ⟨n, hn⟩ := y.2
  have key : ∀ s : {φ : CPoints A // φ f ≠ 0},
      awayLift f S s.1 s.2 x = s.1 a * (s.1 f ^ n)⁻¹ := by
    intro s
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero n s.2), ← map_pow]
    have h1 := congrArg (awayLift f S s.1 s.2) hxy
    rw [map_mul, awayLift_algebraMap, awayLift_algebraMap, ← hn] at h1
    exact h1
  simp only [key]
  exact ((continuous_ev a).comp continuous_subtype_val).mul
    ((((continuous_ev f).comp continuous_subtype_val).pow n).inv₀
      fun s => pow_ne_zero n s.2)

/-- **Localization compatibility**: the ℂ-points of a localization of `A` away from `f`,
with their analytic topology, are homeomorphic to the open subspace `{φ | φ f ≠ 0}` of
the analytic space of ℂ-points of `A`.-/
def awayHomeomorph : CPoints S ≃ₜ {φ : CPoints A // φ f ≠ 0} where
  toEquiv := awayEquiv f S
  continuous_toFun := continuous_awayEquiv f S
  continuous_invFun := continuous_awayLift f S

/--
@isnad1 id=eq.0h3v.s9.2c468793a232 from=translated src=- shape=bd88b5a9 vocab=486889fa
-/
lemma awayRes_eq_val_comp : awayRes A S = Subtype.val ∘ (awayHomeomorph f S) := rfl

include f in
/--
@isnad1 id=isopenem.0h3v.s6.5ffd8115bb63 from=translated src=- shape=d82d4168 vocab=19e6a6e7
-/
theorem isOpenEmbedding_awayRes : IsOpenEmbedding (awayRes A S) := by
  rw [awayRes_eq_val_comp f S]
  exact ((isOpen_setOf_ne_zero f).isOpenEmbedding_subtypeVal).comp
    (awayHomeomorph f S).isOpenEmbedding

/--
@isnad1 id=eq.0h3v.s7.773f608838e8 from=translated src=- shape=0d1ec3b0 vocab=fcc16905
-/
theorem range_awayRes : Set.range (awayRes A S) = {φ : CPoints A | φ f ≠ 0} := by
  rw [awayRes_eq_val_comp f S, (awayHomeomorph f S).surjective.range_comp]
  exact Subtype.range_coe

end Away

/-! ## The generalized bridge

A morphism `Spec S ⟶ Spec R` compatible with the structure morphisms over ℂ comes from
a unique ℂ-algebra homomorphism (`Analytic.bridge` is the case `S = ℂ`). -/

section SpecHom

/-- A morphism `Spec S ⟶ Spec R` over `Spec ℂ` comes from a ℂ-algebra homomorphism
`R →ₐ[ℂ] S`.-/
def algHomOfSpecHom {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ structMor R = structMor S) : R →ₐ[ℂ] S where
  toRingHom := (Spec.preimage g).hom
  commutes' := fun c => by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap ℂ R) ≫ Spec.preimage g) =
        Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
      rw [Spec.map_comp, Spec.map_preimage]
      exact hg
    have h2 : CommRingCat.ofHom (algebraMap ℂ R) ≫ Spec.preimage g =
        CommRingCat.ofHom (algebraMap ℂ S) := Spec.map_injective h1
    have h3 := RingHom.congr_fun (congrArg CommRingCat.Hom.hom h2) c
    simpa using h3

/--
@isnad1 id=eq.1h3v.s7.91ad764fb46f from=translated src=- shape=b32bb825 vocab=843e73dc
-/
lemma SpecMap_algHomOfSpecHom {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S]
    [Algebra ℂ S] (g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ structMor R = structMor S) :
    Spec.map (CommRingCat.ofHom (algHomOfSpecHom g hg).toRingHom) = g := by
  show Spec.map (CommRingCat.ofHom (Spec.preimage g).hom) = g
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

end SpecHom

/-! ## The ℂ-points of a scheme over ℂ and their analytic topology -/

section Scheme

variable {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of ℂ))

/-- The scheme-theoretic ℂ-points of a scheme over ℂ: sections of the structure
morphism.  (Same carrier as in `AlgebraicGeometry.pointEquivClosedPoint`.)-/
abbrev SPoints : Type := {p : Spec (CommRingCat.of ℂ) ⟶ X // p ≫ sX = 𝟙 _}

/-- The map on ℂ-points induced by a morphism from an affine ℂ-scheme.-/
def probe {B : Type} [CommRing B] [Algebra ℂ B] (h : Spec (CommRingCat.of B) ⟶ X)
    (hh : h ≫ sX = structMor B) : CPoints B → SPoints sX := fun φ =>
  ⟨(bridge B φ).1 ≫ h, by rw [Category.assoc, hh]; exact (bridge B φ).2⟩

/--
@isnad1 id=eq.1h5v.s7.52d449996e8c from=translated src=- shape=0f32ac9d vocab=1a44c009
-/
lemma probe_coe {B : Type} [CommRing B] [Algebra ℂ B] (h : Spec (CommRingCat.of B) ⟶ X)
    (hh : h ≫ sX = structMor B) (φ : CPoints B) :
    (probe sX h hh φ).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ h := rfl

/-- An affine chart of a ℂ-scheme: an open immersion from an affine ℂ-scheme,
compatible with the structure morphisms.-/
structure Chart : Type 1 where
  /-- The coordinate ring of the chart.-/
  A : Type
  [commRing : CommRing A]
  [algebra : Algebra ℂ A]
  /-- The open immersion realizing the chart.-/
  hom : Spec (CommRingCat.of A) ⟶ X
  [isOpenImmersion : IsOpenImmersion hom]
  /-- Compatibility with the structure morphisms.-/
  over : hom ≫ sX = structMor A

attribute [instance] Chart.commRing Chart.algebra Chart.isOpenImmersion

/-- The analytic topology on the ℂ-points of a scheme over ℂ: the final topology from
all affine charts.  No affine cover is chosen — the family of all charts is canonical.-/
instance instTopSPoints : TopologicalSpace (SPoints sX) :=
  ⨆ c : Chart sX, TopologicalSpace.coinduced (probe sX c.hom c.over) (instTopCPoints c.A)

/--
@isnad1 id=eq.0h2v.s6.5489d948fcd1 from=translated src=- shape=00840e7c vocab=2148d0bf
-/
lemma topSPoints_eq : instTopSPoints sX =
    ⨆ c : Chart sX, TopologicalSpace.coinduced (probe sX c.hom c.over) (instTopCPoints c.A) :=
  rfl

/--
@isnad1 id=continuo.0h3v.s6.430a4766e7f2 from=translated src=- shape=451dcc86 vocab=73f02282
-/
theorem continuous_probeChart (c : Chart sX) : Continuous (probe sX c.hom c.over) := by
  rw [continuous_iff_coinduced_le, topSPoints_eq sX]
  exact le_iSup
    (fun c : Chart sX => TopologicalSpace.coinduced (probe sX c.hom c.over) (instTopCPoints c.A)) c

/-- Universal property of the analytic topology: a map out of `SPoints sX` is continuous
iff its composite with every chart probe is.
@isnad1 id=continuo.1h4v.s6.bf80adc8c878 from=translated src=- shape=13f1f396 vocab=75852898
-/
theorem continuous_of_probeCharts {T : Type*} [TopologicalSpace T] {k : SPoints sX → T}
    (H : ∀ c : Chart sX, Continuous (k ∘ probe sX c.hom c.over)) : Continuous k := by
  rw [continuous_iff_le_induced, topSPoints_eq sX, iSup_le_iff]
  intro c
  rw [coinduced_le_iff_le_induced, induced_compose]
  exact continuous_iff_le_induced.mp (H c)

/-- Openness in the analytic topology is detected on all charts.
@isnad1 id=iff.0h3v.s6.1baaca411a01 from=translated src=- shape=32ef7b3c vocab=c9c82696
-/
lemma isOpen_SPoints_iff {V : Set (SPoints sX)} :
    IsOpen V ↔ ∀ c : Chart sX, IsOpen (probe sX c.hom c.over ⁻¹' V) := by
  show IsOpen[⨆ c : Chart sX,
    TopologicalSpace.coinduced (probe sX c.hom c.over) (instTopCPoints c.A)] V ↔ _
  rw [isOpen_iSup_iff]
  exact forall_congr' fun c => isOpen_coinduced

/--
@isnad1 id=injectiv.0h3v.s5.b6b1c63113bc from=translated src=- shape=451dcc86 vocab=3e146fe2
-/
theorem injective_probeChart (c : Chart sX) : Function.Injective (probe sX c.hom c.over) := by
  intro φ ψ hfψ
  have h1 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ c.hom =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ c.hom := congrArg Subtype.val hfψ
  have h2 := Spec.map_injective ((cancel_mono c.hom).mp h1)
  have h3 := congrArg CommRingCat.Hom.hom h2
  rw [CommRingCat.hom_ofHom, CommRingCat.hom_ofHom] at h3
  exact AlgHom.coe_ringHom_injective h3

end Scheme

/-! ## The affine comparison -/

section AffineComparison

variable (A : Type) [CommRing A] [Algebra ℂ A]

/--
@isnad1 id=eq.0h1v.s9.9e8ff70c5f7b from=translated src=- shape=1ebd5ff3 vocab=5b79017e
-/
lemma bridge_eq_probe_id : ⇑(bridge A) = probe (structMor A) (𝟙 _) (Category.id_comp _) := by
  funext φ
  exact Subtype.ext (Category.comp_id _).symm

/--
@isnad1 id=continuo.0h1v.s9.8c3142215511 from=translated src=- shape=ba77d11b vocab=06f55269
-/
theorem continuous_bridge : Continuous (bridge A) := by
  rw [bridge_eq_probe_id A]
  exact continuous_probeChart (structMor A)
    { A := A, hom := 𝟙 _, over := Category.id_comp _ }

/--
@isnad1 id=continuo.0h1v.s9.8b5b5e294716 from=translated src=- shape=876efff4 vocab=399ab505
-/
theorem continuous_bridge_symm : Continuous (bridge A).symm := by
  apply continuous_of_probeCharts
  intro c
  have hkey : ⇑(bridge A).symm ∘ probe (structMor A) c.hom c.over =
      comap (algHomOfSpecHom c.hom c.over) := by
    funext φ
    rw [Function.comp_apply, Equiv.symm_apply_eq]
    refine Subtype.ext ?_
    show Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ c.hom =
      Spec.map (CommRingCat.ofHom ((comap (algHomOfSpecHom c.hom c.over) φ)).toRingHom)
    rw [show ((comap (algHomOfSpecHom c.hom c.over) φ)).toRingHom =
        φ.toRingHom.comp (algHomOfSpecHom c.hom c.over).toRingHom from rfl]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, SpecMap_algHomOfSpecHom]
  rw [hkey]
  exact continuous_comap _

/-- **The affine comparison**: for an affine scheme the scheme-level analytic space of
ℂ-points coincides, via `Analytic.bridge`, with the affine construction `CPoints A`.-/
def affineSPointsHomeomorph : CPoints A ≃ₜ SPoints (structMor A) where
  toEquiv := bridge A
  continuous_toFun := continuous_bridge A
  continuous_invFun := continuous_bridge_symm A

end AffineComparison

/-! ## Chart existence: affine opens are charts -/

section ChartExistence

variable {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of ℂ))

/-- Any affine open of `X`, with the ℂ-algebra structure on its sections induced by the
structure morphism, is a chart.-/
def affineOpenChart {U : X.Opens} (hU : IsAffineOpen U) : Chart sX :=
  letI : Algebra ℂ ↑Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ sX.appLE ⊤ U le_top).hom.toAlgebra
  { A := ↑Γ(X, U)
    hom := hU.fromSpec
    over := by
      show hU.fromSpec ≫ sX = Spec.map (CommRingCat.ofHom (algebraMap ℂ ↑Γ(X, U)))
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
        ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
      exact (IsAffineOpen.SpecMap_appLE_fromSpec sX (isAffineOpen_top _) hU le_top).symm }

end ChartExistence

/-! ## The key continuity lemma and its consequences -/

section Glue

variable {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of ℂ))

/--
@isnad1 id=iff.0h3v.s6.8d524f1f456f from=translated src=- shape=c23b3657 vocab=d24f6f40
-/
lemma mem_basicOpen_toZariski {B : Type} [CommRing B] [Algebra ℂ B] (φ : CPoints B) (g : B) :
    toZariski φ ∈ PrimeSpectrum.basicOpen g ↔ φ g ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  simp [toZariski, RingHom.mem_ker]

/-- Local factorization of an affine probe through a chart: near any ℂ-point whose
underlying scheme point lands in the chart, the probe factors, after inverting one
element, through the chart via localization compatibility.
@isnad1 id=ex.2h6v.s10.654fb98ba6d8 from=translated src=- shape=9c824d3a vocab=345a1736
-/
theorem exists_away_factor {B : Type} [CommRing B] [Algebra ℂ B]
    (h : Spec (CommRingCat.of B) ⟶ X) (hh : h ≫ sX = structMor B) (c : Chart sX)
    {φ₀ : CPoints B} (hc : h (toZariski φ₀) ∈ Set.range ⇑c.hom) :
    ∃ (g : B) (ρ : c.A →ₐ[ℂ] Localization.Away g), φ₀ g ≠ 0 ∧
      ∀ s : {φ : CPoints B // φ g ≠ 0},
        probe sX h hh s.1 =
          probe sX c.hom c.over (comap ρ (awayLift g (Localization.Away g) s.1 s.2)) := by
  have hV : IsOpen (⇑h ⁻¹' (Set.range ⇑c.hom)) :=
    (c.hom.isOpenEmbedding.isOpen_range).preimage h.continuous
  obtain ⟨s, ⟨g, rfl⟩, hxs, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hc hV
  have hg0 : φ₀ g ≠ 0 := (mem_basicOpen_toZariski φ₀ g).mp hxs
  have hrange : Set.range ⇑(Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ h)
      ⊆ Set.range ⇑c.hom := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    show Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) y ∈
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B))
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    have hy : PrimeSpectrum.comap (algebraMap B (Localization.Away g)) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) :=
      Set.mem_range_self y
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hy
  obtain ⟨l, hl⟩ : ∃ l', l' ≫ c.hom =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ h :=
    ⟨IsOpenImmersion.lift c.hom _ hrange, IsOpenImmersion.lift_fac c.hom _ hrange⟩
  have hstep : Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g))) ≫ structMor B =
      structMor (Localization.Away g) := by
    rw [structMor, structMor, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  have hlover : l ≫ structMor c.A = structMor (Localization.Away g) := by
    rw [← c.over, ← Category.assoc, hl, Category.assoc, hh, hstep]
  have hρ := SpecMap_algHomOfSpecHom l hlover
  refine ⟨g, algHomOfSpecHom l hlover, hg0, fun s => ?_⟩
  refine Subtype.ext ?_
  show Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ h =
    Spec.map (CommRingCat.ofHom ((awayLift g (Localization.Away g) s.1 s.2).comp
      (algHomOfSpecHom l hlover)).toRingHom) ≫ c.hom
  rw [show ((awayLift g (Localization.Away g) s.1 s.2).comp
      (algHomOfSpecHom l hlover)).toRingHom =
      (awayLift g (Localization.Away g) s.1 s.2).toRingHom.comp
        (algHomOfSpecHom l hlover).toRingHom from rfl]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, hρ, Category.assoc, hl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [show (awayLift g (Localization.Away g) s.1 s.2).toRingHom.comp
      (algebraMap B (Localization.Away g)) = s.1.toRingHom from
    congrArg AlgHom.toRingHom (awayRes_awayLift g (Localization.Away g) s.1 s.2)]

/-- The comparison map from the analytic space of ℂ-points to the underlying (Zariski)
space of the scheme.-/
def toSpace : SPoints sX → X := fun p => p.1 (IsLocalRing.closedPoint ℂ)

end Glue

/-! ## Functoriality -/

section Functoriality

variable {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of ℂ))

/-- Functoriality on points: a morphism of ℂ-schemes induces a map on ℂ-points.-/
def mapSPoints {Y : Scheme} (sY : Y ⟶ Spec (CommRingCat.of ℂ)) (k : X ⟶ Y)
    (hk : k ≫ sY = sX) : SPoints sX → SPoints sY := fun p =>
  ⟨p.1 ≫ k, by rw [Category.assoc, hk]; exact p.2⟩

/--
@isnad1 id=eq.0h2v.s5.d1f8ab23c81a from=translated src=- shape=cfa25909 vocab=b6c1b925
-/
theorem mapSPoints_id : mapSPoints sX sX (𝟙 X) (Category.id_comp sX) = id := by
  funext p
  exact Subtype.ext (Category.comp_id p.1)

/--
@isnad1 id=eq.2h8v.s7.72404262c739 from=translated src=- shape=ba034f7e vocab=d6693c14
-/
theorem mapSPoints_comp {Y Z : Scheme} (sY : Y ⟶ Spec (CommRingCat.of ℂ))
    (sZ : Z ⟶ Spec (CommRingCat.of ℂ)) (k : X ⟶ Y) (m : Y ⟶ Z)
    (hk : k ≫ sY = sX) (hm : m ≫ sZ = sY) :
    mapSPoints sX sZ (k ≫ m) (by rw [Category.assoc, hm, hk]) =
      mapSPoints sY sZ m hm ∘ mapSPoints sX sY k hk := by
  funext p
  exact Subtype.ext (Category.assoc _ _ _).symm

/-- For `X` locally of finite type over ℂ the carrier of the analytic space of ℂ-points
is equivalently the set of closed points of `X` (Nullstellensatz;
`AlgebraicGeometry.pointEquivClosedPoint` applied over ℂ).-/
def sPointsEquivClosedPoints [LocallyOfFiniteType sX] : SPoints sX ≃ closedPoints X :=
  pointEquivClosedPoint sX

end Functoriality

end HodgePilot.Analytic
