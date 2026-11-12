import Tengoku.Seed.Topology.Baire.BaireMeasurable
import Tengoku.Seed.Topology.Baire.Lemmas
import Tengoku.Seed.Topology.Bases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kuratowski--Ulam for sections of a product

This file proves the classical category analogue of Fubini's theorem in the
form needed by Maxwell's closure argument.  Mathlib already provides the
residual filter and sets with the property of Baire, but not the corresponding
fiber theorem.
-/

noncomputable section

open Filter Set TopologicalSpace
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The vertical section of a subset of a product over a point in the first
factor.-/
def productFiber {X Y : Type*} (D : Set (X × Y)) (x : X) : Set Y :=
  {y | (x, y) ∈ D}

@[simp]
theorem mem_productFiber {X Y : Type*} {D : Set (X × Y)} {x : X} {y : Y} :
    y ∈ productFiber D x ↔ (x, y) ∈ D :=
  Iff.rfl

@[simp]
theorem productFiber_compl {X Y : Type*} (D : Set (X × Y)) (x : X) :
    productFiber Dᶜ x = (productFiber D x)ᶜ :=
  rfl

/-- For an open dense subset of a product, the set of base points whose
vertical section is dense is residual.  Second countability of the fiber is
the countability input in the usual basis proof.-/
theorem eventually_residual_dense_productFiber_of_open_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y]
    {G : Set (X × Y)} (hGopen : IsOpen G) (hGdense : Dense G) :
    ∀ᶠ x in residual X, Dense (productFiber G x) := by
  let P : countableBasis Y → Set X := fun V =>
    Prod.fst '' (G ∩ (Set.univ ×ˢ (V : Set Y)))
  have hPopen : ∀ V : countableBasis Y, IsOpen (P V) := by
    intro V
    exact isOpenMap_fst _
      (hGopen.inter (isOpen_univ.prod (isOpen_of_mem_countableBasis V.property)))
  have hPdense : ∀ V : countableBasis Y, Dense (P V) := by
    intro V
    rw [dense_iff_inter_open]
    intro U hUopen hUnonempty
    have hVopen : IsOpen (V : Set Y) :=
      isOpen_of_mem_countableBasis V.property
    have hVnonempty : (V : Set Y).Nonempty :=
      nonempty_of_mem_countableBasis V.property
    obtain ⟨z, hzprod, hzG⟩ := hGdense.inter_open_nonempty
      (U ×ˢ (V : Set Y)) (hUopen.prod hVopen)
        (hUnonempty.prod hVnonempty)
    refine ⟨z.1, hzprod.1, ?_⟩
    exact ⟨z, ⟨hzG, ⟨Set.mem_univ z.1, hzprod.2⟩⟩, rfl⟩
  have hPeventually : ∀ V : countableBasis Y, P V ∈ residual X :=
    fun V => residual_of_dense_open (hPopen V) (hPdense V)
  filter_upwards [eventually_countable_forall.mpr hPeventually] with x hx
  rw [(isBasis_countableBasis Y).dense_iff]
  intro V hV hVnonempty
  let V' : countableBasis Y := ⟨V, hV⟩
  obtain ⟨z, hz, hzx⟩ := hx V'
  refine ⟨z.2, ?_, ?_⟩
  · exact hz.2.2
  · change (x, z.2) ∈ G
    rw [← hzx]
    simpa only [Prod.eta] using hz.1

/-- A residual subset of a product has residual vertical sections at
residually many base points.-/
theorem eventually_residual_productFiber_of_mem_residual
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y]
    {G : Set (X × Y)} (hG : G ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, productFiber G x ∈ residual Y := by
  obtain ⟨S, hSopen, hSdense, hScountable, hSsub⟩ :=
    mem_residual_iff.mp hG
  have hsectionDense : ∀ U ∈ S,
      ∀ᶠ x in residual X, Dense (productFiber U x) := by
    intro U hU
    exact eventually_residual_dense_productFiber_of_open_dense
      (hSopen U hU) (hSdense U hU)
  filter_upwards [eventually_countable_ball hScountable |>.mpr hsectionDense]
    with x hx
  have hsections :
      (⋂ U, ⋂ hU : U ∈ S, productFiber U x) ∈ residual Y := by
    apply (countable_bInter_mem hScountable).mpr
    intro U hU
    exact residual_of_dense_open
      ((hSopen U hU).preimage
        (continuous_const.prodMk continuous_id))
      (hx U hU)
  apply Filter.mem_of_superset hsections
  intro y hy
  apply hSsub
  rw [Set.mem_sInter]
  intro U hU
  simp only [Set.mem_iInter] at hy
  exact hy U hU

/-- Forward Kuratowski--Ulam: a meagre subset of a product has meagre
vertical sections at residually many base points.-/
theorem IsMeagre.eventually_isMeagre_productFiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology Y]
    {D : Set (X × Y)} (hD : IsMeagre D) :
    ∀ᶠ x in residual X, IsMeagre (productFiber D x) := by
  have h := eventually_residual_productFiber_of_mem_residual
    (X := X) (Y := Y) hD
  filter_upwards [h] with x hx
  change (productFiber D x)ᶜ ∈ residual Y
  simpa using hx

/-- In a Baire space, a meagre set has empty interior.-/
theorem IsMeagre.interior_eq_empty
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {A : Set X} (hA : IsMeagre A) : interior A = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact
    (not_isMeagre_of_isOpen isOpen_interior ⟨x, hx⟩)
      (hA.mono interior_subset)

end AbelFormalization
