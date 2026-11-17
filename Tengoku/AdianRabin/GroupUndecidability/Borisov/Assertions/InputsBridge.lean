import Tengoku.AdianRabin.GroupUndecidability.Borisov.Assertions.AssertionIV
import Tengoku.AdianRabin.GroupUndecidability.Borisov.Model.ContextNormalForm
import Tengoku.AdianRabin.GroupUndecidability.Borisov.Model.Intersections
import Tengoku.AdianRabin.GroupUndecidability.Borisov.Assertions.AssertionV

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace BorisovInputsBridge

open BorisovIntersections
open BorisovG0HNN
open BorisovG0NormalForm
open BorisovHNNModel
open BorisovCStage
open BorisovContextNormalForm
open BorisovAssertionIV

noncomputable section

/--
@isnad1 id=eq.0h1v.s7.8f1246aface5 from=translated src=- shape=aa6bf7df vocab=54390e41
-/
@[simp] theorem g0Equiv_stable
    (beta : Fin 2) :
    g0Equiv (BorisovIntersections.stable beta) =
      BorisovCStage.stable3 beta := by
  rw [g0Equiv_apply]
  fin_cases beta <;>
    simp [BorisovCStage.stable3, BorisovG0HNN.hnnS1,
      BorisovG0HNN.hnnS2]

/--
@isnad1 id=eq.0h2v.s7.64c3e02e37df from=translated src=- shape=511e7c8c vocab=1b67cb23
-/
@[simp] theorem g0Equiv_uBasis
    (datum : Thue.StandingDatum) (q : Basis) :
    g0Equiv (BorisovIntersections.uBasis datum q) =
      BorisovCStage.uBasis datum q := by
  cases q with
  | inl beta =>
      exact g0Equiv_stable beta
  | inr i =>
      change g0Equiv (BorisovIntersections.a datum i) =
        BorisovCStage.a3 datum i
      rw [g0Equiv_apply, toHNN_a]
      rfl

/--
@isnad1 id=eq.0h2v.s7.8fc92d0741af from=translated src=- shape=511e7c8c vocab=f6ccc23e
-/
@[simp] theorem g0Equiv_vBasis
    (datum : Thue.StandingDatum) (q : Basis) :
    g0Equiv (BorisovIntersections.vBasis datum q) =
      BorisovCStage.vBasis datum q := by
  cases q with
  | inl beta =>
      exact g0Equiv_stable beta
  | inr i =>
      change g0Equiv (BorisovIntersections.b datum i) =
        BorisovCStage.b3 datum i
      rw [g0Equiv_apply, toHNN_b]
      rfl

/-- Transporting the displayed source-basis lift through `g0Equiv` gives the
semantic source-basis lift.
@isnad1 id=eq.0h2v.s9.07197b30a012 from=translated src=- shape=8263a7d0 vocab=1a7939b8
-/
theorem g0Equiv_uLift
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) :
    g0Equiv (FreeGroup.lift (BorisovIntersections.uBasis datum) w) =
      BorisovCStage.uLift datum w := by
  let f : FreeGroup Basis →* BorisovHNNModel.Gamma3 :=
    g0Equiv.toMonoidHom.comp
      (FreeGroup.lift (BorisovIntersections.uBasis datum))
  have hf : f = BorisovCStage.uLift datum := by
    apply FreeGroup.ext_hom
    intro q
    simpa [f, BorisovCStage.uLift] using g0Equiv_uBasis datum q
  exact DFunLike.congr_fun hf w

/-- Transporting the displayed target-basis lift through `g0Equiv` gives the
semantic target-basis lift.
@isnad1 id=eq.0h2v.s9.b9069de01835 from=translated src=- shape=8263a7d0 vocab=c0f0e3f5
-/
theorem g0Equiv_vLift
    (datum : Thue.StandingDatum) (w : FreeGroup Basis) :
    g0Equiv (FreeGroup.lift (BorisovIntersections.vBasis datum) w) =
      BorisovCStage.vLift datum w := by
  let f : FreeGroup Basis →* BorisovHNNModel.Gamma3 :=
    g0Equiv.toMonoidHom.comp
      (FreeGroup.lift (BorisovIntersections.vBasis datum))
  have hf : f = BorisovCStage.vLift datum := by
    apply FreeGroup.ext_hom
    intro q
    simpa [f, BorisovCStage.vLift] using g0Equiv_vBasis datum q
  exact DFunLike.congr_fun hf w

/-- Assertion IV in the four-generator presentation supplies exactly the
freeness input used to construct the semantic `c`-HNN extension.
@isnad1 id=rankfive.1h1v.s2.3af0dee5ab42 from=translated src=- shape=6321fd23 vocab=0dab7870
-/
theorem rankFiveFree_of_assertionIV
    (datum : Thue.StandingDatum) (hIV : AssertionIV datum) :
    RankFiveFree datum where
  u_injective := by
    intro x y hxy
    apply hIV.u_free
    apply g0Equiv.injective
    rw [g0Equiv_uLift, g0Equiv_uLift]
    exact hxy

  v_injective := by
    intro x y hxy
    apply hIV.v_free
    apply g0Equiv.injective
    rw [g0Equiv_vLift, g0Equiv_vLift]
    exact hxy

/-- Borisov's Assertion IV, transported from the four-generator
presentation to the concrete iterated-HNN model used by the later stages.
@isnad1 id=rankfive.0h1v.s2.479b1b12cf5c from=translated src=- shape=5c11bb93 vocab=f421ec22
-/
theorem rankFiveFree (datum : Thue.StandingDatum) : RankFiveFree datum :=
  rankFiveFree_of_assertionIV datum (assertionIV datum)

/-- The base-intersection input needed after the `c`-stage follows directly
from the strengthened, base-exclusion form of Assertion IV.  This bypasses
the weaker presentation-level `AssertionV` interface: a nontrivial word in
either displayed rank-five basis has a nonempty flat reduced expansion and
therefore cannot lie in the embedded `<d,e>` base.
@isnad1 id=baseinte.0h1v.s2.084c783267e8 from=translated src=- shape=5c11bb93 vocab=6987f851
-/
theorem baseIntersections (datum : Thue.StandingDatum) :
    BaseIntersections datum where
  u_inf_DE := by
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨w, rfl⟩
      by_cases hw : w = 1
      · subst w
        simp
      · exfalso
        apply uLift_not_mem_DE3_of_ne_one datum hw
        rw [← g0Equiv_apply, g0Equiv_uLift]
        exact hx.2
    · exact bot_le
  v_inf_DE := by
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨w, rfl⟩
      by_cases hw : w = 1
      · subst w
        simp
      · exfalso
        apply vLift_not_mem_DE3_of_ne_one datum hw
        rw [← g0Equiv_apply, g0Equiv_vLift]
        exact hx.2
    · exact bot_le

/-! ## The `J_beta` intersections in the semantic `Gamma3` model -/

/-- The semantic copy of `J_beta = <d,e,s_beta>` inside the concrete
iterated-HNN model `Gamma3`.-/
def J3 (beta : Fin 2) : Subgroup BorisovHNNModel.Gamma3 :=
  Subgroup.closure
    ({d3, e3, BorisovCStage.stable3 beta} :
      Set BorisovHNNModel.Gamma3)

/-- The semantic cyclic subgroup `<s_beta>` inside `Gamma3`.-/
def stableCyclic3 (beta : Fin 2) :
    Subgroup BorisovHNNModel.Gamma3 :=
  Subgroup.closure
    ({BorisovCStage.stable3 beta} :
      Set BorisovHNNModel.Gamma3)

/--
@isnad1 id=eq.0h0v.s7.19886d80731a from=translated src=- shape=501f93a1 vocab=5461df01
-/
@[simp] theorem g0Equiv_d :
    g0Equiv BorisovIntersections.d = d3 := by
  change toHNN presentedD = hnnD
  exact toHNN_presentedD

/--
@isnad1 id=eq.0h0v.s7.133b4c5d3a3a from=translated src=- shape=501f93a1 vocab=185abc5f
-/
@[simp] theorem g0Equiv_e :
    g0Equiv BorisovIntersections.e = e3 := by
  change toHNN presentedE = hnnE
  exact toHNN_presentedE

private theorem g0Equiv_symm_mem_J_of_mem_J3
    (beta : Fin 2) {x : BorisovHNNModel.Gamma3}
    (hx : x ∈ J3 beta) :
    g0Equiv.symm x ∈ BorisovIntersections.J beta := by
  let K : Subgroup BorisovHNNModel.Gamma3 :=
    (BorisovIntersections.J beta).comap g0Equiv.symm.toMonoidHom
  have hle : J3 beta ≤ K := by
    rw [J3, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · change g0Equiv.symm d3 ∈ BorisovIntersections.J beta
      rw [← g0Equiv_d]
      simp only [MulEquiv.symm_apply_apply]
      apply Subgroup.subset_closure
      simp
    · change g0Equiv.symm e3 ∈ BorisovIntersections.J beta
      rw [← g0Equiv_e]
      simp only [MulEquiv.symm_apply_apply]
      apply Subgroup.subset_closure
      simp
    · change
        g0Equiv.symm (BorisovCStage.stable3 beta) ∈
          BorisovIntersections.J beta
      rw [← g0Equiv_stable]
      simp only [MulEquiv.symm_apply_apply]
      exact BorisovIntersections.stable_mem_J beta
  exact hle hx

private theorem g0Equiv_mem_stableCyclic3_of_mem_stableCyclic
    (beta : Fin 2) {x : BorisovIntersections.G0}
    (hx : x ∈ BorisovIntersections.stableCyclic beta) :
    g0Equiv x ∈ stableCyclic3 beta := by
  let K : Subgroup BorisovIntersections.G0 :=
    (stableCyclic3 beta).comap g0Equiv.toMonoidHom
  have hle : BorisovIntersections.stableCyclic beta ≤ K := by
    rw [BorisovIntersections.stableCyclic, Subgroup.closure_le,
      Set.singleton_subset_iff]
    change
      g0Equiv (BorisovIntersections.stable beta) ∈ stableCyclic3 beta
    rw [g0Equiv_stable]
    exact Subgroup.subset_closure (Set.mem_singleton _)
  exact hle hx

/--
@isnad1 id=le.0h2v.s6.104c01e60498 from=translated src=- shape=3b656e49 vocab=0504c3a6
-/
theorem stableCyclic3_le_U (datum : Thue.StandingDatum) (beta : Fin 2) :
    stableCyclic3 beta ≤ U datum := by
  rw [stableCyclic3, Subgroup.closure_le, Set.singleton_subset_iff]
  exact ⟨FreeGroup.of (Sum.inl beta), by
    simp [BorisovCStage.uLift, BorisovCStage.uBasis]⟩

/--
@isnad1 id=le.0h2v.s6.1e310f8ee8ea from=translated src=- shape=3b656e49 vocab=c98efac7
-/
theorem stableCyclic3_le_V (datum : Thue.StandingDatum) (beta : Fin 2) :
    stableCyclic3 beta ≤ V datum := by
  rw [stableCyclic3, Subgroup.closure_le, Set.singleton_subset_iff]
  exact ⟨FreeGroup.of (Sum.inl beta), by
    simp [BorisovCStage.vLift, BorisovCStage.vBasis]⟩

/--
@isnad1 id=le.0h1v.s6.aff7fed98081 from=translated src=- shape=97e46943 vocab=e4f2b16b
-/
theorem stableCyclic3_le_J3 (beta : Fin 2) :
    stableCyclic3 beta ≤ J3 beta := by
  rw [stableCyclic3, Subgroup.closure_le, Set.singleton_subset_iff]
  apply Subgroup.subset_closure
  simp

private theorem g0Equiv_symm_mem_Uc_of_mem_U
    (datum : Thue.StandingDatum) {x : BorisovHNNModel.Gamma3}
    (hx : x ∈ U datum) : g0Equiv.symm x ∈ Uc datum := by
  rcases hx with ⟨w, rfl⟩
  rw [← g0Equiv_uLift]
  simp only [g0Equiv.symm_apply_apply]
  change FreeGroup.lift (BorisovIntersections.uBasis datum) w ∈
    Subgroup.closure (Set.range (BorisovIntersections.uBasis datum))
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨w, rfl⟩

private theorem g0Equiv_symm_mem_Vc_of_mem_V
    (datum : Thue.StandingDatum) {x : BorisovHNNModel.Gamma3}
    (hx : x ∈ V datum) : g0Equiv.symm x ∈ Vc datum := by
  rcases hx with ⟨w, rfl⟩
  rw [← g0Equiv_vLift]
  simp only [g0Equiv.symm_apply_apply]
  change FreeGroup.lift (BorisovIntersections.vBasis datum) w ∈
    Subgroup.closure (Set.range (BorisovIntersections.vBasis datum))
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨w, rfl⟩

/-- The `U_c ∩ J_beta` statement in Lemma 3.5 of the paper, transported to the
concrete semantic model `Gamma3`.
@isnad1 id=eq.0h2v.s6.ba2a2f290d88 from=translated src=- shape=28f3fb2c vocab=500520e6
-/
theorem U_inf_J3 (datum : Thue.StandingDatum) (beta : Fin 2) :
    U datum ⊓ J3 beta = stableCyclic3 beta := by
  apply le_antisymm
  · intro x hx
    have hyU := g0Equiv_symm_mem_Uc_of_mem_U datum hx.1
    have hyJ := g0Equiv_symm_mem_J_of_mem_J3 beta hx.2
    have hy :
        g0Equiv.symm x ∈ BorisovIntersections.stableCyclic beta := by
      rw [← (BorisovLemmaFourTwo.lemma4_2 datum).1 beta |>.1]
      exact ⟨hyU, hyJ⟩
    have hx' := g0Equiv_mem_stableCyclic3_of_mem_stableCyclic beta hy
    simpa only [MulEquiv.apply_symm_apply] using hx'
  · intro x hx
    exact ⟨stableCyclic3_le_U datum beta hx, stableCyclic3_le_J3 beta hx⟩

/-- The `V_c ∩ J_beta` statement in Lemma 3.5 of the paper, transported to the
concrete semantic model `Gamma3`.
@isnad1 id=eq.0h2v.s6.0a5d45d5da98 from=translated src=- shape=28f3fb2c vocab=6aa658c7
-/
theorem V_inf_J3 (datum : Thue.StandingDatum) (beta : Fin 2) :
    V datum ⊓ J3 beta = stableCyclic3 beta := by
  apply le_antisymm
  · intro x hx
    have hyV := g0Equiv_symm_mem_Vc_of_mem_V datum hx.1
    have hyJ := g0Equiv_symm_mem_J_of_mem_J3 beta hx.2
    have hy :
        g0Equiv.symm x ∈ BorisovIntersections.stableCyclic beta := by
      rw [← (BorisovLemmaFourTwo.lemma4_2 datum).1 beta |>.2]
      exact ⟨hyV, hyJ⟩
    have hx' := g0Equiv_mem_stableCyclic3_of_mem_stableCyclic beta hy
    simpa only [MulEquiv.apply_symm_apply] using hx'
  · intro x hx
    exact ⟨stableCyclic3_le_V datum beta hx, stableCyclic3_le_J3 beta hx⟩

/-- The canonical copy of `s_beta` in the source associated subgroup `U`.-/
def uStable (datum : Thue.StandingDatum) (beta : Fin 2) : U datum :=
  ⟨BorisovCStage.stable3 beta,
    ⟨FreeGroup.of (Sum.inl beta), by
      simp [BorisovCStage.uLift, BorisovCStage.uBasis]⟩⟩

/--
@isnad1 id=eq.1h2v.s9.40b1ba7cacc3 from=translated src=- shape=6d4f544c vocab=1828521d
-/
@[simp] theorem cEquiv_uStable
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (beta : Fin 2) :
    ((cEquiv datum hfree (uStable datum beta) : V datum) :
        BorisovHNNModel.Gamma3) =
      BorisovCStage.stable3 beta := by
  simpa [uStable, BorisovCStage.uBasis,
    BorisovCStage.vBasis] using
    cEquiv_on_basis datum hfree (Sum.inl beta)

/-- The associated isomorphism for the `c`-HNN stage preserves membership
in `J_beta`.  This is the compatibility hypothesis consumed by the
restricted-HNN embedding over `J_beta`.
@isnad1 id=iff.1h3v.s10.0e7682d5a575 from=translated src=- shape=315af165 vocab=1266f097
-/
theorem cEquiv_mem_J3_iff
    (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)
    (beta : Fin 2) (a : U datum) :
    (a : BorisovHNNModel.Gamma3) ∈ J3 beta ↔
      (cEquiv datum hfree a : BorisovHNNModel.Gamma3) ∈ J3 beta := by
  constructor
  · intro haJ
    have haC :
        (a : BorisovHNNModel.Gamma3) ∈ stableCyclic3 beta := by
      rw [← U_inf_J3 datum beta]
      exact ⟨a.property, haJ⟩
    rcases (Subgroup.mem_closure_singleton.mp haC) with ⟨n, hn⟩
    have ha : a = (uStable datum beta) ^ n := by
      apply Subtype.ext
      exact hn.symm
    rw [ha, map_zpow]
    change
      (cEquiv datum hfree (uStable datum beta) :
          BorisovHNNModel.Gamma3) ^ n ∈ J3 beta
    rw [cEquiv_uStable]
    apply stableCyclic3_le_J3 beta
    exact Subgroup.mem_closure_singleton.mpr ⟨n, rfl⟩
  · intro hbJ
    have hbC :
        (cEquiv datum hfree a : BorisovHNNModel.Gamma3) ∈
          stableCyclic3 beta := by
      rw [← V_inf_J3 datum beta]
      exact ⟨(cEquiv datum hfree a).property, hbJ⟩
    rcases (Subgroup.mem_closure_singleton.mp hbC) with ⟨n, hn⟩
    have ha : a = (uStable datum beta) ^ n := by
      apply (cEquiv datum hfree).injective
      apply Subtype.ext
      rw [map_zpow]
      change
        (cEquiv datum hfree a : BorisovHNNModel.Gamma3) =
          (cEquiv datum hfree (uStable datum beta) :
            BorisovHNNModel.Gamma3) ^ n
      rw [cEquiv_uStable]
      exact hn.symm
    rw [ha]
    change
      BorisovCStage.stable3 beta ^ n ∈ J3 beta
    apply stableCyclic3_le_J3 beta
    exact Subgroup.mem_closure_singleton.mpr ⟨n, rfl⟩

end

end BorisovInputsBridge
end Undecidability
