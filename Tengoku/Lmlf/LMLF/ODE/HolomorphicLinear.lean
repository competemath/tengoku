import Tengoku.Lmlf.LMLF.ODE.HolomorphicLinear.Local
import Tengoku.Seed.Analysis.Analytic.Uniqueness
import Tengoku.Seed.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Tengoku.Seed.Topology.Homotopy.Lifting
import Tengoku.Seed.Topology.Sheaves.EtaleSpace
import Tengoku.Seed.Topology.Sheaves.LocalPredicate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic linear ordinary differential equations

Existence and uniqueness for a homogeneous linear equation on a simply connected complex domain.
The solution sheaf and its étale-space continuation are implementation details.
-/

namespace LMLF.ODE

open CategoryTheory Filter Metric Set TopologicalSpace Topology
open scoped Topology

universe u

private abbrev LiftedDomain (Z : Set ℂ) := ULift.{u} Z

private def domainCoord {Z : Set ℂ} : LiftedDomain.{u} Z → ℂ :=
  fun x ↦ x.down.1

private theorem domainCoord_isOpenEmbedding {Z : Set ℂ} (hZ : IsOpen Z) :
    IsOpenEmbedding (domainCoord (Z := Z)) :=
  hZ.isOpenEmbedding_subtypeVal.comp Homeomorph.ulift.isOpenEmbedding

private theorem domainCoord_injective {Z : Set ℂ} (hZ : IsOpen Z) :
    Function.Injective (domainCoord (Z := Z)) :=
  (domainCoord_isOpenEmbedding hZ).injective

private theorem isOpen_domainCoord_image {Z : Set ℂ} (hZ : IsOpen Z)
    (U : Opens (LiftedDomain.{u} Z)) :
    IsOpen (domainCoord (Z := Z) '' (U : Set (LiftedDomain.{u} Z))) :=
  (domainCoord_isOpenEmbedding hZ).isOpenMap U U.isOpen

private theorem mem_open_of_mem_domainCoord_image {Z : Set ℂ} (hZ : IsOpen Z)
    (U : Opens (LiftedDomain.{u} Z)) (x : LiftedDomain.{u} Z)
    (hx : domainCoord x ∈ domainCoord '' (U : Set (LiftedDomain.{u} Z))) : x ∈ U := by
  rcases hx with ⟨y, hyU, hy⟩
  exact (domainCoord_injective hZ hy) ▸ hyU

private noncomputable def ambientize {E : Type u} {Z : Set ℂ} (_hZ : IsOpen Z)
    {U : Opens (LiftedDomain.{u} Z)} (s : U → E) [Zero E] : ℂ → E := by
  classical
  exact fun z ↦ if hz : ∃ x : U, domainCoord (x : LiftedDomain.{u} Z) = z then
    s (Classical.choose hz) else 0

private theorem ambientize_domainCoord {Z : Set ℂ} (hZ : IsOpen Z)
    {U : Opens (LiftedDomain.{u} Z)} (s : U → E) [Zero E] (x : U) :
    ambientize hZ s (domainCoord (x : LiftedDomain.{u} Z)) = s x := by
  classical
  unfold ambientize
  split
  · rename_i hx
    congr 1
    apply Subtype.ext
    apply domainCoord_injective hZ
    exact Classical.choose_spec hx
  · rename_i hx
    exact (hx ⟨x, rfl⟩).elim

private def IsHolomorphicLinearSolution
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Z : Set ℂ} (_hZ : IsOpen Z) (A : ℂ → (E →L[ℂ] E))
    {U : Opens (LiftedDomain.{u} Z)} (s : U → E) : Prop :=
  ∃ a : ℂ → E,
    (∀ x : U, a (domainCoord (x : LiftedDomain.{u} Z)) = s x) ∧
      AnalyticOnNhd ℂ a (domainCoord '' (U : Set (LiftedDomain.{u} Z))) ∧
      ∀ z ∈ domainCoord '' (U : Set (LiftedDomain.{u} Z)),
        HasDerivAt a (A z (a z)) z

private def holomorphicLinearPrelocal
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Z : Set ℂ} (hZ : IsOpen Z) (A : ℂ → (E →L[ℂ] E)) :
    TopCat.PrelocalPredicate (fun _ : TopCat.of (LiftedDomain.{u} Z) ↦ E) where
  pred := IsHolomorphicLinearSolution hZ A
  res := by
    intro U V i s hs
    rcases hs with ⟨a, ha, hana, hode⟩
    refine ⟨a, ?_, hana.mono ?_, ?_⟩
    · intro x
      change a (domainCoord (x : LiftedDomain.{u} Z)) = s ⟨x, i.le x.2⟩
      exact ha ⟨x, i.le x.2⟩
    · rintro z ⟨x, hxU, rfl⟩
      exact ⟨x, i.le hxU, rfl⟩
    · intro z hz
      rcases hz with ⟨x, hxU, rfl⟩
      exact hode _ ⟨x, i.le hxU, rfl⟩

private theorem ambientize_eventuallyEq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Z : Set ℂ} (hZ : IsOpen Z)
    {U V : Opens (LiftedDomain.{u} Z)} (i : V ⟶ U) (s : U → E)
    {b : ℂ → E}
    (hb : ∀ x : V, b (domainCoord (x : LiftedDomain.{u} Z)) = s (Opens.inclusion i.le x))
    (x : V) :
    ambientize hZ s =ᶠ[nhds (domainCoord (x : LiftedDomain.{u} Z))] b := by
  apply Filter.eventually_of_mem
    ((isOpen_domainCoord_image hZ V).mem_nhds ⟨x.1, x.2, rfl⟩)
  rintro z ⟨y, hyV, rfl⟩
  let yV : V := ⟨y, hyV⟩
  rw [ambientize_domainCoord hZ s (Opens.inclusion i.le yV), ← hb yV]

private def holomorphicLinearLocalPredicate
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Z : Set ℂ} (hZ : IsOpen Z) (A : ℂ → (E →L[ℂ] E)) :
    TopCat.LocalPredicate (fun _ : TopCat.of (LiftedDomain.{u} Z) ↦ E) where
  __ := holomorphicLinearPrelocal hZ A
  locality := by
    intro U s hs
    let a := ambientize hZ s
    refine ⟨a, ambientize_domainCoord hZ s, ?_, ?_⟩
    · intro z hz
      rcases hz with ⟨x, hxU, rfl⟩
      rcases hs ⟨x, hxU⟩ with ⟨V, hxV, i, hV⟩
      change IsHolomorphicLinearSolution hZ A
        (fun y : V ↦ s (Opens.inclusion i.le y)) at hV
      rcases hV with ⟨b, hb, hbana, hbode⟩
      have heq := ambientize_eventuallyEq hZ i s hb ⟨x, hxV⟩
      exact (hbana (domainCoord x) ⟨x, hxV, rfl⟩).congr heq.symm
    · intro z hz
      rcases hz with ⟨x, hxU, rfl⟩
      rcases hs ⟨x, hxU⟩ with ⟨V, hxV, i, hV⟩
      change IsHolomorphicLinearSolution hZ A
        (fun y : V ↦ s (Opens.inclusion i.le y)) at hV
      rcases hV with ⟨b, hb, hbana, hbode⟩
      have heq := ambientize_eventuallyEq hZ i s hb ⟨x, hxV⟩
      have hder := (hbode (domainCoord x) ⟨x, hxV, rfl⟩).congr_of_eventuallyEq heq
      change HasDerivAt (ambientize hZ s)
        (A (domainCoord x) (ambientize hZ s (domainCoord x))) (domainCoord x)
      simpa only [heq.eq_of_nhds] using hder

private theorem stalkToFiber_injective_holomorphicLinear
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Z : Set ℂ} (hZ : IsOpen Z) {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A Z) (x : LiftedDomain.{u} Z) :
    Function.Injective
      (TopCat.stalkToFiber (holomorphicLinearLocalPredicate hZ A) x) := by
  let P := holomorphicLinearLocalPredicate hZ A
  apply TopCat.stalkToFiber_injective P x
  intro U V fU hfU fV hfV hvalue
  change IsHolomorphicLinearSolution hZ A fU at hfU
  change IsHolomorphicLinearSolution hZ A fV at hfV
  rcases hfU with ⟨a, ha, haAnalytic, haOde⟩
  rcases hfV with ⟨b, hb, hbAnalytic, hbOde⟩
  let q := domainCoord x
  have habq : a q = b q := by
    calc
      a q = fU ⟨x, U.2⟩ := ha ⟨x, U.2⟩
      _ = fV ⟨x, V.2⟩ := hvalue
      _ = b q := (hb ⟨x, V.2⟩).symm
  have hopen : IsOpen
      (domainCoord '' (U.1 : Set (LiftedDomain.{u} Z)) ∩
        domainCoord '' (V.1 : Set (LiftedDomain.{u} Z))) :=
    (isOpen_domainCoord_image hZ U.1).inter (isOpen_domainCoord_image hZ V.1)
  have hq : q ∈
      domainCoord '' (U.1 : Set (LiftedDomain.{u} Z)) ∩
        domainCoord '' (V.1 : Set (LiftedDomain.{u} Z)) :=
    ⟨⟨x, U.2, rfl⟩, ⟨x, V.2, rfl⟩⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen q hq
  have hballZ : ball q r ⊆ Z := by
    intro z hz
    rcases (hrsub hz).1 with ⟨y, -, rfl⟩
    exact y.down.2
  obtain ⟨s, hs0, hsAnalytic, hsOde, hsUnique⟩ :=
    exists_unique_holomorphicLinearIVP_ball hr (hA.mono hballZ)
      (mem_ball_self hr) (a q)
  have hsa : EqOn s a (ball q r) :=
    hsUnique a rfl (haAnalytic.mono fun _ hz ↦ (hrsub hz).1)
      (fun z hz ↦ haOde z (hrsub hz).1)
  have hsb : EqOn s b (ball q r) :=
    hsUnique b habq.symm (hbAnalytic.mono fun _ hz ↦ (hrsub hz).2)
      (fun z hz ↦ hbOde z (hrsub hz).2)
  have hab : EqOn a b (ball q r) := fun z hz ↦ (hsa hz).symm.trans (hsb hz)
  let W₀ : Opens (LiftedDomain.{u} Z) :=
    ⟨domainCoord ⁻¹' ball q r, isOpen_ball.preimage (domainCoord_isOpenEmbedding hZ).continuous⟩
  have hxW₀ : x ∈ W₀ := mem_ball_self hr
  let W : TopologicalSpace.OpenNhds (X := TopCat.of (LiftedDomain.{u} Z)) x :=
    ⟨W₀, hxW₀⟩
  have hWU : W ≤ U := by
    intro y hy
    exact mem_open_of_mem_domainCoord_image hZ U.1 y ((hrsub hy).1)
  have hWV : W ≤ V := by
    intro y hy
    exact mem_open_of_mem_domainCoord_image hZ V.1 y ((hrsub hy).2)
  let iU : W ⟶ U := homOfLE hWU
  let iV : W ⟶ V := homOfLE hWV
  refine ⟨W, iU, iV, ?_⟩
  intro y
  have hyball : domainCoord (y : LiftedDomain.{u} Z) ∈ ball q r := y.2
  calc
    fU (iU y : U.1) = a (domainCoord (y : LiftedDomain.{u} Z)) :=
      (ha (iU y : U.1)).symm
    _ = b (domainCoord (y : LiftedDomain.{u} Z)) := hab hyball
    _ = fV (iV y : V.1) := hb (iV y : V.1)

private theorem isCoveringMap_holomorphicLinear
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Z : Set ℂ} (hZ : IsOpen Z) {A : ℂ → (E →L[ℂ] E)}
    (hA : AnalyticOnNhd ℂ A Z) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base
      (F := (TopCat.subsheafToTypes (holomorphicLinearLocalPredicate hZ A)).presheaf)) := by
  let P := holomorphicLinearLocalPredicate hZ A
  let F := (TopCat.subsheafToTypes P).presheaf
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.mp hZ (domainCoord x) x.down.2
  let B : Opens (LiftedDomain.{u} Z) :=
    ⟨domainCoord ⁻¹' ball (domainCoord x) r,
      isOpen_ball.preimage (domainCoord_isOpenEmbedding hZ).continuous⟩
  have hxB : x ∈ B := mem_ball_self hr
  have himageB : domainCoord '' (B : Set (LiftedDomain.{u} Z)) = ball (domainCoord x) r := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hyB, rfl⟩
      exact hyB
    · intro z hz
      have hzZ : z ∈ Z := hrZ hz
      let y : LiftedDomain.{u} Z := ULift.up ⟨z, hzZ⟩
      exact ⟨y, hz, rfl⟩
  refine ⟨B, hxB, ?_⟩
  intro y hyB
  let ev : F.obj (Opposite.op B) → E := fun s ↦ s.1 ⟨y, hyB⟩
  have hev_surjective : Function.Surjective ev := by
    intro e
    obtain ⟨u, hu0, huAnalytic, huOde, -⟩ :=
      exists_unique_holomorphicLinearIVP_ball hr (hA.mono hrZ) hyB e
    let s : B → E := fun z ↦ u (domainCoord (z : LiftedDomain.{u} Z))
    have hs : IsHolomorphicLinearSolution hZ A s := by
      refine ⟨u, fun _ ↦ rfl, ?_, ?_⟩
      · simpa only [himageB] using huAnalytic
      · simpa only [himageB] using huOde
    refine ⟨⟨s, hs⟩, ?_⟩
    exact hu0
  have hev_injective : Function.Injective ev := by
    intro f g hfg
    apply Subtype.ext
    funext z
    have hf : IsHolomorphicLinearSolution hZ A f.1 := f.2
    have hg : IsHolomorphicLinearSolution hZ A g.1 := g.2
    rcases hf with ⟨a, ha, haAnalytic, haOde⟩
    rcases hg with ⟨b, hb, hbAnalytic, hbOde⟩
    have haby : a (domainCoord y) = b (domainCoord y) := by
      calc
        a (domainCoord y) = f.1 ⟨y, hyB⟩ := ha ⟨y, hyB⟩
        _ = g.1 ⟨y, hyB⟩ := hfg
        _ = b (domainCoord y) := (hb ⟨y, hyB⟩).symm
    obtain ⟨s, hs0, hsAnalytic, hsOde, hsUnique⟩ :=
      exists_unique_holomorphicLinearIVP_ball hr (hA.mono hrZ) hyB
        (a (domainCoord y))
    have hsa : EqOn s a (ball (domainCoord x) r) := by
      apply hsUnique a rfl
      · simpa only [himageB] using haAnalytic
      · simpa only [himageB] using haOde
    have hsb : EqOn s b (ball (domainCoord x) r) := by
      apply hsUnique b haby.symm
      · simpa only [himageB] using hbAnalytic
      · simpa only [himageB] using hbOde
    calc
      f.1 z = a (domainCoord (z : LiftedDomain.{u} Z)) := (ha z).symm
      _ = b (domainCoord (z : LiftedDomain.{u} Z)) :=
        (hsa z.2).symm.trans (hsb z.2)
      _ = g.1 z := hb z
  have hev_bijective : Function.Bijective ev := ⟨hev_injective, hev_surjective⟩
  have hstalk_injective := stalkToFiber_injective_holomorphicLinear hZ hA y
  constructor
  · intro f g hfg
    apply hev_injective
    change f.1 ⟨y, hyB⟩ = g.1 ⟨y, hyB⟩
    calc
      f.1 ⟨y, hyB⟩ = TopCat.stalkToFiber P y (F.germ B y hyB f) :=
        (TopCat.stalkToFiber_germ P B y hyB f).symm
      _ = TopCat.stalkToFiber P y (F.germ B y hyB g) := congrArg _ hfg
      _ = g.1 ⟨y, hyB⟩ := TopCat.stalkToFiber_germ P B y hyB g
  · intro germ
    obtain ⟨s, hs⟩ := hev_surjective (TopCat.stalkToFiber P y germ)
    refine ⟨s, hstalk_injective ?_⟩
    calc
      TopCat.stalkToFiber P y (F.germ B y hyB s) = s.1 ⟨y, hyB⟩ :=
        TopCat.stalkToFiber_germ P B y hyB s
      _ = ev s := rfl
      _ = TopCat.stalkToFiber P y germ := hs

/-- A holomorphic homogeneous linear initial-value problem on a simply connected complex domain
has a unique solution on that domain.
@isnad1 id=ex.4h5v.s9.66b876ad51dc from=translated src=- shape=c793f76e vocab=57db2bb5
-/
theorem exists_unique_holomorphicLinearIVP
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Z : Set ℂ} (hZ : IsOpen Z) (hZc : IsSimplyConnected Z)
    {A : ℂ → (E →L[ℂ] E)} (hA : AnalyticOnNhd ℂ A Z)
    {x₀ : ℂ} (hx₀ : x₀ ∈ Z) (u₀ : E) :
    ∃ u : ℂ → E, u x₀ = u₀ ∧ AnalyticOnNhd ℂ u Z ∧
      (∀ z ∈ Z, HasDerivAt u (A z (u z)) z) ∧
      ∀ v : ℂ → E, v x₀ = u₀ → AnalyticOnNhd ℂ v Z →
        (∀ z ∈ Z, HasDerivAt v (A z (v z)) z) → Set.EqOn u v Z := by
  classical
  let P := holomorphicLinearLocalPredicate hZ A
  let F := (TopCat.subsheafToTypes P).presheaf
  let X := LiftedDomain Z
  let x₀X : X := ULift.up ⟨x₀, hx₀⟩
  have hcov : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F)) :=
    isCoveringMap_holomorphicLinear hZ hA
  obtain ⟨r₀, hr₀, hr₀Z⟩ := Metric.isOpen_iff.mp hZ x₀ hx₀
  let B₀ : Opens X :=
    ⟨domainCoord ⁻¹' ball x₀ r₀,
      isOpen_ball.preimage (domainCoord_isOpenEmbedding hZ).continuous⟩
  have hx₀B₀ : x₀X ∈ B₀ := mem_ball_self hr₀
  have himageB₀ : domainCoord '' (B₀ : Set X) = ball x₀ r₀ := by
    apply Set.Subset.antisymm
    · rintro z ⟨y, hy, rfl⟩
      exact hy
    · intro z hz
      let y : X := ULift.up ⟨z, hr₀Z hz⟩
      exact ⟨y, hz, rfl⟩
  obtain ⟨u₀loc, hu₀loc, hu₀locAnalytic, hu₀locOde, -⟩ :=
    exists_unique_holomorphicLinearIVP_ball hr₀ (hA.mono hr₀Z)
      (mem_ball_self hr₀) u₀
  let s₀ : B₀ → E := fun z ↦ u₀loc (domainCoord (z : X))
  have hs₀ : IsHolomorphicLinearSolution hZ A s₀ := by
    refine ⟨u₀loc, fun _ ↦ rfl, ?_, ?_⟩
    · simpa only [himageB₀] using hu₀locAnalytic
    · simpa only [himageB₀] using hu₀locOde
  let s₀F : F.obj (Opposite.op B₀) := ⟨s₀, hs₀⟩
  let e₀ : F.EtaleSpace :=
    ⟨x₀X, F.germ B₀ x₀X hx₀B₀ s₀F⟩
  let _ : SimplyConnectedSpace Z := hZc.simplyConnectedSpace
  let _ : SimplyConnectedSpace X :=
    Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace
  let _ : LocallyPathConnectedSpace Z := hZ.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace X :=
    Homeomorph.ulift.isOpenEmbedding.locallyPathConnectedSpace
  obtain ⟨L, hL, -⟩ := hcov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀X e₀ rfl
  have hLbase : ∀ x : X, (L x).base = x := by
    intro x
    exact congrFun hL.2 x
  let germValue : F.EtaleSpace → E := fun t ↦ TopCat.stalkToFiber P t.base t.germ
  let uX : X → E := fun x ↦ germValue (L x)
  let u : ℂ → E := fun z ↦ if hz : z ∈ Z then uX (ULift.up ⟨z, hz⟩) else 0
  have hu_local (z : ℂ) (hz : z ∈ Z) :
      ∃ a : ℂ → E, u =ᶠ[nhds z] a ∧ AnalyticAt ℂ a z ∧
        HasDerivAt a (A z (a z)) z := by
    let x : X := ULift.up ⟨z, hz⟩
    have hLtendsto : Tendsto L (nhds x) (nhds (L x)) := L.continuous.continuousAt
    obtain ⟨U, hLxU, s, hsEventual⟩ :=
      TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto hLtendsto
    have hsPred : IsHolomorphicLinearSolution hZ A s.1 := s.2
    rcases hsPred with ⟨a, ha, haAnalytic, haOde⟩
    obtain ⟨W, hWsub, hWopen, hxW⟩ := _root_.mem_nhds_iff.mp hsEventual
    have himageWopen : IsOpen (domainCoord '' W) :=
      (domainCoord_isOpenEmbedding hZ).isOpenMap W hWopen
    have hzimageW : z ∈ domainCoord '' W := ⟨x, hxW, rfl⟩
    have hueq : u =ᶠ[nhds z] a := by
      apply Filter.eventually_of_mem (himageWopen.mem_nhds hzimageW)
      rintro z' ⟨y, hyW, rfl⟩
      rcases hWsub hyW with ⟨hyLU, hygerm⟩
      have hybase : (L y).base = y := hLbase y
      have hyU : y ∈ U := hybase ▸ hyLU
      have hvalue : uX y = s.1 ⟨y, hyU⟩ := by
        change TopCat.stalkToFiber P (L y).base (L y).germ = s.1 ⟨y, hyU⟩
        rw [hygerm, TopCat.stalkToFiber_germ]
        exact congrArg s.1 (Subtype.ext hybase)
      calc
        u (domainCoord y) = uX y := by
          have hyZ : domainCoord y ∈ Z := y.down.2
          rw [show u (domainCoord y) = if hy : domainCoord y ∈ Z then
            uX (ULift.up ⟨domainCoord y, hy⟩) else 0 by rfl, dite_eq_left hyZ]
          apply congrArg uX
          apply ULift.ext
          apply Subtype.ext
          rfl
        _ = s.1 ⟨y, hyU⟩ := hvalue
        _ = a (domainCoord y) := (ha ⟨y, hyU⟩).symm
    have hxU : x ∈ U := (hLbase x) ▸ hLxU
    have hzimageU : z ∈ domainCoord '' (U : Set X) := ⟨x, hxU, rfl⟩
    exact ⟨a, hueq, haAnalytic z hzimageU, haOde z hzimageU⟩
  have huAnalytic : AnalyticOnNhd ℂ u Z := by
    intro z hz
    obtain ⟨a, hua, haAnalytic, -⟩ := hu_local z hz
    exact haAnalytic.congr hua.symm
  have huOde : ∀ z ∈ Z, HasDerivAt u (A z (u z)) z := by
    intro z hz
    obtain ⟨a, hua, -, haOde⟩ := hu_local z hz
    have hder := haOde.congr_of_eventuallyEq hua
    simpa only [hua.eq_of_nhds] using hder
  have hu₀ : u x₀ = u₀ := by
    have hstalk := TopCat.stalkToFiber_germ P B₀ x₀X hx₀B₀ s₀F
    calc
      u x₀ = uX x₀X := by
        rw [show u x₀ = if hx : x₀ ∈ Z then uX (ULift.up ⟨x₀, hx⟩) else 0 by rfl,
          dite_eq_left hx₀]
      _ = germValue e₀ := by
        change germValue (L x₀X) = germValue e₀
        rw [hL.1]
      _ = s₀F.1 ⟨x₀X, hx₀B₀⟩ := hstalk
      _ = u₀ := hu₀loc
  refine ⟨u, hu₀, huAnalytic, huOde, ?_⟩
  intro v hv₀ hvAnalytic hvOde
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.mp hZ x₀ hx₀
  obtain ⟨s, hs0, hsAnalytic, hsOde, hsUnique⟩ :=
    exists_unique_holomorphicLinearIVP_ball hr (hA.mono hrZ)
      (mem_ball_self hr) u₀
  have hsu : EqOn s u (ball x₀ r) :=
    hsUnique u hu₀ (huAnalytic.mono hrZ) (fun z hz ↦ huOde z (hrZ hz))
  have hsv : EqOn s v (ball x₀ r) :=
    hsUnique v hv₀ (hvAnalytic.mono hrZ) (fun z hz ↦ hvOde z (hrZ hz))
  have huv : u =ᶠ[nhds x₀] v := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (hsu hz).symm.trans (hsv hz)
  exact huAnalytic.eqOn_of_preconnected_of_eventuallyEq hvAnalytic
    hZc.isPathConnected.isConnected.isPreconnected hx₀ huv

end LMLF.ODE
