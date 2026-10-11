import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.PlaqueCharts

namespace OAI

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A X : Type*} [TopologicalSpace P] [TopologicalSpace A] [TopologicalSpace X]

lemma continuousOn_prod_iff {f : P × A → X} {U : Set P} {V : Set A} :
    ContinuousOn f (U ×ˢ V) ↔ Continuous (fun z : U × V ↦ f (z.1,z.2)) := by
  constructor
  · intro h
    exact h.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun z ↦ ⟨z.1.property,z.2.property⟩)
  · intro h
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact h.comp (Homeomorph.Set.prod U V).continuous

lemma continuousOn_prod_union {f : P × A → X} {U : Set P} {V W : Set A}
    (hV : IsClosed V) (hW : IsClosed W)
    (hfV : ContinuousOn f (U ×ˢ V)) (hfW : ContinuousOn f (U ×ˢ W)) :
    ContinuousOn f (U ×ˢ (V ∪ W)) := by
  let g : U × A → X := fun z ↦ f (z.1,z.2)
  have hgV : ContinuousOn g (univ ×ˢ V) := hfV.comp
    (continuous_subtype_val.prodMap continuous_id).continuousOn
    (fun z hz ↦ ⟨z.1.property,hz.2⟩)
  have hgW : ContinuousOn g (univ ×ˢ W) := hfW.comp
    (continuous_subtype_val.prodMap continuous_id).continuousOn
    (fun z hz ↦ ⟨z.1.property,hz.2⟩)
  have hg : ContinuousOn g (univ ×ˢ (V ∪ W)) := by
    rw [prod_union]
    exact hgV.union_of_isClosed hgW (isClosed_univ.prod hV) (isClosed_univ.prod hW)
  apply continuousOn_prod_iff.mpr
  exact hg.comp_continuous (continuous_id.prodMap continuous_subtype_val)
    (fun z ↦ ⟨trivial,z.2.property⟩)

def LocalFamilyContinuous (R : P → A → X) (p : P) (K : Set A) : Prop :=
  ∃ U : Set P, IsOpen U ∧ p ∈ U ∧ ContinuousOn (Function.uncurry R) (U ×ˢ K)

lemma LocalFamilyContinuous.mono {R : P → A → X} {p : P} {K L : Set A}
    (h : LocalFamilyContinuous R p K) (hLK : L ⊆ K) : LocalFamilyContinuous R p L := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact ⟨U,hU,hp,hR.mono (prod_mono_right hLK)⟩

lemma LocalFamilyContinuous.union {R : P → A → X} {p : P} {K L : Set A}
    (hK : IsClosed K) (hL : IsClosed L)
    (hR : LocalFamilyContinuous R p K) (hS : LocalFamilyContinuous R p L) :
    LocalFamilyContinuous R p (K ∪ L) := by
  obtain ⟨U,hU,hp,hRu⟩ := hR
  obtain ⟨V,hV,hpv,hRv⟩ := hS
  exact ⟨U ∩ V,hU.inter hV,⟨hp,hpv⟩,continuousOn_prod_union hK hL
    (hRu.mono (prod_mono_left inter_subset_left))
    (hRv.mono (prod_mono_left inter_subset_right))⟩

lemma LocalFamilyContinuous.of_continuous {R : P → A → X} {p : P} {K : Set A}
    (h : Continuous (Function.uncurry R)) : LocalFamilyContinuous R p K :=
  ⟨univ,isOpen_univ,trivial,h.continuousOn⟩

lemma LocalFamilyContinuous.subtype_parameter {R : P → A → X} {p : P} {K : Set A}
    {U : Set P} (hU : IsOpen U) (hp : p ∈ U)
    (h : LocalFamilyContinuous (fun q : U ↦ R q) ⟨p,hp⟩ K) :
    LocalFamilyContinuous R p K := by
  obtain ⟨W,hW,hpW,hRW⟩ := h
  obtain ⟨V,hV,hVe⟩ := isOpen_induced_iff.mp hW
  have hpV : p ∈ V := by change (⟨p,hp⟩ : U) ∈ Subtype.val ⁻¹' V; rwa [hVe]
  refine ⟨U ∩ V,hU.inter hV,⟨hp,hpV⟩,continuousOn_prod_iff.mpr ?_⟩
  have hc := continuousOn_prod_iff.mp hRW
  let k : ↥(U ∩ V) → W := fun q ↦ ⟨⟨q.val,q.property.1⟩,by rw [← hVe]; exact q.property.2⟩
  have hk : Continuous k := (continuous_subtype_val.subtype_mk _).subtype_mk _
  exact hc.comp (hk.prodMap continuous_id)

lemma LocalFamilyContinuous.precomp {B : Type*} [TopologicalSpace B]
    {R : P → A → X} {p : P} {K : Set A} {L : Set B}
    (h : LocalFamilyContinuous R p K) {f : B → A} (hf : Continuous f)
    (hmap : MapsTo f L K) : LocalFamilyContinuous (fun p b ↦ R p (f b)) p L := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact ⟨U,hU,hp,hR.comp (continuous_id.prodMap hf).continuousOn
    (fun z hz ↦ ⟨hz.1,hmap hz.2⟩)⟩

lemma LocalFamilyContinuous.of_restrict {R : P → A → X} {p : P} {K : Set A}
    (h : LocalFamilyContinuous (fun q (a : K) ↦ R q a) p univ) :
    LocalFamilyContinuous R p K := by
  obtain ⟨U,hU,hp,hR⟩ := h
  refine ⟨U,hU,hp,continuousOn_prod_iff.mpr ?_⟩
  exact hR.comp_continuous (continuous_subtype_val.prodMap continuous_id)
    (fun z ↦ ⟨z.1.property,trivial⟩)

lemma LocalFamilyContinuous.continuousAt {R : P → A → X} {p : P}
    (h : LocalFamilyContinuous R p univ) (a : A) :
    ContinuousAt (Function.uncurry R) (p,a) := by
  obtain ⟨U,hU,hp,hR⟩ := h
  exact hR.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hp,trivial⟩)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
namespace ProductBoxTopology
variable {P A B X C D : Type*} [TopologicalSpace P] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace C] [TopologicalSpace D]

lemma ProductChart.parameter_tile_local [T2Space X] [CompactSpace A] [CompactSpace B]
    [PathConnectedSpace A] [PathConnectedSpace B]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source) (e : ProductChart atlas)
    {R : P → A × B → X} (hR : ∀ p, IsBox atlas (R p)) (p₀ : P) (a₀ : A) (b₀ : B)
    (hbottom : LocalFamilyContinuous (fun p a ↦ R p (a,b₀)) p₀ univ)
    (hleft : LocalFamilyContinuous (fun p b ↦ R p (a₀,b)) p₀ univ)
    (he : ∀ w, R p₀ w ∈ e.chart.source) : LocalFamilyContinuous R p₀ univ := by
  obtain ⟨U,hU,hpU,hbU⟩ := hbottom
  obtain ⟨V,hV,hpV,hlV⟩ := hleft
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : p₀ ∈ W := ⟨hpU,hpV⟩
  have hb : Continuous (fun z : W × A ↦ R z.1 (z.2,b₀)) :=
    hbU.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun z ↦ ⟨z.1.property.1,trivial⟩)
  have hl : Continuous (fun z : W × B ↦ R z.1 (a₀,z.2)) :=
    hlV.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      (fun z ↦ ⟨z.1.property.2,trivial⟩)
  obtain ⟨T,hT,hpT,hRT⟩ := e.parameter_tile hcover (R := fun p : W ↦ R p)
    (fun p ↦ hR p) ⟨p₀,hpW⟩ a₀ b₀ hb hl he
  apply LocalFamilyContinuous.subtype_parameter hW hpW
  refine ⟨T,hT,hpT,continuousOn_prod_iff.mpr ?_⟩
  exact hRT.comp (continuous_id.prodMap continuous_subtype_val)

lemma LocalFamilyContinuous.prod_of_restrict {R : P → A × B → X} {p : P}
    {U : Set A} {V : Set B}
    (h : LocalFamilyContinuous (fun q (w : U × V) ↦ R q (w.1,w.2)) p univ) :
    LocalFamilyContinuous R p (U ×ˢ V) := by
  apply LocalFamilyContinuous.of_restrict
  exact h.precomp (Homeomorph.Set.prod U V).continuous (mapsTo_univ _ _)

end ProductBoxTopology
end
end

section

noncomputable section
open Set Filter Topology
open scoped unitInterval
namespace ProductBoxTopology
variable {P X C D : Type*} [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace C] [TopologicalSpace D]

theorem continuous_family [T2Space X]
    {atlas : Set (OpenPartialHomeomorph X (C × D))}
    (hcharts : ∀ x : X, ∃ e : ProductChart atlas, x ∈ e.chart.source)
    {R : P → I × I → X} (hR : ∀ p, IsBox atlas (R p))
    (hbottom : Continuous (fun z : P × I ↦ R z.1 (z.2,0)))
    (hleft : Continuous (fun z : P × I ↦ R z.1 (0,z.2))) :
    Continuous (Function.uncurry R) := by
  classical
  have hcover : ∀ x : X, ∃ e ∈ atlas, x ∈ e.source := by
    intro x
    obtain ⟨e,he⟩ := hcharts x
    exact ⟨e.chart,e.mem_atlas,he⟩
  have hbLocal (p : P) : LocalFamilyContinuous R p (univ ×ˢ {0}) := by
    refine ⟨univ,isOpen_univ,trivial,?_⟩
    have hc : Continuous (fun z : P × (I × I) ↦ R z.1 (z.2.1,0)) :=
      hbottom.comp (continuous_fst.prodMk continuous_snd.fst)
    apply hc.continuousOn.congr
    rintro ⟨q,a,b⟩ h
    have hb : b=0 := h.2.2
    subst b
    rfl
  have hlLocal (p : P) : LocalFamilyContinuous R p ({0} ×ˢ univ) := by
    refine ⟨univ,isOpen_univ,trivial,?_⟩
    have hc : Continuous (fun z : P × (I × I) ↦ R z.1 (0,z.2.2)) :=
      hleft.comp (continuous_fst.prodMk continuous_snd.snd)
    apply hc.continuousOn.congr
    rintro ⟨q,a,b⟩ h
    have ha : a=0 := h.2.1
    subst a
    rfl
  have hlocal (p₀ : P) : LocalFamilyContinuous R p₀ univ := by
    let c : ProductChart atlas → Set (I × I) := fun e ↦ R p₀ ⁻¹' e.chart.source
    have hc : ∀ e, IsOpen (c e) := fun e ↦ e.chart.open_source.preimage (hR p₀).1
    have hcU : univ ⊆ ⋃ e, c e := by
      intro w _
      obtain ⟨e,he⟩ := hcharts (R p₀ w)
      exact mem_iUnion.mpr ⟨e,he⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,ht⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc hcU
    have hprefix : ∀ i j, LocalFamilyContinuous R p₀ (Icc 0 (t i) ×ˢ Icc 0 (t j)) := by
      intro i
      induction i with
      | zero =>
        intro j
        apply (hlLocal p₀).mono
        intro w hw
        exact ⟨le_antisymm (ht0 ▸ hw.1.2) hw.1.1,trivial⟩
      | succ i hi =>
        intro j
        induction j with
        | zero =>
          apply (hbLocal p₀).mono
          intro w hw
          exact ⟨trivial,le_antisymm (ht0 ▸ hw.2.2) hw.2.1⟩
        | succ j hj =>
          have hti : t i ≤ t (i+1) := htmono (Nat.le_succ i)
          have htj : t j ≤ t (j+1) := htmono (Nat.le_succ j)
          let A := Icc (t i) (t (i+1))
          let B := Icc (t j) (t (j+1))
          let : PathConnectedSpace A := pathConnected_Icc_unit hti
          let : PathConnectedSpace B := pathConnected_Icc_unit htj
          let a₀ : A := ⟨t i,le_rfl,hti⟩
          let b₀ : B := ⟨t j,le_rfl,htj⟩
          obtain ⟨e,he⟩ := ht i j
          have htile : LocalFamilyContinuous R p₀ (A ×ˢ B) := by
            apply LocalFamilyContinuous.prod_of_restrict
            apply e.parameter_tile_local hcover
              (fun p ↦ (hR p).precomp continuous_subtype_val continuous_subtype_val) p₀ a₀ b₀
            · exact hj.precomp (continuous_subtype_val.prodMk continuous_const)
                (fun a _ ↦ ⟨⟨bot_le,a.property.2⟩,⟨bot_le,le_rfl⟩⟩)
            · exact (hi (j+1)).precomp (continuous_const.prodMk continuous_subtype_val)
                (fun b _ ↦ ⟨⟨bot_le,le_rfl⟩,⟨bot_le,b.property.2⟩⟩)
            · intro w
              exact he ⟨w.1.property,w.2.property⟩
          have hcl : IsClosed (Icc (0:I) (t i) ×ˢ Icc (0:I) (t (j+1))) := isClosed_Icc.prod isClosed_Icc
          have hcb : IsClosed (Icc (0:I) (t (i+1)) ×ˢ Icc (0:I) (t j)) := isClosed_Icc.prod isClosed_Icc
          have hct : IsClosed (A ×ˢ B) := isClosed_Icc.prod isClosed_Icc
          apply (((hi (j+1)).union hcl hcb hj).union (hcl.union hcb) hct htile).mono
          intro w hw
          by_cases hx : w.1 ≤ t i
          · exact Or.inl (Or.inl ⟨⟨hw.1.1,hx⟩,hw.2⟩)
          by_cases hy : w.2 ≤ t j
          · exact Or.inl (Or.inr ⟨hw.1,⟨hw.2.1,hy⟩⟩)
          exact Or.inr ⟨⟨(not_le.mp hx).le,hw.1.2⟩,⟨(not_le.mp hy).le,hw.2.2⟩⟩
    apply (hprefix N N).mono
    intro w _
    rw [hN N le_rfl]
    exact ⟨⟨bot_le,le_top⟩,⟨bot_le,le_top⟩⟩
  exact continuous_iff_continuousAt.mpr fun z ↦ (hlocal z.1).continuousAt z.2

end ProductBoxTopology
end
end

section

noncomputable section
open Set Metric Filter Topology
open scoped Manifold unitInterval
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

end UniversalCoverSplitting
end
end

end OAI
