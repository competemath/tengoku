import Tengoku.HodgeStructuresLean4.HodgePilot.SingularGamma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative Lemma W: `Γ`-surjectivity over an open with paracompact subspace topology

This file relativizes the `Γ`-surjectivity lemma of `HodgePilot.SingularGamma`
("Lemma W") from global sections to sections over an arbitrary open `W` of the
ambient space `X`, under the hypothesis that the subspace topology of `W` is
paracompact (the ambient `X` is only asked to be Hausdorff).  Every tool is the
one shipped by `HodgePilot.SingularGamma`; the four new pieces are exactly the
transport layer:

1. **relative local lifts** (`exists_local_lift_rel`): local lifts, inside `W`,
   of a section of the target sheaf over `W`, from local surjectivity of sheaf
   epimorphisms;
2. **relative subordinate partition** (`exists_subordinate_partition_rel`): the
   shipped `exists_subordinate_partition` instantiated at the subspace
   `TopCat.of ↥W` and transported along the open inclusion — the partition
   subsets live in `W`, the closure data is the ambient closure intersected
   with `W` (closure in `W` = ambient closure ∩ `W`, by the embedding), and
   local finiteness of the supports is recorded pointwise at points of `W`;
3. **relative cover packs** (`exists_pack_rel`): the shipped `exists_pack`
   re-proved from pointwise-at-the-open local finiteness only (the shipped
   proof already used nothing more);
4. **relative correction family** (`exists_correction_rel`): the shipped
   correction assembly with supports `closure (A j) ∩ W` — an open inside `W`
   disjoint from `closure (A j) ∩ W` is disjoint from `closure (A j)`, so the
   shipped support and extension-by-zero receipts fire unchanged.

The headline is **`gammaSurjective_rel`**: for an open `W` of a Hausdorff
space `X` such that `↥W` is paracompact, every short exact sequence of abelian
sheaves on `X` whose kernel is a sheafified cochain sheaf has surjective
induced map on sections over `W`.  The proof is Steps A–E of the shipped
global lemma, run over `W` while staying on `X`.  The statement is packaged
verbatim as `RelativeLemmaWStatement`/`relativeLemmaW` so downstream
assembly is plumbing.

**What remains open here**: no `Γ`-acyclicity of any sheaf is claimed or
approached in this file — `Γ`-surjectivity of one short exact sequence at a
time, over one open at a time, is all that is proven.  No statement below is
about the cohomology of anything; no cohomology group of any kind is
mentioned, computed, or related to another.  The word "singular" is not used
below for any sheaf-level carrier: the carriers are the sheafified cochain
sheaves of `HodgePilot.SingularResolution`.  **Nothing here identifies sheaf
cohomology with singular cohomology in any degree, and nothing here makes the
Hodge conjecture statable.**
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  HodgePilot.SingularResolution HodgePilot.SingularFineness HodgePilot.SingularGamma

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.SingularGammaRel

/-! ## Relative local lifts -/

set_option backward.isDefEq.respectTransparency false in
/-- **Relative local lifts**: an epimorphism of abelian sheaves admits local
lifts, on opens inside `W`, of any section of the target over `W`.-/
lemma exists_local_lift_rel {X : TopCat.{0}} {B R : TopCat.Sheaf AddCommGrpCat.{0} X}
    (g : B ⟶ R) [Epi g] {W : Opens X} (r : R.1.obj (op W)) (x : ↑X) (hx : x ∈ W) :
    ∃ (V : Opens X) (hVW : V ≤ W) (_ : x ∈ V) (b : B.1.obj (op V)),
      g.hom.app (op V) b = R.1.map (homOfLE hVW).op r := by
  have hls : TopCat.Presheaf.IsLocallySurjective g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr inferInstance
  obtain ⟨V, hVW, ⟨b, hb⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp hls W r x hx
  exact ⟨V, hVW, hxV, b, hb⟩

/-! ## Relative cover packs -/

set_option backward.isDefEq.respectTransparency false in
/-- A cover pack over an open `O` extracted from support data whose local
finiteness is recorded only pointwise at the points of `O`: each point of `O`
gets an open neighbourhood inside `O` meeting only a finite, recorded set of
the supports.  (The shipped `exists_pack` asked for global local finiteness
but used only this.)-/
lemma exists_pack_rel {X : TopCat.{0}} {ι : Type} (Z : ι → Set ↑X) (O : Opens X)
    (hlf : ∀ x : ↑X, x ∈ O → ∃ N ∈ nhds x, {i | (Z i ∩ N).Nonempty}.Finite) :
    ∃ (V : ↥O → Opens X) (S : ↥O → Finset ι),
      (∀ y : ↥O, V y ≤ O) ∧ (O ≤ ⨆ y, V y) ∧
        ∀ y i, i ∉ S y → Disjoint ((V y : Opens X) : Set ↑X) (Z i) := by
  choose N hN hfin using fun y : ↥O => hlf (y : ↑X) y.2
  refine ⟨fun y => ⟨interior (N y), isOpen_interior⟩ ⊓ O,
    fun y => (hfin y).toFinset, fun y => inf_le_right,
    fun x hx => Opens.mem_iSup.mpr
      ⟨⟨x, hx⟩, ⟨mem_interior_iff_mem_nhds.mpr (hN ⟨x, hx⟩), hx⟩⟩, ?_⟩
  intro y i hi
  rw [Set.Finite.mem_toFinset] at hi
  refine Set.disjoint_left.mpr (fun a ha hZa => hi ⟨a, hZa, ?_⟩)
  exact interior_subset ha.1

/-! ## The relative subordinate partition -/

set_option backward.isDefEq.respectTransparency false in
/-- **Relative subordinate partition**: for an open `W` of a Hausdorff space
whose subspace topology is paracompact, any family of ambient opens covering
`W` admits a partition of `W` into (arbitrary) subsets, one per cover member,
such that the ambient closure of each piece meets `W` inside the corresponding
cover member and the supports `closure (A i) ∩ W` are pointwise locally finite
at the points of `W`.  This is the shipped `exists_subordinate_partition`
instantiated at the subspace `TopCat.of ↥W` and transported along the open
inclusion (closure in `W` = ambient closure intersected with `W`).-/
lemma exists_subordinate_partition_rel {X : TopCat.{0}} [T2Space ↑X]
    (W : Opens X) [ParacompactSpace ↥W]
    {ι : Type} (u : ι → Opens X) (hu : W ≤ ⨆ i, u i) :
    ∃ A : ι → Set ↑X,
      (∀ i, A i ⊆ (W : Set ↑X))
      ∧ (∀ y : ↑X, y ∈ W → ∃! i, y ∈ A i)
      ∧ (∀ i, closure (A i) ∩ (W : Set ↑X) ⊆ ((u i : Opens X) : Set ↑X))
      ∧ (∀ x : ↑X, x ∈ W →
          ∃ N ∈ nhds x, {i | (closure (A i) ∩ (W : Set ↑X) ∩ N).Nonempty}.Finite) := by
  haveI : ParacompactSpace ↑(TopCat.of ↥W) := inferInstanceAs (ParacompactSpace ↥W)
  haveI : T2Space ↑(TopCat.of ↥W) := inferInstanceAs (T2Space ↥W)
  obtain ⟨A', hA', hclA', hlf'⟩ :=
    exists_subordinate_partition (X := TopCat.of ↥W)
      (fun i => ⟨Subtype.val ⁻¹' ((u i : Opens X) : Set ↑X),
        (u i).isOpen.preimage continuous_subtype_val⟩)
      (fun y _ => Opens.mem_iSup.mpr (by
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hu y.2)
        exact ⟨i, hi⟩))
  -- retype the three receipts once at the subtype spelling
  have hA'' : ∀ y : ↥W, ∃! i, y ∈ A' i := hA'
  have hcl'' : ∀ i, closure (A' i) ⊆ Subtype.val ⁻¹' ((u i : Opens X) : Set ↑X) := hclA'
  have hlf'' : LocallyFinite (fun i => closure (A' i)) := hlf'
  -- closure of a subtype set through the (open) inclusion
  have hclosure : ∀ i, closure (A' i)
      = Subtype.val ⁻¹' closure (Subtype.val '' A' i) := fun i =>
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image (A' i)
  refine ⟨fun i => Subtype.val '' A' i, ?_, ?_, ?_, ?_⟩
  · -- the pieces live in `W`
    rintro i z ⟨z', _, rfl⟩
    exact z'.2
  · -- exactly one piece per point of `W`
    intro y hy
    obtain ⟨i₀, hi₀, huniq⟩ := hA'' ⟨y, hy⟩
    refine ⟨i₀, ⟨⟨y, hy⟩, hi₀, rfl⟩, fun k hk => ?_⟩
    obtain ⟨z, hz, hzy⟩ := hk
    have hzeq : z = (⟨y, hy⟩ : ↥W) := Subtype.ext hzy
    rw [hzeq] at hz
    exact huniq k hz
  · -- ambient-closure-in-`W` containment
    rintro i z ⟨hzc, hzW⟩
    have hz' : (⟨z, hzW⟩ : ↥W) ∈ closure (A' i) := by
      rw [hclosure i]
      exact hzc
    exact hcl'' i hz'
  · -- pointwise local finiteness of the supports at points of `W`
    intro x hx
    obtain ⟨N', hN', hfin⟩ := hlf'' (⟨x, hx⟩ : ↥W)
    refine ⟨Subtype.val '' N',
      (W.isOpen.isOpenMap_subtype_val).image_mem_nhds hN', hfin.subset ?_⟩
    rintro i ⟨z, ⟨⟨hzc, hzW⟩, z', hz'N, rfl⟩⟩
    refine ⟨z', ?_, hz'N⟩
    show z' ∈ closure (A' i)
    rw [hclosure i]
    exact hzc

/-! ## The relative correction family -/

set_option backward.isDefEq.respectTransparency false in
/-- **The relative correction family**: given a family of opens `V i ≤ W`, a
partition of `W` whose ambient closures meet `W` inside the corresponding
`V i` with pointwise-at-`W` locally finite supports, and a family `δ` of
sections of the sheafified cochain sheaf over the pairwise intersections
satisfying the restricted cocycle identity, there is a family `c i` of
sections over the `V i` whose overlap differences recover `δ` — each `c i` is
the locally finite sum over `j` of the extension by zero of the
`A j`-partition image of `δ i j`, exactly as in the shipped global
`exists_correction`; the supports are `closure (A j) ∩ W`, and an open inside
`W` disjoint from `closure (A j) ∩ W` is disjoint from `closure (A j)`, so
every shipped receipt fires unchanged.-/
lemma exists_correction_rel (X : TopCat.{0}) (n : ℕ) {ι : Type}
    (W : Opens X) (A : ι → Set ↑X) (V : ι → Opens X)
    (hVW : ∀ i, V i ≤ W)
    (hA : ∀ y : ↑X, y ∈ W → ∃! i, y ∈ A i)
    (hclA : ∀ j, closure (A j) ∩ (W : Set ↑X) ⊆ ((V j : Opens X) : Set ↑X))
    (hlf : ∀ x : ↑X, x ∈ W →
      ∃ N ∈ nhds x, {i | (closure (A i) ∩ (W : Set ↑X) ∩ N).Nonempty}.Finite)
    (δ : ∀ i j : ι, ((sheafifiedCochainComplex X).X n).1.obj (op (V i ⊓ V j)))
    (hcoc : ∀ (i j k : ι) (O : Opens X) (h1 : O ≤ V i ⊓ V k) (h2 : O ≤ V j ⊓ V k)
      (h3 : O ≤ V i ⊓ V j),
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE h1).op (δ i k)
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE h2).op (δ j k)
        = ((sheafifiedCochainComplex X).X n).1.map (homOfLE h3).op (δ i j)) :
    ∃ c : ∀ i : ι, ((sheafifiedCochainComplex X).X n).1.obj (op (V i)),
      ∀ i j : ι,
        ((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i)
          - ((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)
          = δ i j := by
  classical
  have hVijW : ∀ i j : ι, V i ⊓ V j ≤ W := fun i _ => inf_le_left.trans (hVW i)
  have hZo : ∀ k : ι, IsOpen (closure (A k))ᶜ := fun k => isClosed_closure.isOpen_compl
  have hcov_ext : ∀ i j : ι,
      V i ≤ (V i ⊓ V j) ⊔ (⟨(closure (A j))ᶜ, hZo j⟩ : Opens X) := by
    intro i j y hy
    by_cases hyA : y ∈ closure (A j)
    · exact Opens.mem_sup.mpr (Or.inl ⟨hy, hclA j ⟨hyA, hVW i hy⟩⟩)
    · exact Opens.mem_sup.mpr (Or.inr hyA)
  have hs_ext : ∀ i j : ι, ((sheafifiedCochainComplex X).X n).1.map
      (homOfLE (inf_le_left :
        (V i ⊓ V j) ⊓ (⟨(closure (A j))ᶜ, hZo j⟩ : Opens X) ≤ V i ⊓ V j)).op
      ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j)) = 0 := by
    intro i j
    exact partitionEndoSheaf_app_supp X (A j) n (δ i j) _ inf_le_left
      (Set.disjoint_left.mpr (fun a ha => ha.2))
  have hsupp : ∀ (i j : ι) (O : Opens X) (hOW : O ≤ V i),
      Disjoint (O : Set ↑X) (closure (A j) ∩ (W : Set ↑X)) →
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE hOW).op
        (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i j)
          ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j))
          (hs_ext i j)) = 0 := by
    intro i j O hOW hd
    have hd' : Disjoint (O : Set ↑X) (closure (A j)) :=
      Set.disjoint_left.mpr (fun a haO haC =>
        Set.disjoint_left.mp hd haO ⟨haC, (hOW.trans (hVW i)) haO⟩)
    exact extendByZero_res_of_le _ _ _ _ _
      (fun a ha => Set.disjoint_left.mp hd' ha) hOW
  choose P T hPle hPcov hPT using fun i : ι =>
    exists_pack_rel (fun k => closure (A k) ∩ (W : Set ↑X)) (V i)
      (fun x hx => hlf x (hVW i hx))
  refine ⟨fun i => locFinSum ((sheafifiedCochainComplex X).X n)
    (fun j => extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i j)
      ((partitionEndoSheaf X (A j) n).hom.app (op (V i ⊓ V j)) (δ i j)) (hs_ext i j))
    (fun j => closure (A j) ∩ (W : Set ↑X)) (hsupp i) (P i) (hPle i) (hPcov i)
    (T i) (hPT i),
    fun i j => ?_⟩
  obtain ⟨Q, TQ, hQle, hQcov, hQT⟩ :=
    exists_pack_rel (fun k => closure (A k) ∩ (W : Set ↑X)) (V i ⊓ V j)
      (fun x hx => hlf x (hVijW i j hx))
  refine ((sheafifiedCochainComplex X).X n).eq_of_locally_eq' Q (V i ⊓ V j)
    (fun y => homOfLE (hQle y)) hQcov _ _ (fun y => ?_)
  have hQVi : Q y ≤ V i := (hQle y).trans inf_le_left
  have hQVj : Q y ≤ V j := (hQle y).trans inf_le_right
  have hQW : Q y ≤ W := (hQle y).trans (hVijW i j)
  rw [map_sub,
    res_res' ((sheafifiedCochainComplex X).X n) (homOfLE (hQle y))
      (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) (homOfLE hQVi) _,
    res_res' ((sheafifiedCochainComplex X).X n) (homOfLE (hQle y))
      (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) (homOfLE hQVj) _,
    locFinSum_res_adequate ((sheafifiedCochainComplex X).X n) _ _ (hsupp i)
      (P i) (hPle i) (hPcov i) (T i) (hPT i) hQVi (TQ y) (fun k hk => hQT y k hk),
    locFinSum_res_adequate ((sheafifiedCochainComplex X).X n) _ _ (hsupp j)
      (P j) (hPle j) (hPcov j) (T j) (hPT j) hQVj (TQ y) (fun k hk => hQT y k hk),
    ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ TQ y,
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE hQVi).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
            (hs_ext i k))
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE hQVj).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
            (hs_ext j k))
      = (partitionEndoSheaf X (A k) n).hom.app (op (Q y))
        (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)) := by
    intro k _
    have hU₁Vik : Q y ⊓ V k ≤ V i ⊓ V k := le_inf (inf_le_left.trans hQVi) inf_le_right
    have hU₁Vjk : Q y ⊓ V k ≤ V j ⊓ V k := le_inf (inf_le_left.trans hQVj) inf_le_right
    have hU₁Vij : Q y ⊓ V k ≤ V i ⊓ V j := inf_le_left.trans (hQle y)
    refine ((sheafifiedCochainComplex X).X n).eq_of_locally_eq₂
      (homOfLE (inf_le_left : Q y ⊓ V k ≤ Q y))
      (homOfLE (inf_le_left : Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y))
      (fun z hz => ?_) _ _ ?_ ?_
    · by_cases hzA : z ∈ closure (A k)
      · exact Opens.mem_sup.mpr (Or.inl ⟨hz, hclA k ⟨hzA, hQW hz⟩⟩)
      · exact Opens.mem_sup.mpr (Or.inr ⟨hz, hzA⟩)
    · -- restriction to Q y ⊓ V k
      rw [map_sub,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVi) (homOfLE (inf_le_left.trans hQVi)) _,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVj) (homOfLE (inf_le_left.trans hQVj)) _,
        ← res_res' ((sheafifiedCochainComplex X).X n) (homOfLE hU₁Vik)
          (homOfLE (inf_le_left : V i ⊓ V k ≤ V i))
          (homOfLE (inf_le_left.trans hQVi)) _,
        ← res_res' ((sheafifiedCochainComplex X).X n) (homOfLE hU₁Vjk)
          (homOfLE (inf_le_left : V j ⊓ V k ≤ V j))
          (homOfLE (inf_le_left.trans hQVj)) _,
        extendByZero_res ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
          ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
          (hs_ext i k),
        extendByZero_res ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
          ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
          (hs_ext j k),
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE hU₁Vik) (δ i k),
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE hU₁Vjk) (δ j k),
        ← map_sub, hcoc i j k (Q y ⊓ V k) hU₁Vik hU₁Vjk hU₁Vij,
        ← app_res (partitionEndoSheaf X (A k) n) (homOfLE (inf_le_left : Q y ⊓ V k ≤ Q y))
          (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)),
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE (hQle y)) (homOfLE hU₁Vij) _]
    · -- restriction to Q y ⊓ (closure (A k))ᶜ
      have h0i : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE ((inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y).trans hQVi)).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext i k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V i ⊓ V k)) (δ i k))
            (hs_ext i k)) = 0 :=
        extendByZero_res_of_le _ _ _ _ _ inf_le_right _
      have h0j : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE ((inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y).trans hQVj)).op
          (extendByZero ((sheafifiedCochainComplex X).X n) inf_le_left (hcov_ext j k)
            ((partitionEndoSheaf X (A k) n).hom.app (op (V j ⊓ V k)) (δ j k))
            (hs_ext j k)) = 0 :=
        extendByZero_res_of_le _ _ _ _ _ inf_le_right _
      have happ0 : ((sheafifiedCochainComplex X).X n).1.map
          (homOfLE (inf_le_left :
            Q y ⊓ (⟨(closure (A k))ᶜ, hZo k⟩ : Opens X) ≤ Q y)).op
          ((partitionEndoSheaf X (A k) n).hom.app (op (Q y))
            (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j)))
          = 0 :=
        partitionEndoSheaf_app_supp X (A k) n _ _ inf_le_left
          (disjoint_compl_left.mono_left Set.inter_subset_right)
      rw [map_sub,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVi) (homOfLE (inf_le_left.trans hQVi)) _,
        res_res' ((sheafifiedCochainComplex X).X n) (homOfLE inf_le_left)
          (homOfLE hQVj) (homOfLE (inf_le_left.trans hQVj)) _,
        h0i, h0j, happ0, sub_zero]
  rw [Finset.sum_congr rfl hterm]
  exact sum_partitionEndoSheaf_app_apply X A (TQ y) n
    (fun z hz => by
      obtain ⟨k₀, hk₀, huniq⟩ := hA z (hQW hz)
      have hkT : k₀ ∈ TQ y := by
        by_contra hns
        exact Set.disjoint_left.mp (hQT y k₀ hns) hz ⟨subset_closure hk₀, hQW hz⟩
      exact ⟨k₀, ⟨hkT, hk₀⟩, fun m hm => huniq m hm.2⟩)
    (((sheafifiedCochainComplex X).X n).1.map (homOfLE (hQle y)).op (δ i j))

/-! ## Relative Lemma W -/

set_option backward.isDefEq.respectTransparency false in
/-- **Relative Lemma W: `Γ`-surjectivity over an open with paracompact
subspace topology**: on a Hausdorff space `X`, for an open `W` whose subspace
topology is paracompact, every short exact sequence of abelian sheaves on `X`
whose kernel is a sheafified cochain sheaf has surjective induced map on
sections over `W`.  Steps A–E of the shipped global lemma, run over `W`.-/
theorem gammaSurjective_rel (X : TopCat.{0}) [T2Space ↑X]
    (W : Opens X) [ParacompactSpace ↥W] (n : ℕ)
    {B R : TopCat.Sheaf AddCommGrpCat.{0} X}
    (f : (sheafifiedCochainComplex X).X n ⟶ B) (g : B ⟶ R) (hfg : f ≫ g = 0)
    (hexact : (ShortComplex.mk f g hfg).ShortExact) :
    Function.Surjective (g.hom.app (op W)) := by
  intro r
  haveI hEpi : Epi g := hexact.epi_g
  haveI hMono : Mono f := hexact.mono_f
  -- Step A: local lifts of `r` inside `W` and a relative subordinate partition
  choose V hVW hxV b₀ hb₀ using fun y : ↥W => exists_local_lift_rel g r (y : ↑X) y.2
  have hcover : W ≤ ⨆ y, V y :=
    fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨A, -, hA, hclA, hlf⟩ := exists_subordinate_partition_rel W V hcover
  have hij : ∀ i j : ↥W, V i ⊓ V j ≤ W := fun i _ => inf_le_left.trans (hVW i)
  -- Step B: the overlap differences of the lifts come from the kernel sheaf
  have hdiffzero : ∀ i j : ↥W, g.hom.app (op (V i ⊓ V j))
      (B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
        - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)) = 0 := by
    intro i j
    rw [map_sub, app_res g (homOfLE inf_le_left) (b₀ i),
      app_res g (homOfLE inf_le_right) (b₀ j), hb₀ i, hb₀ j,
      res_res' R (homOfLE inf_le_left) (homOfLE (hVW i)) (homOfLE (hij i j)) r,
      res_res' R (homOfLE inf_le_right) (homOfLE (hVW j)) (homOfLE (hij i j)) r,
      sub_self]
  choose δ hδ using fun i j : ↥W => (existsUnique_section_preimage f g hfg hexact
    (V i ⊓ V j) _ (hdiffzero i j)).exists
  -- Step B': the restricted cocycle identity, by injectivity of `f`
  have hcoc : ∀ (i j k : ↥W) (O : Opens X) (h1 : O ≤ V i ⊓ V k) (h2 : O ≤ V j ⊓ V k)
      (h3 : O ≤ V i ⊓ V j),
      ((sheafifiedCochainComplex X).X n).1.map (homOfLE h1).op (δ i k)
        - ((sheafifiedCochainComplex X).X n).1.map (homOfLE h2).op (δ j k)
        = ((sheafifiedCochainComplex X).X n).1.map (homOfLE h3).op (δ i j) := by
    intro i j k O h1 h2 h3
    apply app_injective_of_mono f O
    have hOVi : O ≤ V i := h1.trans inf_le_left
    have hOVj : O ≤ V j := h2.trans inf_le_left
    have hOVk : O ≤ V k := h1.trans inf_le_right
    rw [map_sub, app_res f (homOfLE h1) (δ i k), app_res f (homOfLE h2) (δ j k),
      app_res f (homOfLE h3) (δ i j), hδ i k, hδ j k, hδ i j,
      map_sub, map_sub, map_sub,
      res_res' B (homOfLE h1) (homOfLE (inf_le_left : V i ⊓ V k ≤ V i))
        (homOfLE hOVi) (b₀ i),
      res_res' B (homOfLE h1) (homOfLE (inf_le_right : V i ⊓ V k ≤ V k))
        (homOfLE hOVk) (b₀ k),
      res_res' B (homOfLE h2) (homOfLE (inf_le_left : V j ⊓ V k ≤ V j))
        (homOfLE hOVj) (b₀ j),
      res_res' B (homOfLE h2) (homOfLE (inf_le_right : V j ⊓ V k ≤ V k))
        (homOfLE hOVk) (b₀ k),
      res_res' B (homOfLE h3) (homOfLE (inf_le_left : V i ⊓ V j ≤ V i))
        (homOfLE hOVi) (b₀ i),
      res_res' B (homOfLE h3) (homOfLE (inf_le_right : V i ⊓ V j ≤ V j))
        (homOfLE hOVj) (b₀ j)]
    abel
  -- Step C: the relative correction family
  obtain ⟨c, hc⟩ := exists_correction_rel X n W A V hVW hA hclA hlf δ hcoc
  -- Step D: the corrected lifts agree on overlaps
  have hcompat : ∀ i j : ↥W,
      B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
          (b₀ i - f.hom.app (op (V i)) (c i))
        = B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
          (b₀ j - f.hom.app (op (V j)) (c j)) := by
    intro i j
    rw [map_sub, map_sub,
      ← app_res f (homOfLE inf_le_left) (c i),
      ← app_res f (homOfLE inf_le_right) (c j)]
    have hfc : f.hom.app (op (V i ⊓ V j))
          (((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
        - f.hom.app (op (V i ⊓ V j))
          (((sheafifiedCochainComplex X).X n).1.map
            (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j))
        = B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
          - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j) := by
      rw [← map_sub, hc i j, hδ i j]
    calc B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
          - f.hom.app (op (V i ⊓ V j))
            (((sheafifiedCochainComplex X).X n).1.map
              (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
        = (B.1.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b₀ i)
            - B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j))
          - (f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (c i))
            - f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)))
          + (B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)
            - f.hom.app (op (V i ⊓ V j))
              (((sheafifiedCochainComplex X).X n).1.map
                (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j))) := by abel
      _ = B.1.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b₀ j)
          - f.hom.app (op (V i ⊓ V j))
            (((sheafifiedCochainComplex X).X n).1.map
              (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (c j)) := by
          rw [hfc, sub_self, zero_add]
  -- Step E: glue the corrected lifts over `W` and conclude
  obtain ⟨b, hb, -⟩ := B.existsUnique_gluing' V W (fun i => homOfLE (hVW i)) hcover
    (fun i => b₀ i - f.hom.app (op (V i)) (c i))
    (fun i j => hcompat i j)
  refine ⟨b, ?_⟩
  refine R.eq_of_locally_eq' V W (fun i => homOfLE (hVW i)) hcover _ _ (fun i => ?_)
  rw [← app_res g (homOfLE (hVW i)) b, hb i, map_sub, hb₀ i,
    comp_app_apply_eq_zero f g hfg (V i) (c i), sub_zero]

/-! ## The packaged statement shape -/

/-- **Statement shape of relative Lemma W** (for downstream assembly): for
every open `W` with paracompact subspace topology and every short exact
sequence of abelian sheaves on `X` whose kernel is a sheafified cochain sheaf,
the induced map on sections over `W` is surjective.-/
def RelativeLemmaWStatement (X : TopCat.{0}) [T2Space ↑X] : Prop :=
  ∀ (W : Opens X), ParacompactSpace ↥W → ∀ (n : ℕ)
    ⦃B R : TopCat.Sheaf AddCommGrpCat.{0} X⦄
    (f : (sheafifiedCochainComplex X).X n ⟶ B) (g : B ⟶ R)
    (hfg : f ≫ g = 0), (ShortComplex.mk f g hfg).ShortExact →
    Function.Surjective (g.hom.app (op W))

/-- Relative Lemma W, packaged in the statement shape: on every Hausdorff
space, `RelativeLemmaWStatement` holds.-/
theorem relativeLemmaW (X : TopCat.{0}) [T2Space ↑X] : RelativeLemmaWStatement X := by
  intro W hW n B R f g hfg hexact
  haveI := hW
  exact gammaSurjective_rel X W n f g hfg hexact

end HodgePilot.SingularGammaRel
