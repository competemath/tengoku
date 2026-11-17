import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

open TopologicalSpace Topology

namespace ExtendDefNoeth

/--
@isnad1 id=isopen.0h2v.s4.f7ab073973fa from=translated src=- shape=4927a877 vocab=9a12ad69
-/
theorem isOpen_connectedComponent_of_noetherianSpace {α : Type} [TopologicalSpace α] [NoetherianSpace α]
    (x : α) : IsOpen (connectedComponent x) := by
  classical
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcl : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  have heq : (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents α | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZC⟩, hyZ⟩ hyC
      apply hZC
      rw [connectedComponent_eq hyC]
      exact hZ.1.2.isPreconnected.subset_connectedComponent hyZ
  rw [← isClosed_compl_iff, heq]
  exact hcl

/--
@isnad1 id=or.1h2v.s6.1294d71df5e0 from=translated src=- shape=9256402a vocab=612acb1b
-/
theorem isIdempotentElem_eq_zero_or_one_of_preconnectedSpace {S : Type} [CommRing S]
    [PreconnectedSpace (PrimeSpectrum S)] (f : S) (hf : IsIdempotentElem f) : f = 0 ∨ f = 1 := by
  have key : ∀ g : S, IsIdempotentElem g → (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = ∅ → g = 0 := by
    intro g hg h
    have hbot : PrimeSpectrum.basicOpen g = ⊥ := TopologicalSpace.Opens.ext (by simpa using h)
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_eq_bot_iff g).mp hbot
    cases n with
    | zero =>
      rw [pow_zero] at hn
      rw [← mul_one g, hn, mul_zero]
    | succ n => rw [← hg.pow_succ_eq n, hn]
  have hclopen : IsClopen (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨f, hf, rfl⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact Or.inl (key f hf h)
  · right
    have h1 : (PrimeSpectrum.basicOpen (1 - f) : Set (PrimeSpectrum S)) = ∅ := by
      rw [← PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem f hf]
      exact Set.compl_univ_iff.mp (by rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl]; exact h)
    have := key (1 - f) hf.one_sub h1
    exact (sub_eq_zero.mp this).symm

section comp

variable (B : Type) [CommRing B]

def Comp : Type := {C : Set (PrimeSpectrum B) // ∃ p : PrimeSpectrum B, C = connectedComponent p}

variable {B}

theorem Comp.eq_of_mem {C C' : Comp B} {y : PrimeSpectrum B} (h : y ∈ C.1) (h' : y ∈ C'.1) : C = C' := by
  obtain ⟨p, hp⟩ := C.2
  obtain ⟨p', hp'⟩ := C'.2
  apply Subtype.ext
  rw [hp] at h ⊢; rw [hp'] at h' ⊢
  rw [connectedComponent_eq h, connectedComponent_eq h']

/--
@isnad1 id=isprecon.0h2v.s6.600cfecc8d9d from=translated src=- shape=99d05c9a vocab=e072e4c1
-/
theorem Comp.isPreconnected (C : Comp B) : _root_.IsPreconnected C.1 := by
  obtain ⟨p, hp⟩ := C.2
  rw [hp]; exact isPreconnected_connectedComponent

variable [IsNoetherianRing B]

/--
@isnad1 id=isclopen.0h2v.s6.bd70a5948a61 from=translated src=- shape=a365de58 vocab=75e01a0b
-/
theorem Comp.isClopen (C : Comp B) : IsClopen C.1 := by
  obtain ⟨p, hp⟩ := C.2
  rw [hp]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace p⟩

noncomputable def Comp.idem (C : Comp B) : B := (PrimeSpectrum.isClopen_iff.mp C.isClopen).choose

/--
@isnad1 id=and.0h2v.s6.d5e0d8aa47d6 from=translated src=- shape=7c4baf7b vocab=e58df73f
-/
theorem Comp.idem_spec (C : Comp B) :
    IsIdempotentElem C.idem ∧ C.1 = ↑(PrimeSpectrum.basicOpen C.idem) :=
  (PrimeSpectrum.isClopen_iff.mp C.isClopen).choose_spec

abbrev Comp.Piece (C : Comp B) : Type := Localization.Away C.idem

/--
@isnad1 id=eq.0h2v.s7.26028338f1aa from=translated src=- shape=a2061667 vocab=e2b8424f
-/
theorem Comp.range_comap (C : Comp B) :
    Set.range (PrimeSpectrum.comap (algebraMap B C.Piece)) = C.1 := by
  rw [PrimeSpectrum.localization_away_comap_range C.Piece C.idem, ← C.idem_spec.2]

/--
@isnad1 id=or.1h3v.s7.97e19696b0fc from=translated src=- shape=de3b67aa vocab=88935192
-/
theorem Comp.piece_connected (C : Comp B) : ∀ f : C.Piece, IsIdempotentElem f → f = 0 ∨ f = 1 := by
  have hemb := PrimeSpectrum.localization_away_isOpenEmbedding C.Piece C.idem
  haveI : PreconnectedSpace (PrimeSpectrum C.Piece) := ⟨by
    rw [← hemb.isInducing.isPreconnected_image, Set.image_univ, C.range_comap]
    exact C.isPreconnected⟩
  exact isIdempotentElem_eq_zero_or_one_of_preconnectedSpace

def Comp.of (p : PrimeSpectrum B) : Comp B := ⟨connectedComponent p, p, rfl⟩

omit [IsNoetherianRing B] in
/--
@isnad1 id=mem.0h2v.s6.c025931805f8 from=translated src=- shape=11da2f7f vocab=d62e1fa6
-/
theorem Comp.mem_of (p : PrimeSpectrum B) : p ∈ (Comp.of p).1 := mem_connectedComponent

end comp

section cover

variable (B : Type) [CommRing B] [IsNoetherianRing B]

noncomputable abbrev cover : (Spec (CommRingCat.of B)).OpenCover where
  I₀ := Comp B
  X C := Spec (CommRingCat.of C.Piece)
  f C := Spec.map (CommRingCat.ofHom (algebraMap B C.Piece))
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p => ⟨Comp.of p, ?_⟩, fun C => inferInstance⟩
    have := (Comp.of p).range_comap
    exact (eq_iff_iff.mp congr(p ∈ $this)).mpr (Comp.mem_of p)

variable {B}

/--
@isnad1 id=mem.0h3v.s8.b0ac6cf04dcb from=translated src=- shape=58050118 vocab=5f5a667b
-/
theorem cover_f_apply_mem (C : Comp B) (a : ↥((cover B).X C)) : (cover B).f C a ∈ C.1 := by
  have := C.range_comap
  exact (eq_iff_iff.mp congr(((cover B).f C a) ∈ $this)).mp ⟨a, rfl⟩

/--
@isnad1 id=isempty.1h3v.s7.18fe41a20936 from=translated src=- shape=df2fa5f7 vocab=3b0fd29a
-/
theorem isEmpty_pullback_of_ne {C C' : Comp B} (h : C ≠ C') :
    IsEmpty ↥(Limits.pullback ((cover B).f C) ((cover B).f C')) := by
  refine ⟨fun z => h ?_⟩
  have e := congrArg (fun φ => φ z) (Limits.pullback.condition (f := (cover B).f C) (g := (cover B).f C'))
  simp only [Scheme.Hom.comp_apply] at e
  exact Comp.eq_of_mem (cover_f_apply_mem C _) (e ▸ cover_f_apply_mem C' _)

/--
@isnad1 id=eq.0h5v.s9.1ecd2b80b889 from=translated src=- shape=566e19d2 vocab=0acac3ab
-/
theorem compatible {Y : Scheme.{0}} (g : ∀ C : Comp B, (cover B).X C ⟶ Y) (C C' : Comp B) :
    Limits.pullback.fst ((cover B).f C) ((cover B).f C') ≫ g C = Limits.pullback.snd ((cover B).f C) ((cover B).f C') ≫ g C' := by
  classical
  by_cases h : C = C'
  · subst h
    rw [Limits.fst_eq_snd_of_mono_eq]
  · haveI := isEmpty_pullback_of_ne h
    exact (isInitialOfIsEmpty).hom_ext _ _

end cover

section extend

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
  {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))
  (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
    (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → F.obj B → (Scheme.nilpPoints fN).obj B)

/--
@isnad1 id=isnilpot.1h4v.s8.e309770641f8 from=translated src=- shape=61838ef1 vocab=635834eb
-/
theorem nilp_piece {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (C : Comp B) : IsNilpotent (algebraMap 𝒪 C.Piece π) := by
  rw [IsScalarTower.algebraMap_apply 𝒪 B C.Piece]
  exact hB.map _

noncomputable def piece {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) (C : Comp B) : (cover B).X C ⟶ N :=
  (u C.Piece (nilp_piece π hB C) C.piece_connected (F.map (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)).1

noncomputable def glue {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) : Spec (CommRingCat.of B) ⟶ N :=
  (cover B).glueMorphisms (piece π F fN u hB x) (compatible _)

/--
@isnad1 id=eq.1h9v.s8.248b51e3de8f from=translated src=- shape=198dcc89 vocab=dc4fd6ef
-/
theorem cover_f_glue {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) (C : Comp B) : (cover B).f C ≫ glue π F fN u hB x = piece π F fN u hB x C := by
  rw [glue]
  exact Scheme.Cover.ι_glueMorphisms (cover B) (piece π F fN u hB x) (compatible (piece π F fN u hB x)) C

/--
@isnad1 id=eq.0h3v.s7.7f718dcdf8bf from=translated src=- shape=6fd2c92d vocab=c7bbc631
-/
theorem cover_f_comp_specOver {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (C : Comp B) :
    (cover B).f C ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver C.Piece :=
  Scheme.specMap_algHom_comp_specOver (IsScalarTower.toAlgHom 𝒪 B C.Piece)

noncomputable def UN (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (x : F.obj B) : (Scheme.nilpPoints fN).obj B :=
  ⟨glue π F fN u hB x, by
    refine (cover B).hom_ext _ _ fun C => ?_
    rw [← Category.assoc, cover_f_glue, cover_f_comp_specOver]
    exact (u C.Piece (nilp_piece π hB C) C.piece_connected (F.map (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)).2⟩

variable (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
    (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
    (φ : B →ₐ[𝒪] B') (x : F.obj B),
    u B' hB' hc' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x))

include hu in

/--
@isnad1 id=eq.3h8v.s9.487ab88d1612 from=translated src=- shape=a332a027 vocab=bbc96789
-/
theorem UN_eq {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : F.obj B) : UN π F fN u B hB x = u B hB hc x := by
  apply Subtype.ext
  refine (cover B).hom_ext _ _ fun C => ?_
  show (cover B).f C ≫ glue π F fN u hB x = (cover B).f C ≫ (u B hB hc x).1
  rw [cover_f_glue]
  have h := congrArg Subtype.val (hu B C.Piece hB (nilp_piece π hB C) hc C.piece_connected (IsScalarTower.toAlgHom 𝒪 B C.Piece) x)
  rw [Scheme.nilpPoints_map_val] at h
  exact h

/--
@isnad1 id=isunit.1h4v.s7.6f5044e2f247 from=translated src=- shape=cb91a789 vocab=d22625fd
-/
theorem isUnit_of_range_comap_subset {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (b : R)
    (h : Set.range (PrimeSpectrum.comap g) ⊆ ↑(PrimeSpectrum.basicOpen b)) : IsUnit (g b) := by
  by_contra hb
  obtain ⟨m, hm, hbm⟩ := Ideal.exists_le_maximal (Ideal.span {g b}) ((Ideal.span_singleton_ne_top) hb)
  have hq := h ⟨⟨m, hm.isPrime⟩, rfl⟩
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq
  exact hq (hbm (Ideal.mem_span_singleton_self _))

variable {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
  (φ : B →ₐ[𝒪] B')

noncomputable def back (C' : Comp B') : Comp B := Comp.of (PrimeSpectrum.comap φ.toRingHom C'.2.choose)

/--
@isnad1 id=le.0h5v.s8.60c7bcbd06c5 from=translated src=- shape=a1243c00 vocab=86cd8a32
-/
theorem range_subset_back (C' : Comp B') :
    Set.range (PrimeSpectrum.comap ((algebraMap B' C'.Piece).comp φ.toRingHom)) ⊆ (back φ C').1 := by
  have hp' : C'.1 = connectedComponent C'.2.choose := C'.2.choose_spec
  have hr : Set.range (PrimeSpectrum.comap ((algebraMap B' C'.Piece).comp φ.toRingHom)) =
      PrimeSpectrum.comap φ.toRingHom '' C'.1 := by
    rw [← C'.range_comap, ← Set.range_comp]
    rfl
  rw [hr]
  refine (C'.isPreconnected.image _ (PrimeSpectrum.continuous_comap φ.toRingHom).continuousOn).subset_connectedComponent ?_
  exact ⟨C'.2.choose, ((Set.ext_iff.mp hp') _).mpr mem_connectedComponent, rfl⟩

/--
@isnad1 id=isunit.0h5v.s8.14d430aaf9d1 from=translated src=- shape=f0473442 vocab=38f34ab7
-/
theorem isUnit_back (C' : Comp B') : IsUnit (((algebraMap B' C'.Piece).comp φ.toRingHom) (back φ C').idem) :=
  isUnit_of_range_comap_subset _ _ ((back φ C').idem_spec.2 ▸ range_subset_back φ C')

private noncomputable def _root_.ExtendDefNoeth.lift (C' : Comp B') : (back φ C').Piece →ₐ[𝒪] C'.Piece where
  toRingHom := IsLocalization.Away.lift (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C')
  commutes' r := by
    have h := congrArg (fun g => g (algebraMap 𝒪 B r)) (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C'))
    simp only [RingHom.comp_apply] at h
    rw [IsScalarTower.algebraMap_apply 𝒪 B (back φ C').Piece, IsScalarTower.algebraMap_apply 𝒪 B' C'.Piece]
    refine h.trans ?_
    change algebraMap B' C'.Piece (φ (algebraMap 𝒪 B r)) = _
    rw [AlgHom.commutes]

export _root_.ExtendDefNoeth (lift)
/--
@isnad1 id=eq.0h5v.s9.71294c1bcd29 from=translated src=- shape=cc493c48 vocab=73e83b92
-/
theorem lift_comp_toAlgHom (C' : Comp B') :
    (lift φ C').comp (IsScalarTower.toAlgHom 𝒪 B (back φ C').Piece) = (IsScalarTower.toAlgHom 𝒪 B' C'.Piece).comp φ := by
  apply AlgHom.ext
  intro b
  have h := congrArg (fun g => g b) (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C'))
  exact h

/--
@isnad1 id=eq.0h5v.s9.45b710584cc3 from=translated src=- shape=31f68c14 vocab=5c1698cb
-/
theorem cover_f_comp_specMap (C' : Comp B') :
    (cover B').f C' ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
      Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ (cover B).f (back φ C') := by
  show Spec.map (CommRingCat.ofHom (algebraMap B' C'.Piece)) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
    Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B (back φ C').Piece))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (IsLocalization.Away.lift_comp (S := (back φ C').Piece) (back φ C').idem (isUnit_back φ C')).symm

include hu in
/--
@isnad1 id=eq.3h10v.s9.7f23c6c3b92e from=translated src=- shape=89dfdd15 vocab=bbc96789
-/
theorem UN_nat (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (x : F.obj B) :
    UN π F fN u B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (UN π F fN u B hB x) := by
  apply Subtype.ext
  rw [Scheme.nilpPoints_map_val]
  refine (cover B').hom_ext _ _ fun C' => ?_
  show (cover B').f C' ≫ glue π F fN u hB' (F.map φ x) = (cover B').f C' ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ glue π F fN u hB x)
  have e2 : (cover B').f C' ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ glue π F fN u hB x) =
      Spec.map (CommRingCat.ofHom (lift φ C').toRingHom) ≫ piece π F fN u hB x (back φ C') := by
    rw [← cover_f_glue π F fN u hB x (back φ C'), ← Category.assoc, ← Category.assoc, cover_f_comp_specMap]
  rw [cover_f_glue, e2]

  have h := congrArg Subtype.val (hu (back φ C').Piece C'.Piece (nilp_piece π hB (back φ C')) (nilp_piece π hB' C')
    (back φ C').piece_connected C'.piece_connected (lift φ C') (F.map (IsScalarTower.toAlgHom 𝒪 B (back φ C').Piece) x))
  rw [Scheme.nilpPoints_map_val, ← F.map_comp, lift_comp_toAlgHom, F.map_comp] at h
  exact h

end extend

end ExtendDefNoeth

open ExtendDefNoeth in
/--
@isnad1 id=existsun.1h6v.s10.b50b9cd16f08 from=translated src=- shape=b8cba172 vocab=79e3fd30
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → F.obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
      (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u B' hB' hc' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x)) :
    ∃! U : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints fN).obj B,

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
          U B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : F.obj B), U B hB x = u B hB hc x) := by
  classical
  refine ⟨UN π F fN u, ⟨?_, ?_⟩, ?_⟩
  · intro B _ _ _ B' _ _ _ hB hB' φ x
    exact UN_nat π F fN u hu φ hB hB' x
  · intro B _ _ _ hB hc x
    exact UN_eq π F fN u hu hB hc x
  · rintro U' ⟨hU'nat, hU'u⟩
    funext B instB instN instA hB x
    exact AlgebraicGeometry.Scheme.nilpPoints.forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem π F fN
      U' (UN π F fN u) hU'nat (fun B _ _ _ B' _ _ _ hB hB' φ x => UN_nat π F fN u hu φ hB hB' x)
      (fun B _ _ _ hB hc x => by rw [hU'u B hB hc x, UN_eq π F fN u hu hB hc x]) B hB x
