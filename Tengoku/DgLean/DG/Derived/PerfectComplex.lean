import Tengoku.Seed.Algebra.Category.ModuleCat.Projective
import Tengoku.Seed.Algebra.Homology.DerivedCategory.FullyFaithful
import Tengoku.Seed.Algebra.Homology.DerivedCategory.KProjective
import Tengoku.Seed.Algebra.Homology.Embedding.CochainComplex
import Tengoku.DgLean.DG.K0.Euler
import Tengoku.DgLean.DG.K0.ProjectiveModules

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Perfect complexes over a ring

Let `R` be a ring. A *perfect complex* over `R` is a strictly bounded cochain complex of finitely
generated projective `R`-modules (`DG.IsPerfectComplex`, a property of Mathlib's
`CochainComplex (ModuleCat R) ℤ`); an object of Mathlib's derived category
`DerivedCategory (ModuleCat R)` is *perfect* if it is isomorphic to the image of a perfect
complex (`DG.IsPerfect R`). See The Stacks Project, Chapter "More on Algebra", Section "Perfect
complexes".

## Main definitions and results

* `DG.IsPerfectComplex K`, with the closure properties `DG.IsPerfectComplex.of_iso`,
  `DG.IsPerfectComplex.mappingCone`, `DG.IsPerfectComplex.shift`, `DG.IsPerfectComplex.single`.
* `DG.IsPerfectComplex.eulerChar : DG.ProjK0 R`: the Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]` of a
  perfect complex in the Grothendieck group of finitely generated projective modules;
  `DG.IsPerfectComplex.eulerChar_mappingCone` (`χ(C(φ)) = χ(L) - χ(K)` for `φ : K ⟶ L`),
  `DG.IsPerfectComplex.eulerChar_single`.
* `DG.IsPerfectComplex.eulerChar_eq_zero_of_homotopy`: a contractible perfect complex has Euler
  characteristic `0` (its cocycles are finitely generated projective and the alternating sum
  telescopes).
* `DG.IsPerfectComplex.isKProjective`: a perfect complex is K-projective, so morphisms out of it
  in the derived category are homotopy classes of morphisms of complexes
  (`DG.IsPerfectComplex.exists_Q_map_eq`, `DG.IsPerfectComplex.nonempty_homotopy_of_Q_map_eq`).
* `DG.IsPerfectComplex.eulerChar_eq_of_iso_Q`: perfect complexes which are isomorphic in the
  derived category have the same Euler characteristic.
* `DG.IsPerfect R`: the perfect objects of the derived category, closed under isomorphisms,
  shifts and cones (`DG.IsPerfect.of_iso`, `DG.IsPerfect.shift`, `DG.IsPerfect.ext₂`,
  `DG.IsPerfect.ext₃`). Closure under direct summands is in `DG/Derived/PerfectThick.lean`.
-/

namespace DG

open CategoryTheory Category Limits Pretriangulated ZeroObject

universe w u

variable {R : Type u} [Ring R]

/-- A *perfect complex* over `R`: a strictly bounded cochain complex of finitely generated
projective `R`-modules.-/
structure IsPerfectComplex (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  /-- The complex is strictly bounded.-/
  bounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b
  /-- The terms are finitely generated projective modules.-/
  fgProjective : ∀ n, IsFGProjective R (K.X n)

namespace IsPerfectComplex

section Complex

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/--
@isnad1 id=ex.1h2v.s6.3fcf75a63233 from=translated src=- shape=0e181e5b vocab=3394a8b5
-/
theorem exists_bounds (hK : IsPerfectComplex K) :
    ∃ (a : ℤ) (m : ℕ), ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n) := by
  obtain ⟨a, b, _, _⟩ := hK.bounded
  refine ⟨a, (b + 1 - a).toNat, fun n hn => ?_⟩
  rcases hn with hn | hn
  · exact K.isZero_of_isStrictlyGE a n hn
  · exact K.isZero_of_isStrictlyLE b n (by omega)

/-- The Euler characteristic `χ(K) = Σₙ (-1)ⁿ [Kⁿ] ∈ K₀(R)` of a perfect complex.-/
noncomputable def eulerChar (hK : IsPerfectComplex K) : ProjK0.{u} R :=
  ∑ᶠ n : ℤ, n.negOnePow • ProjK0.mk (K.X n) (hK.fgProjective n)

/--
@isnad1 id=eq.2h4v.s8.5726a086a177 from=translated src=- shape=4f523244 vocab=c30910b3
-/
theorem eulerChar_eq_sum_range (hK : IsPerfectComplex K) (a : ℤ) (m : ℕ)
    (h : ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n)) :
    hK.eulerChar = ∑ i ∈ Finset.range m,
      (a + i).negOnePow • ProjK0.mk (K.X (a + i)) (hK.fgProjective _) :=
  AbelianK0.finsum_eq_sum_range _ a m fun n hn => by
    rw [ProjK0.mk_eq_zero_of_isZero (h n hn), smul_zero]

/--
@isnad1 id=finite.1h2v.s7.fc9e78885069 from=translated src=- shape=9d83ccc0 vocab=da0f60f3
-/
theorem support_finite (hK : IsPerfectComplex K) :
    (Function.support fun n : ℤ => n.negOnePow • ProjK0.mk (K.X n) (hK.fgProjective n)).Finite
    := by
  obtain ⟨a, m, h⟩ := hK.exists_bounds
  refine (Set.finite_Ico a (a + m)).subset fun n hn => ?_
  by_contra h'
  simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h'
  exact hn (by
    change n.negOnePow • ProjK0.mk (K.X n) (hK.fgProjective n) = 0
    rw [ProjK0.mk_eq_zero_of_isZero (h n (by omega)), smul_zero])

/-- A cochain complex of finitely generated projective modules whose terms vanish outside
`[a, a + m)` is perfect.
@isnad1 id=isperfec.1h5v.s7.b45aa625db39 from=translated src=- shape=d9ea8afd vocab=df5596b5
-/
theorem mk' (hK : ∀ n, IsFGProjective R (K.X n)) (a : ℤ) (m : ℕ)
    (h : ∀ n, n < a ∨ a + m ≤ n → IsZero (K.X n)) : IsPerfectComplex K where
  bounded := ⟨a, a + m, (K.isStrictlyGE_iff a).2 fun i hi => h i (Or.inl hi),
    (K.isStrictlyLE_iff _).2 fun i hi => h i (Or.inr (by omega))⟩
  fgProjective := hK

/--
@isnad1 id=isperfec.1h4v.s7.904a17a5b858 from=translated src=- shape=f18430b8 vocab=324854ed
-/
theorem of_iso (e : K ≅ L) (hL : IsPerfectComplex L) : IsPerfectComplex K where
  bounded := by
    obtain ⟨a, b, _, _⟩ := hL.bounded
    exact ⟨a, b, L.isStrictlyGE_of_iso e.symm a, L.isStrictlyLE_of_iso e.symm b⟩
  fgProjective n := IsFGProjective.of_iso ((HomologicalComplex.eval _ _ n).mapIso e)
    (hL.fgProjective n)

/--
@isnad1 id=eq.2h4v.s7.055d751b3758 from=translated src=- shape=0f9d3b58 vocab=8d5965ef
-/
theorem eulerChar_eq_of_iso (e : K ≅ L) (hK : IsPerfectComplex K) (hL : IsPerfectComplex L) :
    hK.eulerChar = hL.eulerChar := by
  unfold eulerChar
  congr 1
  ext n
  rw [ProjK0.mk_eq_of_iso (P := K.X n) (Q := L.X n) ((HomologicalComplex.eval _ _ n).mapIso e)
    (hK.fgProjective n) (hL.fgProjective n)]

/-! ### Mapping cones -/

section MappingCone

open CochainComplex

variable (φ : K ⟶ L)

/-- The terms of the mapping cone: `C(φ)ⁿ ≅ Kⁿ⁺¹ ⊞ Lⁿ`.-/
noncomputable def mappingConeXIso (n : ℤ) : (mappingCone φ).X n ≅ K.X (n + 1) ⊞ L.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl

/--
@isnad1 id=isperfec.2h4v.s7.f1c5c3322d9b from=translated src=- shape=f73310e0 vocab=2b4fe78e
-/
theorem mappingCone (hK : IsPerfectComplex K) (hL : IsPerfectComplex L) :
    IsPerfectComplex (mappingCone φ) := by
  obtain ⟨a, m, hm⟩ := hK.exists_bounds
  obtain ⟨a', m', hm'⟩ := hL.exists_bounds
  refine mk' (fun n => IsFGProjective.of_iso (mappingConeXIso φ n)
    ((hK.fgProjective _).biprod (hL.fgProjective _))) (min (a - 1) a')
    (max (a + m) (a' + m') - min (a - 1) a').toNat ?_
  intro n hn
  refine IsZero.of_iso ?_ (mappingConeXIso φ n)
  rw [biprod_isZero_iff]
  constructor
  · exact hm _ (by omega)
  · exact hm' _ (by omega)

/--
@isnad1 id=eq.2h4v.s8.785d85b90246 from=translated src=- shape=eadd3281 vocab=73b988ee
-/
theorem eulerChar_mappingCone (hK : IsPerfectComplex K) (hL : IsPerfectComplex L) :
    (hK.mappingCone φ hL).eulerChar = hL.eulerChar - hK.eulerChar := by
  have h₁ : ∀ n : ℤ, n.negOnePow • ProjK0.mk ((CochainComplex.mappingCone φ).X n)
      ((hK.mappingCone φ hL).fgProjective n) =
      -((n + 1).negOnePow • ProjK0.mk (K.X (n + 1)) (hK.fgProjective _)) +
        n.negOnePow • ProjK0.mk (L.X n) (hL.fgProjective n) := fun n => by
    rw [ProjK0.mk_eq_of_iso (mappingConeXIso φ n) _
        ((hK.fgProjective _).biprod (hL.fgProjective _)), ProjK0.mk_biprod, smul_add,
      Int.negOnePow_succ, Units.neg_smul, neg_neg]
  have hfK : Function.HasFiniteSupport fun n : ℤ =>
      -((n + 1).negOnePow • ProjK0.mk (K.X (n + 1)) (hK.fgProjective _)) := by
    have := hK.support_finite.preimage (f := fun n : ℤ => n + 1)
      (fun _ _ _ _ h => by simpa using h)
    refine this.subset fun n hn => ?_
    simpa using hn
  have h₂ : ∑ᶠ n : ℤ, (n + 1).negOnePow • ProjK0.mk (K.X (n + 1)) (hK.fgProjective _) =
      ∑ᶠ n : ℤ, n.negOnePow • ProjK0.mk (K.X n) (hK.fgProjective n) :=
    finsum_comp_equiv (Equiv.addRight (1 : ℤ))
      (f := fun n : ℤ => n.negOnePow • ProjK0.mk (K.X n) (hK.fgProjective n))
  unfold eulerChar
  rw [finsum_congr h₁, finsum_add_distrib hfK hL.support_finite, finsum_neg_distrib, h₂,
    neg_add_eq_sub]

end MappingCone

/--
@isnad1 id=isperfec.1h3v.s8.768ef7fb21d6 from=translated src=- shape=b0b264ae vocab=1a294408
-/
theorem shift (hK : IsPerfectComplex K) (n : ℤ) : IsPerfectComplex (K⟦n⟧) := by
  obtain ⟨a, m, hm⟩ := hK.exists_bounds
  refine mk' (fun i => IsFGProjective.of_iso (K.shiftFunctorObjXIso n i _ rfl)
    (hK.fgProjective _)) (a - n) m fun i hi => ?_
  exact IsZero.of_iso (hm _ (by omega)) (K.shiftFunctorObjXIso n i _ rfl)

/--
@isnad1 id=isperfec.0h4v.s6.ffb595575064 from=translated src=- shape=0c26acef vocab=eeeefffe
-/
theorem single {P : ModuleCat.{u} R} (hP : IsFGProjective R P) (n : ℤ) :
    IsPerfectComplex ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj P) := by
  refine mk' (fun i => ?_) n 1 fun i hi => HomologicalComplex.isZero_single_obj_X _ _ _ _
    (by omega)
  by_cases hi : i = n
  · subst hi
    exact IsFGProjective.of_iso (HomologicalComplex.singleObjXSelf _ i P) hP
  · exact IsFGProjective.of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/--
@isnad1 id=eq.0h4v.s7.79d5e4a872cc from=translated src=- shape=d7e86066 vocab=577fdbe4
-/
theorem eulerChar_single {P : ModuleCat.{u} R} (hP : IsFGProjective R P) (n : ℤ) :
    (single hP n).eulerChar = n.negOnePow • ProjK0.mk P hP := by
  unfold eulerChar
  rw [finsum_eq_single _ n (fun i hi => by
    rw [ProjK0.mk_eq_zero_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi),
      smul_zero]),
    ProjK0.mk_eq_of_iso (HomologicalComplex.singleObjXSelf _ n P) _ hP]

/--
@isnad1 id=isperfec.0h1v.s7.f242e0a64d16 from=translated src=- shape=52db5a99 vocab=34c6459a
-/
theorem zero : IsPerfectComplex (0 : CochainComplex (ModuleCat.{u} R) ℤ) :=
  mk' (fun i => IsFGProjective.of_isZero (by
    exact (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))) 0 0
    fun i _ => (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)

end Complex

/-! ### Contractible perfect complexes -/

section Contractible

variable {C : CochainComplex (ModuleCat.{u} R) ℤ}

omit [Ring R] in
theorem _root_.DG.d_apply_d_apply {R : Type u} [Ring R] {C : CochainComplex (ModuleCat.{u} R) ℤ}
    (i j k : ℤ) (x : C.X i) : (C.d j k).hom ((C.d i j).hom x) = 0 := by
  rw [← ModuleCat.comp_apply, C.d_comp_d]
  rfl

/-- A contracting homotopy gives `x = h (d x) + d (h x)`.-/
theorem _root_.DG.homotopy_apply_eq_of_id_zero (h : Homotopy (𝟙 C) 0) (n : ℤ) (x : C.X n) :
    x = (h.hom (n + 1) n).hom ((C.d n (n + 1)).hom x) +
      (C.d (n - 1) n).hom ((h.hom n (n - 1)).hom x) := by
  have e := h.comm n
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (n - 1) n by simp),
    HomologicalComplex.zero_f, add_zero, HomologicalComplex.id_f] at e
  have e' := congrArg (fun f => f.hom x) e
  simpa using e'

theorem _root_.DG.homotopy_d_apply_eq_of_id_zero (h : Homotopy (𝟙 C) 0) (n : ℤ) (x : C.X n)
    (hx : (C.d n (n + 1)).hom x = 0) : (C.d (n - 1) n).hom ((h.hom n (n - 1)).hom x) = x := by
  conv_rhs => rw [homotopy_apply_eq_of_id_zero h n x, hx, map_zero, zero_add]

/-- The cocycles `Zⁿ = ker dⁿ` of a cochain complex of modules, as a module.-/
abbrev _root_.DG.cyclesModule (C : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.ker (C.d n (n + 1)).hom)

/-- The cocycles of a contractible complex of finitely generated projective modules are finitely
generated projective: `x ↦ d (h x)` is a retraction of `Zⁿ ⊆ Cⁿ`.-/
theorem _root_.DG.fgProjective_cyclesModule (h : Homotopy (𝟙 C) 0)
    (hC : ∀ n, IsFGProjective R (C.X n)) (n : ℤ) : IsFGProjective R (cyclesModule C n) :=
  IsFGProjective.of_retract (ModuleCat.ofHom (Submodule.subtype _))
    (ModuleCat.ofHom (LinearMap.codRestrict _ (h.hom n (n - 1) ≫ C.d (n - 1) n).hom
      fun x => by
        rw [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply]
        exact d_apply_d_apply _ _ _ _))
    (by
      ext x
      simpa using homotopy_d_apply_eq_of_id_zero h n x.1 x.2)
    (hC n)

/-- For a contractible complex, `0 ⟶ Zⁿ ⟶ Cⁿ ⟶ Zⁿ⁺¹ ⟶ 0` (the second map induced by `d`) is
exact.-/
theorem _root_.DG.shortExact_cyclesModule (h : Homotopy (𝟙 C) 0) (n : ℤ) : (ShortComplex.mk
    (ModuleCat.ofHom (Submodule.subtype (LinearMap.ker (C.d n (n + 1)).hom)))
    (ModuleCat.ofHom (LinearMap.codRestrict (LinearMap.ker (C.d (n + 1) (n + 1 + 1)).hom)
      (C.d n (n + 1)).hom fun x => LinearMap.mem_ker.mpr (d_apply_d_apply _ _ _ x))) (by
        ext x
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
          ModuleCat.hom_zero, LinearMap.zero_apply, Submodule.coe_subtype]
        exact (LinearMap.mem_ker.mp x.2))).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ (Submodule.injective_subtype _) ?_
  · intro x
    constructor
    · intro hx
      exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext (LinearMap.mem_ker.mp y.2)
  · intro y
    refine ⟨(h.hom (n + 1) n).hom y, Subtype.ext ?_⟩
    have := homotopy_d_apply_eq_of_id_zero h (n + 1) y.1 y.2
    obtain ⟨m, hm⟩ : ∃ m, m = n + 1 - 1 := ⟨_, rfl⟩
    rw [← hm] at this
    obtain rfl : m = n := by omega
    exact this

theorem _root_.DG.isZero_cyclesModule_of_isZero {n : ℤ} (hn : IsZero (C.X n)) :
    IsZero (cyclesModule C n) := by
  have := ModuleCat.subsingleton_of_isZero hn
  have : Subsingleton (LinearMap.ker (C.d n (n + 1)).hom) :=
    ⟨fun x y => Subtype.ext (Subsingleton.elim (x : C.X n) y)⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem _root_.DG.isZero_cyclesModule_of_homotopy (h : Homotopy (𝟙 C) 0) {n : ℤ}
    (hn : IsZero (C.X (n - 1))) : IsZero (cyclesModule C n) := by
  have := ModuleCat.subsingleton_of_isZero hn
  have : Subsingleton (LinearMap.ker (C.d n (n + 1)).hom) := ⟨fun x y => Subtype.ext (by
    rw [← homotopy_d_apply_eq_of_id_zero h n x.1 x.2,
      ← homotopy_d_apply_eq_of_id_zero h n y.1 y.2,
      Subsingleton.elim ((h.hom n (n - 1)).hom x.1) ((h.hom n (n - 1)).hom y.1)])⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The Euler characteristic of a contractible perfect complex vanishes: with `Zⁿ = ker dⁿ`,
`[Cⁿ] = [Zⁿ] + [Zⁿ⁺¹]` and the alternating sum telescopes.
@isnad1 id=eq.1h3v.s9.3cd855f2b032 from=translated src=- shape=e8cb169e vocab=6d68270d
-/
theorem eulerChar_eq_zero_of_homotopy (hC : IsPerfectComplex C) (h : Homotopy (𝟙 C) 0) :
    hC.eulerChar = 0 := by
  obtain ⟨a, m, hm⟩ := hC.exists_bounds
  let z : ℤ → ProjK0.{u} R := fun n =>
    ProjK0.mk (cyclesModule C n) (fgProjective_cyclesModule h hC.fgProjective n)
  have hz : ∀ n n', n = n' → z n = z n' := by
    rintro n _ rfl
    rfl
  have hx : ∀ n, ProjK0.mk (C.X n) (hC.fgProjective n) = z n + z (n + 1) := fun n =>
    ProjK0.mk_X₂ (shortExact_cyclesModule h n) (fgProjective_cyclesModule h hC.fgProjective n)
      (hC.fgProjective n) (fgProjective_cyclesModule h hC.fgProjective (n + 1))
  have ht := AbelianK0.sum_range_negOnePow_telescope
    (fun n => ProjK0.mk (C.X n) (hC.fgProjective n)) (fun _ => 0) (fun n => z (n + 1))
    (fun n => by rw [hx, zero_add, hz (n - 1 + 1) n (by omega)]) a m
  rw [hC.eulerChar_eq_sum_range a m hm, ht]
  simp only [smul_zero, Finset.sum_const_zero, zero_add]
  rw [hz (a - 1 + 1) a (by omega), hz (a + m - 1 + 1) (a + m) (by omega)]
  simp only [z]
  rw [ProjK0.mk_eq_zero_of_isZero (isZero_cyclesModule_of_homotopy h (hm _ (by omega))),
    ProjK0.mk_eq_zero_of_isZero (isZero_cyclesModule_of_isZero (hm _ (by omega))),
    smul_zero, smul_zero, sub_zero]

end Contractible

/-! ### Perfect complexes in the derived category -/

section Derived

variable [_root_.HasDerivedCategory.{w} (ModuleCat.{u} R)]
  {K L : CochainComplex (ModuleCat.{u} R) ℤ}

omit [_root_.HasDerivedCategory (ModuleCat R)] in
/-- A perfect complex is K-projective (a bounded above complex of projectives).
@isnad1 id=iskproje.1h2v.s5.826b3b4dd310 from=translated src=- shape=7b1ebee6 vocab=40901e2c
-/
theorem isKProjective (hK : IsPerfectComplex K) : K.IsKProjective := by
  obtain ⟨a, b, _, _⟩ := hK.bounded
  have : ∀ n, Projective (K.X n) := fun n =>
    (IsProjective.iff_projective (K.X n)).1 (hK.fgProjective n).2
  exact CochainComplex.isKProjective_of_projective K b

/-- Morphisms in the derived category out of a perfect complex are induced by morphisms of
complexes.
@isnad1 id=ex.1h4v.s10.2f7c87082c5c from=translated src=- shape=6a22f51b vocab=b3e3c1b6
-/
theorem exists_Q_map_eq (hK : IsPerfectComplex K)
    (f : _root_.DerivedCategory.Q.obj K ⟶ _root_.DerivedCategory.Q.obj L) :
    ∃ g : K ⟶ L, _root_.DerivedCategory.Q.map g = f := by
  have := hK.isKProjective
  obtain ⟨g₀, hg₀⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient _ _).obj L)).2
      ((_root_.DerivedCategory.quotientCompQhIso _).hom.app K ≫ f ≫
        (_root_.DerivedCategory.quotientCompQhIso _).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g₀
  refine ⟨g, ?_⟩
  have h := _root_.DerivedCategory.quotientCompQhIso_hom_naturality g
  rw [hg₀] at h
  simpa using h.symm

/-- Two morphisms out of a perfect complex which agree in the derived category are
homotopic.
@isnad1 id=nonempty.2h5v.s9.fbdaef1cd013 from=translated src=- shape=acca686e vocab=c429cbea
-/
theorem nonempty_homotopy_of_Q_map_eq (hK : IsPerfectComplex K) {g₁ g₂ : K ⟶ L}
    (h : _root_.DerivedCategory.Q.map g₁ = _root_.DerivedCategory.Q.map g₂) :
    Nonempty (Homotopy g₁ g₂) := by
  have := hK.isKProjective
  have h' : _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g₁) =
      _root_.DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map g₂) := by
    rw [← cancel_mono ((_root_.DerivedCategory.quotientCompQhIso _).hom.app L),
      _root_.DerivedCategory.quotientCompQhIso_hom_naturality,
      _root_.DerivedCategory.quotientCompQhIso_hom_naturality, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _
    ((CochainComplex.IsKProjective.Qh_map_bijective K _).1 h')⟩

/-- **Invariance of the Euler characteristic**: perfect complexes which are isomorphic in the
derived category have the same Euler characteristic. A morphism `g : K ⟶ L` inducing the
isomorphism is a quasi-isomorphism, so its mapping cone is acyclic and K-projective, hence
contractible, and `χ(L) - χ(K) = χ(C(g)) = 0`.
@isnad1 id=eq.2h4v.s8.d4b94fb05d59 from=translated src=- shape=f1d76a04 vocab=ce42b265
-/
theorem eulerChar_eq_of_iso_Q (hK : IsPerfectComplex K) (hL : IsPerfectComplex L)
    (e : _root_.DerivedCategory.Q.obj K ≅ _root_.DerivedCategory.Q.obj L) :
    hK.eulerChar = hL.eulerChar := by
  obtain ⟨g, hg⟩ := hK.exists_Q_map_eq e.hom
  have hT := _root_.DerivedCategory.mappingCone_triangle_distinguished g
  have hZ : IsZero (_root_.DerivedCategory.Q.obj (CochainComplex.mappingCone g)) :=
    (Triangle.isZero₃_iff_isIso₁ _ hT).2 (by
      change IsIso (_root_.DerivedCategory.Q.map g)
      rw [hg]
      infer_instance)
  have hC := hK.mappingCone g hL
  obtain ⟨H⟩ := hC.nonempty_homotopy_of_Q_map_eq (g₁ := 𝟙 _) (g₂ := 0) (hZ.eq_of_src _ _)
  have h := hC.eulerChar_eq_zero_of_homotopy H
  rw [hK.eulerChar_mappingCone g hL, sub_eq_zero] at h
  exact h.symm

end Derived

end IsPerfectComplex

/-! ### Perfect objects of the derived category -/

section Perfect

variable (R) [_root_.HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- The *perfect* objects of the derived category of `R`-modules: those isomorphic to (the image
of) a perfect complex, i.e. a strictly bounded complex of finitely generated projective
modules.-/
def IsPerfect : ObjectProperty (_root_.DerivedCategory (ModuleCat.{u} R)) :=
  fun X => ∃ (K : CochainComplex (ModuleCat.{u} R) ℤ) (_ : IsPerfectComplex K),
    Nonempty (_root_.DerivedCategory.Q.obj K ≅ X)

variable {R}

namespace IsPerfect

/--
@isnad1 id=isperfec.0h5v.s6.1bce80f55150 from=translated src=- shape=b6c706ea vocab=7878af37
-/
theorem of_iso {X Y : _root_.DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y)
    (hY : IsPerfect R Y) : IsPerfect R X := by
  obtain ⟨K, hK, ⟨e'⟩⟩ := hY
  exact ⟨K, hK, ⟨e' ≪≫ e.symm⟩⟩

/--
@isnad1 id=isperfec.1h2v.s7.9e02a9b95cac from=translated src=- shape=a5092004 vocab=780bfee7
-/
theorem Q_obj {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsPerfectComplex K) :
    IsPerfect R (_root_.DerivedCategory.Q.obj K) :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

/--
@isnad1 id=isperfec.1h2v.s5.ee18fcc75408 from=translated src=- shape=41c74b30 vocab=f60e74f7
-/
theorem of_isZero {X : _root_.DerivedCategory (ModuleCat.{u} R)} (hX : IsZero X) :
    IsPerfect R X :=
  ⟨0, IsPerfectComplex.zero, ⟨(_root_.DerivedCategory.Q.map_isZero (isZero_zero _)).iso hX⟩⟩

/--
@isnad1 id=isperfec.0h4v.s6.bfd14dc0307d from=translated src=- shape=9340c496 vocab=7872cbe3
-/
theorem shift {X : _root_.DerivedCategory (ModuleCat.{u} R)} (hX : IsPerfect R X) (n : ℤ) :
    IsPerfect R (X⟦n⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hX
  exact ⟨K⟦n⟧, hK.shift n,
    ⟨(_root_.DerivedCategory.Q.commShiftIso n).app K ≪≫ (shiftFunctor _ n).mapIso e⟩⟩

/-- In a distinguished triangle whose first two objects are represented by perfect complexes `K`
and `L`, the morphism is induced by a morphism of complexes `g : K ⟶ L` and the third object is
isomorphic to the mapping cone of `g`.
@isnad1 id=ex.2h6v.s10.b9698ce62efa from=translated src=- shape=aa8ee899 vocab=f2c8511a
-/
theorem exists_iso_mappingCone (T : Triangle (_root_.DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsPerfectComplex K)
    (e₁ : _root_.DerivedCategory.Q.obj K ≅ T.obj₁)
    (e₂ : _root_.DerivedCategory.Q.obj L ≅ T.obj₂) :
    ∃ g : K ⟶ L, Nonempty
      (_root_.DerivedCategory.Q.obj (CochainComplex.mappingCone g) ≅ T.obj₃) := by
  obtain ⟨g, hg⟩ := hK.exists_Q_map_eq (e₁.hom ≫ T.mor₁ ≫ e₂.inv)
  refine ⟨g, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
    (_root_.DerivedCategory.mappingCone_triangle_distinguished g) hT e₁ e₂ ?_)⟩⟩
  change _root_.DerivedCategory.Q.map g ≫ e₂.hom = e₁.hom ≫ T.mor₁
  rw [hg]
  simp

/-- The third object of a distinguished triangle whose first two objects are perfect is
perfect.
@isnad1 id=isperfec.1h4v.s8.337379e4d5dc from=translated src=- shape=68ed80f5 vocab=7d136bec
-/
theorem ext₃ (T : Triangle (_root_.DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : IsPerfect R T.obj₁) (h₂ : IsPerfect R T.obj₂) : IsPerfect R T.obj₃ := by
  obtain ⟨K, hK, ⟨e₁⟩⟩ := h₁
  obtain ⟨L, hL, ⟨e₂⟩⟩ := h₂
  obtain ⟨g, ⟨e⟩⟩ := exists_iso_mappingCone T hT hK e₁ e₂
  exact ⟨_, hK.mappingCone g hL, ⟨e⟩⟩

/-- The middle object of a distinguished triangle whose outer objects are perfect is perfect.
@isnad1 id=isperfec.1h4v.s8.762c25e55685 from=translated src=- shape=68ed80f5 vocab=7d136bec
-/
theorem ext₂ (T : Triangle (_root_.DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    (h₁ : IsPerfect R T.obj₁) (h₃ : IsPerfect R T.obj₃) : IsPerfect R T.obj₂ :=
  ext₃ _ (inv_rot_of_distTriang _ hT) (h₃.shift _) h₁

end IsPerfect

end Perfect

end DG
