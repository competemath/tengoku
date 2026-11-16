import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_ContinuousUnramified

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace groupCohomology

universe u

variable {G : Type u} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

def IsLevelConstantSr₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstantSr₂ {X : Type*} (f : G × G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
    ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g')

variable {r S}

/--
@isnad1 id=islevelc.1h5v.s8.c20bd9bc88fd from=translated src=- shape=123305cd vocab=76cd8188
-/
lemma IsLevelConstantSr₁.isLevelConstant₁ {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : IsLevelConstant₁ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩

/--
@isnad1 id=islevelc.1h5v.s8.a4227bcfcbf4 from=translated src=- shape=4a4df825 vocab=7a07015a
-/
lemma IsLevelConstantSr₂.isLevelConstant₂ {X : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) : IsLevelConstant₂ r f := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF.1, h⟩

/--
@isnad1 id=islevelc.2h6v.s8.3ce20d84954b from=translated src=- shape=6593fea8 vocab=e8848169
-/
lemma IsLevelConstantSr₁.add {X : Type*} [Add X] {f f' : G → X} (hf : IsLevelConstantSr₁ r S f) (hf' : IsLevelConstantSr₁ r S f') :
    IsLevelConstantSr₁ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

/--
@isnad1 id=islevelc.2h6v.s8.9a5bca89e9d3 from=translated src=- shape=1c200db3 vocab=31451c76
-/
lemma IsLevelConstantSr₂.add {X : Type*} [Add X] {f f' : G × G → X} (hf : IsLevelConstantSr₂ r S f)
    (hf' : IsLevelConstantSr₂ r S f') : IsLevelConstantSr₂ r S (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  refine ⟨F ⊔ F', hF.sup hF', fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

variable (r S) in
/--
@isnad1 id=islevelc.0h5v.s8.c8d60cd00e1c from=translated src=- shape=f37f5ea7 vocab=9358b856
-/
lemma isLevelConstantSr₁_const {X : Type*} (x : X) : IsLevelConstantSr₁ r S (fun _ : G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ => rfl⟩

variable (r S) in
/--
@isnad1 id=islevelc.0h5v.s8.763fd0c079c4 from=translated src=- shape=d90c9fe8 vocab=6de49755
-/
lemma isLevelConstantSr₂_const {X : Type*} (x : X) : IsLevelConstantSr₂ r S (fun _ : G × G => x) :=
  ⟨⊥, IntermediateField.isUnramifiedOutside_bot S, fun _ _ _ _ _ _ => rfl⟩

/--
@isnad1 id=islevelc.1h7v.s8.3a08d0075e8b from=translated src=- shape=20f165df vocab=efc63c8c
-/
lemma IsLevelConstantSr₁.comp {X Y : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) (φ : X → Y) :
    IsLevelConstantSr₁ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

/--
@isnad1 id=islevelc.1h7v.s8.08684809ff49 from=translated src=- shape=28d0066c vocab=e6299b37
-/
lemma IsLevelConstantSr₂.comp {X Y : Type*} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) (φ : X → Y) :
    IsLevelConstantSr₂ r S (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

/--
@isnad1 id=islevelc.2h6v.s8.98458d4d1361 from=translated src=- shape=7f1dd8a9 vocab=7bfe554d
-/
lemma IsLevelConstantSr₁.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    IsLevelConstantSr₁ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

/--
@isnad1 id=islevelc.2h6v.s8.1d800e995150 from=translated src=- shape=c2f149f8 vocab=b56d565c
-/
lemma IsLevelConstantSr₂.mono {S' : Finset Nat.Primes} (h : S ⊆ S') {X : Type*} {f : G × G → X}
    (hf : IsLevelConstantSr₂ r S f) : IsLevelConstantSr₂ r S' f := by
  obtain ⟨F, hF, hc⟩ := hf
  exact ⟨F, hF.mono h, hc⟩

section carriers

variable (r S) {k : Type u} [CommRing k] (M : Rep k G)

def levelCochainsSr₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstantSr₁ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₁_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochainsSr₂ : Submodule k (G × G → M) where
  carrier := {f | IsLevelConstantSr₂ r S f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstantSr₂_const r S (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

/--
@isnad1 id=iff.0h6v.s9.93673c03397c from=translated src=- shape=62e4fdb5 vocab=2bc924d8
-/
lemma mem_levelCochainsSr₁_iff (f : G → M) : f ∈ levelCochainsSr₁ r S M ↔ IsLevelConstantSr₁ r S f := Iff.rfl

def levelCocyclesSr₁ : Submodule k (cocycles₁ M) :=
  (levelCochainsSr₁ r S M).comap (cocycles₁ M).subtype

/--
@isnad1 id=iff.0h6v.s12.78d6bf5acfac from=translated src=- shape=4a9f3031 vocab=533b7400
-/
lemma mem_levelCocyclesSr₁_iff (c : cocycles₁ M) : c ∈ levelCocyclesSr₁ r S M ↔ IsLevelConstantSr₁ r S c := Iff.rfl

def continuousH1Sr : Submodule k (H1 M) :=
  (levelCocyclesSr₁ r S M).map (H1π M).hom

/--
@isnad1 id=iff.0h6v.s13.658dff94a97d from=translated src=- shape=dd020fb2 vocab=6906b83e
-/
lemma mem_continuousH1Sr_iff (x : H1 M) :
    x ∈ continuousH1Sr r S M ↔ ∃ c : cocycles₁ M, IsLevelConstantSr₁ r S c ∧ (H1π M).hom c = x := by
  simp only [continuousH1Sr, Submodule.mem_map, mem_levelCocyclesSr₁_iff]

/--
@isnad1 id=mem.1h6v.s13.811fa621b35b from=translated src=- shape=b4abe644 vocab=6906b83e
-/
lemma H1π_mem_continuousH1Sr {c : cocycles₁ M} (hc : IsLevelConstantSr₁ r S c) : (H1π M).hom c ∈ continuousH1Sr r S M :=
  (mem_continuousH1Sr_iff r S M _).2 ⟨c, hc, rfl⟩

/--
@isnad1 id=le.0h5v.s9.9051dc7c179a from=translated src=- shape=1d546511 vocab=c3ee1b56
-/
lemma continuousH1Sr_le_continuousH1 : continuousH1Sr r S M ≤ continuousH1 r M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact H1π_mem_continuousH1 r M hc.isLevelConstant₁

variable {S} in

/--
@isnad1 id=le.1h6v.s9.db08fb0841b1 from=translated src=- shape=a706cb43 vocab=d69b317e
-/
lemma continuousH1Sr_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH1Sr r S M ≤ continuousH1Sr r S' M := by
  rintro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1Sr_iff r S M x).1 hx
  exact (mem_continuousH1Sr_iff r S' M _).2 ⟨c, hc.mono h, rfl⟩

def levelCocyclesSr₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochainsSr₂ r S M

def levelCoboundariesSr₂ : Submodule k (G × G → M) :=
  (levelCochainsSr₁ r S M).map (d₁₂ M).hom

/--
@isnad1 id=iff.0h6v.s10.c645653fcb0f from=translated src=- shape=ba9d750b vocab=031eb7b4
-/
lemma mem_levelCocyclesSr₂_iff (f : G × G → M) : f ∈ levelCocyclesSr₂ r S M ↔ f ∈ cocycles₂ M ∧ IsLevelConstantSr₂ r S f :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s11.31f9a007842f from=translated src=- shape=0108779e vocab=0244cdc2
-/
lemma mem_levelCoboundariesSr₂_iff (f : G × G → M) :
    f ∈ levelCoboundariesSr₂ r S M ↔ ∃ x : G → M, IsLevelConstantSr₁ r S x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundariesSr₂, Submodule.mem_map, mem_levelCochainsSr₁_iff]

/--
@isnad1 id=le.0h5v.s9.3e2450bbbf0f from=translated src=- shape=557142ee vocab=b27952e1
-/
lemma levelCocyclesSr₂_le_levelCocycles₂ : levelCocyclesSr₂ r S M ≤ levelCocycles₂ r M :=
  fun _ h => ⟨h.1, h.2.isLevelConstant₂⟩

/--
@isnad1 id=le.0h5v.s9.26445876aa43 from=translated src=- shape=557142ee vocab=d3b4d822
-/
lemma levelCoboundariesSr₂_le_levelCoboundaries₂ : levelCoboundariesSr₂ r S M ≤ levelCoboundaries₂ r M := by
  rintro f hf
  obtain ⟨x, hx, rfl⟩ := (mem_levelCoboundariesSr₂_iff r S M f).1 hf
  exact (mem_levelCoboundaries₂_iff r M _).2 ⟨x, hx.isLevelConstant₁, rfl⟩

variable {S} in
/--
@isnad1 id=le.1h6v.s9.3eb857361f99 from=translated src=- shape=97e23487 vocab=85ab391c
-/
lemma levelCocyclesSr₂_mono {S' : Finset Nat.Primes} (h : S ⊆ S') : levelCocyclesSr₂ r S M ≤ levelCocyclesSr₂ r S' M :=
  fun _ hf => ⟨hf.1, hf.2.mono h⟩

abbrev continuousH2Sr : Type u :=
  ↥(levelCocyclesSr₂ r S M) ⧸ (levelCoboundariesSr₂ r S M).comap (levelCocyclesSr₂ r S M).subtype

abbrev continuousH2Srπ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] continuousH2Sr r S M :=
  Submodule.mkQ _

/--
@isnad1 id=iff.0h6v.s13.60b29e6bf8f3 from=translated src=- shape=73543ceb vocab=53507e0a
-/
lemma continuousH2Srπ_eq_zero_iff (f : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2Srπ r S M f = 0 ↔ (f : G × G → M) ∈ levelCoboundariesSr₂ r S M := by
  simp [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

/--
@isnad1 id=surjecti.0h5v.s13.09179d07c76d from=translated src=- shape=085fc32f vocab=10d3886b
-/
lemma continuousH2Srπ_surjective : Function.Surjective (continuousH2Srπ r S M) :=
  Submodule.mkQ_surjective _

def levelCocyclesSr₂ToLevelCocycles₂ : ↥(levelCocyclesSr₂ r S M) →ₗ[k] ↥(levelCocycles₂ r M) :=
  Submodule.inclusion (levelCocyclesSr₂_le_levelCocycles₂ r S M)

def continuousH2SrToContinuousH2 : continuousH2Sr r S M →ₗ[k] continuousH2 r M :=
  Submodule.mapQ _ _ (levelCocyclesSr₂ToLevelCocycles₂ r S M) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    exact levelCoboundariesSr₂_le_levelCoboundaries₂ r S M hc)

/--
@isnad1 id=eq.0h6v.s15.b11f6c81e291 from=translated src=- shape=624ecf5d vocab=adace3b8
-/
lemma continuousH2SrToContinuousH2_mk (c : ↥(levelCocyclesSr₂ r S M)) :
    continuousH2SrToContinuousH2 r S M (continuousH2Srπ r S M c) = continuousH2π r M (levelCocyclesSr₂ToLevelCocycles₂ r S M c) := rfl

variable {S} in

def continuousH2SrOfLE {S' : Finset Nat.Primes} (h : S ⊆ S') : continuousH2Sr r S M →ₗ[k] continuousH2Sr r S' M :=
  Submodule.mapQ _ _ (Submodule.inclusion (levelCocyclesSr₂_mono r M h)) (fun c hc => by
    simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
    obtain ⟨x, hx, hxc⟩ := (mem_levelCoboundariesSr₂_iff r S M _).1 hc
    exact (mem_levelCoboundariesSr₂_iff r S' M _).2 ⟨x, hx.mono h, hxc⟩)

end carriers

end groupCohomology

end
