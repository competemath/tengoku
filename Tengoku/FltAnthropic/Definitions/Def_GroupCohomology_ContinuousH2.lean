import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

def IsLevelConstant₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

def IsLevelConstant₂ {X : Type*} (f : G × G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ g g' s s' : G, r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup →
      f (g * s, g' * s') = f (g, g')

variable {r} in
/--
@isnad1 id=islevelc.2h5v.s8.c0dd3d832001 from=translated src=- shape=a294d8f6 vocab=ab24b4ee
-/
lemma IsLevelConstant₁.add {X : Type*} [Add X] {f f' : G → X}
    (hf : IsLevelConstant₁ r f) (hf' : IsLevelConstant₁ r f') : IsLevelConstant₁ r (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

variable {r} in
/--
@isnad1 id=islevelc.2h5v.s8.54db9344693b from=translated src=- shape=7ef913c1 vocab=6d7c0771
-/
lemma IsLevelConstant₂.add {X : Type*} [Add X] {f f' : G × G → X}
    (hf : IsLevelConstant₂ r f) (hf' : IsLevelConstant₂ r f') : IsLevelConstant₂ r (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g g' s s' hs hs' => ?_⟩
  simp only [Pi.add_apply]
  rw [h g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_left hs'),
    h' g g' s s' (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
      (IntermediateField.fixingSubgroup_antitone le_sup_right hs')]

/--
@isnad1 id=islevelc.0h4v.s8.851a955574a4 from=translated src=- shape=2113a4d7 vocab=44a5a78c
-/
lemma isLevelConstant₁_const {X : Type*} (x : X) : IsLevelConstant₁ r (fun _ : G => x) :=
  ⟨⊥, inferInstance, fun _ _ _ => rfl⟩

/--
@isnad1 id=islevelc.0h4v.s8.477b0ced3645 from=translated src=- shape=640b863f vocab=1103fc67
-/
lemma isLevelConstant₂_const {X : Type*} (x : X) : IsLevelConstant₂ r (fun _ : G × G => x) :=
  ⟨⊥, inferInstance, fun _ _ _ _ _ _ => rfl⟩

variable {r} in
/--
@isnad1 id=islevelc.1h6v.s8.eb276959cb61 from=translated src=- shape=eafea8e8 vocab=b6ce379f
-/
lemma IsLevelConstant₁.comp {X Y : Type*} {f : G → X} (hf : IsLevelConstant₁ r f) (φ : X → Y) :
    IsLevelConstant₁ r (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable {r} in
/--
@isnad1 id=islevelc.1h6v.s8.537685766ab1 from=translated src=- shape=65d0fc13 vocab=2d5a986c
-/
lemma IsLevelConstant₂.comp {X Y : Type*} {f : G × G → X} (hf : IsLevelConstant₂ r f) (φ : X → Y) :
    IsLevelConstant₂ r (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g g' s s' hs hs' => by simp only [Function.comp_apply, h g g' s s' hs hs']⟩

variable (M : Rep k G)

def levelCochains₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstant₁ r f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstant₁_const r (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

def levelCochains₂ : Submodule k (G × G → M) where
  carrier := {f | IsLevelConstant₂ r f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstant₂_const r (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

/--
@isnad1 id=iff.0h5v.s9.d53b109bd333 from=translated src=- shape=fc55fa61 vocab=444be5f6
-/
lemma mem_levelCochains₁_iff (f : G → M) : f ∈ levelCochains₁ r M ↔ IsLevelConstant₁ r f :=
  Iff.rfl

def levelCocycles₂ : Submodule k (G × G → M) :=
  cocycles₂ M ⊓ levelCochains₂ r M

/--
@isnad1 id=iff.0h5v.s10.fc4fd0dcaf6f from=translated src=- shape=4ac43f45 vocab=9ab3b7b4
-/
lemma mem_levelCocycles₂_iff (f : G × G → M) :
    f ∈ levelCocycles₂ r M ↔ f ∈ cocycles₂ M ∧ IsLevelConstant₂ r f :=
  Iff.rfl

def levelCoboundaries₂ : Submodule k (G × G → M) :=
  (levelCochains₁ r M).map (d₁₂ M).hom

/--
@isnad1 id=iff.0h5v.s11.32b1788bf1bf from=translated src=- shape=3981f24a vocab=afbef711
-/
lemma mem_levelCoboundaries₂_iff (f : G × G → M) :
    f ∈ levelCoboundaries₂ r M ↔ ∃ x : G → M, IsLevelConstant₁ r x ∧ (d₁₂ M).hom x = f := by
  simp only [levelCoboundaries₂, Submodule.mem_map, mem_levelCochains₁_iff]

/--
@isnad1 id=le.0h4v.s9.3473d2d080cb from=translated src=- shape=89d52325 vocab=f1cb35d9
-/
lemma levelCoboundaries₂_le_coboundaries₂ : levelCoboundaries₂ r M ≤ coboundaries₂ M :=
  fun _ ⟨x, _, hx⟩ => ⟨x, hx⟩

/--
@isnad1 id=le.0h4v.s9.6ef6e67ec64f from=translated src=- shape=89d52325 vocab=4cbefb5a
-/
lemma levelCoboundaries₂_le_cocycles₂ : levelCoboundaries₂ r M ≤ cocycles₂ M :=
  (levelCoboundaries₂_le_coboundaries₂ r M).trans (coboundaries₂_le_cocycles₂ M)

abbrev continuousH2 : Type u :=
  ↥(levelCocycles₂ r M) ⧸ (levelCoboundaries₂ r M).comap (levelCocycles₂ r M).subtype

abbrev continuousH2π : ↥(levelCocycles₂ r M) →ₗ[k] continuousH2 r M :=
  Submodule.mkQ _

/--
@isnad1 id=iff.0h5v.s13.f8011caa26a7 from=translated src=- shape=92b1268d vocab=d75309db
-/
lemma continuousH2π_eq_zero_iff (f : ↥(levelCocycles₂ r M)) :
    continuousH2π r M f = 0 ↔ (f : G × G → M) ∈ levelCoboundaries₂ r M := by
  simp [continuousH2π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]

def levelCocyclesToCocycles₂ : ↥(levelCocycles₂ r M) →ₗ[k] ↥(cocycles₂ M) where
  toFun c := ⟨(c : G × G → M), c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def continuousH2ToH2 : continuousH2 r M →ₗ[k] H2 M :=
  Submodule.liftQ _ ((H2π M).hom ∘ₗ levelCocyclesToCocycles₂ r M)
    (fun c hc => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact (H2π_eq_zero_iff _).2 (levelCoboundaries₂_le_coboundaries₂ r M hc))

/--
@isnad1 id=eq.0h5v.s14.0ff40349811f from=translated src=- shape=4121f6ce vocab=4d9716f5
-/
@[simp]
lemma continuousH2ToH2_mk (c : ↥(levelCocycles₂ r M)) :
    continuousH2ToH2 r M (Submodule.Quotient.mk c) = H2π M (levelCocyclesToCocycles₂ r M c) :=
  rfl

end groupCohomology
