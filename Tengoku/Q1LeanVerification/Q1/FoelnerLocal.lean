import Tengoku.Q1LeanVerification.Q1.FoelnerGrowth
import Tengoku.Seed.Algebra.Group.Subgroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Transport of finite Følner sets and finite witnesses in subgroup closures.
Only the explicit finite-set predicate is used. No invariant-mean or radical
permanence theorem is postulated. -/

namespace Q1

variable {G H : Type*} [Group G] [Group H]

/--
@isnad1 id=eq.0h5v.s7.2ea0068010aa from=translated src=- shape=56160126 vocab=9051a29d
-/
theorem leftTranslate_image_hom [DecidableEq G] (φ : H →* G) (g : H) (F : Finset H) :
    leftTranslate (φ g) (F.image φ) = (leftTranslate g F).image φ := by
  classical
  ext y
  simp only [leftTranslate, Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨t, ht, rfl⟩, hz⟩
    exact ⟨g * t, ⟨t, ht, rfl⟩, by simpa only [map_mul] using hz⟩
  · rintro ⟨z, ⟨t, ht, rfl⟩, hz⟩
    exact ⟨φ t, ⟨t, ht, rfl⟩, by simpa only [map_mul] using hz⟩

/--
@isnad1 id=eq.1h5v.s8.93504d470959 from=translated src=- shape=27ae448b vocab=5aa5330e
-/
theorem translateBoundary_image_hom [DecidableEq G] (φ : H →* G) (hinj : Function.Injective φ)
    (g : H) (F : Finset H) :
    translateBoundary (φ g) (F.image φ) = (translateBoundary g F).image φ := by
  classical
  unfold translateBoundary
  rw [leftTranslate_image_hom, Finset.image_sdiff _ _ hinj]
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_image]

/-- Finite Følner sets in an injectively embedded group handle every finite
collection of translations contained in its image.
@isnad1 id=ex.4h5v.s7.7b8780f861dc from=translated src=- shape=7dc33778 vocab=6a4e506c
-/
theorem foelner_set_of_injective_hom (φ : H →* G) (hinj : Function.Injective φ)
    (hH : FiniteFoelner H) (K : Finset G) (hK : ∀ g ∈ K, g ∈ Set.range φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset G, F.Nonempty ∧
      ∀ g ∈ K, ((translateBoundary g F).card : ℝ) ≤ ε * F.card := by
  classical
  let lift : {g // g ∈ K} → H := fun g => Classical.choose (hK g.val g.property)
  have hlift : ∀ g : {g // g ∈ K}, φ (lift g) = g.val :=
    fun g => Classical.choose_spec (hK g.val g.property)
  let K' : Finset H := K.attach.image lift
  obtain ⟨F, hF, hbound⟩ := hH K' ε hε
  refine ⟨F.image φ, hF.image _, ?_⟩
  intro g hg
  let g' : {g // g ∈ K} := ⟨g, hg⟩
  have hg' : lift g' ∈ K' := Finset.mem_image.mpr ⟨g', Finset.mem_attach _ _, rfl⟩
  have hh := hbound (lift g') hg'
  have he : φ (lift g') = g := hlift g'
  rw [← he, translateBoundary_image_hom φ hinj,
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj]
  exact hh

/-- Local amenability expressed using the explicit finite Følner condition.
@isnad1 id=finitefo.1h1v.s6.c00402b16f56 from=translated src=- shape=06e69ca1 vocab=b93f7b89
-/
theorem finiteFoelner_of_locally (hloc : ∀ K : Finset G,
    ∃ A : Subgroup G, (∀ g ∈ K, g ∈ A) ∧ FiniteFoelner A) : FiniteFoelner G := by
  intro K ε hε
  obtain ⟨A, hK, hA⟩ := hloc K
  apply foelner_set_of_injective_hom A.subtype Subtype.val_injective hA K _ ε hε
  intro g hg
  exact ⟨⟨g, hK g hg⟩, rfl⟩

/-- Finite groups satisfy the explicit finite Følner condition.
@isnad1 id=finitefo.0h1v.s3.df3e9d234405 from=translated src=- shape=c612a321 vocab=2fffce8a
-/
theorem finiteFoelner_of_finite [Finite G] : FiniteFoelner G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro K ε hε
  refine ⟨Finset.univ, Finset.univ_nonempty, ?_⟩
  intro g hg
  have he : translateBoundary g Finset.univ = ∅ := by
    simp [translateBoundary]
  rw [he, Finset.card_empty, Nat.cast_zero]
  positivity

/-- Every element of a generated subgroup uses only finitely many generators.
@isnad1 id=ex.1h3v.s6.597657e123bd from=translated src=- shape=071d3e08 vocab=6a615f79
-/
theorem exists_finset_of_mem_closure (S : Set G) (x : G) (hx : x ∈ Subgroup.closure S) :
    ∃ P : Finset G, (↑P : Set G) ⊆ S ∧ x ∈ Subgroup.closure (↑P : Set G) := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    exact ⟨{x}, by simpa using hx, Subgroup.subset_closure (by simp)⟩
  | one => exact ⟨∅, by simp, Subgroup.one_mem _⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨P, hP, hxP⟩ := ihx
    obtain ⟨Q, hQ, hyQ⟩ := ihy
    refine ⟨P ∪ Q, ?_, ?_⟩
    · simpa only [Finset.coe_union, Set.union_subset_iff] using And.intro hP hQ
    · exact Subgroup.mul_mem _
        (Subgroup.closure_mono (by exact_mod_cast Finset.subset_union_left) hxP)
        (Subgroup.closure_mono (by exact_mod_cast Finset.subset_union_right) hyQ)
  | inv x hx ih =>
    obtain ⟨P, hP, hxP⟩ := ih
    exact ⟨P, hP, Subgroup.inv_mem _ hxP⟩

/-- A finite collection in a generated subgroup lies in one finite generated stage.
@isnad1 id=ex.1h3v.s6.316d10beb16c from=translated src=- shape=db1f5fe0 vocab=6a615f79
-/
theorem exists_finset_stage (S : Set G) (K : Finset G)
    (hK : ∀ x ∈ K, x ∈ Subgroup.closure S) :
    ∃ P : Finset G, (↑P : Set G) ⊆ S ∧
      ∀ x ∈ K, x ∈ Subgroup.closure (↑P : Set G) := by
  classical
  induction K using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert x K hx ih =>
    obtain ⟨P, hP, hxP⟩ := exists_finset_of_mem_closure S x (hK x (by simp))
    obtain ⟨Q, hQ, hKQ⟩ := ih (fun y hy => hK y (by simp [hy]))
    refine ⟨P ∪ Q, ?_, ?_⟩
    · simpa only [Finset.coe_union, Set.union_subset_iff] using And.intro hP hQ
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Subgroup.closure_mono (by exact_mod_cast Finset.subset_union_left) hxP
      · exact Subgroup.closure_mono (by exact_mod_cast Finset.subset_union_right) (hKQ y hy)

/-- If every finite stage is Følner, its full subgroup closure is Følner.
@isnad1 id=finitefo.1h2v.s6.ca3c24cb7be5 from=translated src=- shape=3d64ff95 vocab=376a1695
-/
theorem finiteFoelner_closure_of_finite_stages (S : Set G)
    (hstage : ∀ P : Finset G, (↑P : Set G) ⊆ S →
      FiniteFoelner (Subgroup.closure (↑P : Set G))) :
    FiniteFoelner (Subgroup.closure S) := by
  classical
  intro K ε hε
  let N := Subgroup.closure S
  obtain ⟨P, hP, hKP⟩ := exists_finset_stage S (K.image N.subtype) (by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact y.property)
  let A := Subgroup.closure (↑P : Set G)
  have hAN : A ≤ N := Subgroup.closure_mono hP
  let φ : A →* N := Subgroup.inclusion hAN
  apply foelner_set_of_injective_hom φ _ (hstage P hP) K _ ε hε
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) hab
  · intro x hx
    refine ⟨⟨x.val, hKP x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩, ?_⟩
    rfl

/-- A non-Følner subgroup closure has a finite non-Følner generated stage.
@isnad1 id=ex.1h2v.s6.4cec896e5bef from=translated src=- shape=aba61ee3 vocab=376a1695
-/
theorem exists_not_finiteFoelner_finset_stage (S : Set G)
    (hnot : ¬ FiniteFoelner (Subgroup.closure S)) :
    ∃ P : Finset G, (↑P : Set G) ⊆ S ∧
      ¬ FiniteFoelner (Subgroup.closure (↑P : Set G)) := by
  classical
  by_contra h
  push Not at h
  exact hnot (finiteFoelner_closure_of_finite_stages S h)

/-- Specialization to the actual normal closure: generators are conjugates
of elements of the original set.
@isnad1 id=ex.1h2v.s6.a29ef80ea708 from=translated src=- shape=a7333475 vocab=ffd6b10e
-/
theorem exists_not_finiteFoelner_normalClosure_stage (S : Set G)
    (hnot : ¬ FiniteFoelner (Subgroup.normalClosure S)) :
    ∃ P : Finset G, (↑P : Set G) ⊆ Group.conjugatesOfSet S ∧
      ¬ FiniteFoelner (Subgroup.closure (↑P : Set G)) :=
  exists_not_finiteFoelner_finset_stage (Group.conjugatesOfSet S) hnot

/-- A non-Følner closure has a nonempty finite stage; the empty stage is finite.
@isnad1 id=ex.1h2v.s6.ed5cba1176c7 from=translated src=- shape=9df1763a vocab=7b7eef16
-/
theorem exists_nonempty_not_finiteFoelner_finset_stage (S : Set G)
    (hnot : ¬ FiniteFoelner (Subgroup.closure S)) :
    ∃ P : Finset G, P.Nonempty ∧ (↑P : Set G) ⊆ S ∧
      ¬ FiniteFoelner (Subgroup.closure (↑P : Set G)) := by
  classical
  obtain ⟨P, hP, hbad⟩ := exists_not_finiteFoelner_finset_stage S hnot
  refine ⟨P, ?_, hP, hbad⟩
  by_contra he
  have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  subst P
  apply hbad
  have he : Subgroup.closure (↑(∅ : Finset G) : Set G) = ⊥ := by simp
  rw [he]
  exact finiteFoelner_of_finite

end Q1
