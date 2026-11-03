module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Picture.Split
public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Picture.EulerBound

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Components of combinatorial maps and the spherical split

* `numOrbits_subtypePerm_add` : orbits of a permutation are counted separately on an invariant
  subset and on its complement;
* `CombMap.restrict` : the submap on a set of darts invariant under `σ` and `α`, with
  `CombMap.euler_restrict_add` : `χ` is additive over an invariant set and its complement;
* `CombMap.component c`, `CombMap.componentCompl c` : the connected component of the dart `c`
  and the rest of the map; the component is connected (`component_connected`);
* `CombMap.split_sameFace_spherical` : **if `M` is connected with `χ(M) = 2` and `a ≠ b` are darts
  of the same vertex and of the same face, then the split map is disconnected, and it consists
  of exactly two components — the component of `a` and the component of `b` — each connected
  with `χ = 2`.**
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

/-- Orbits of a permutation are counted separately on an invariant set and its complement.
@isnad1 id=eq.1h3v.s6.29c5847294f5 from=translated src=- shape=949d34b4 vocab=cfb296b3
-/
theorem numOrbits_subtypePerm_add {D : Type*} [Finite D] (π : Perm D) (p : D → Prop)
    (h : ∀ x, p (π x) ↔ p x) :
    numOrbits π = numOrbits (π.subtypePerm h) +
      numOrbits (π.subtypePerm (p := fun x => ¬ p x) fun x => not_congr (h x)) := by
  classical
  rw [← numOrbits_sumCongr]
  have hinv : ∀ {x y}, π.SameCycle x y → (p x ↔ p y) := fun hxy =>
    (SameCycle.eq_of_invariant (f := p) (fun x => propext (h x)) hxy) ▸ Iff.rfl
  let g : D → {x // p x} ⊕ {x // ¬ p x} := fun x => if hx : p x then .inl ⟨x, hx⟩ else .inr ⟨x, hx⟩
  refine numOrbits_eq_of_iff π (fun x => (⟦g x⟧ : Quotient (Perm.SameCycle.setoid _))) ?_ ?_
  · rintro ⟨(⟨x, hx⟩ | ⟨x, hx⟩)⟩
    · exact ⟨x, by simp [g, hx]; rfl⟩
    · exact ⟨x, by simp [g, hx]; rfl⟩
  · intro x y
    rw [Quotient.eq]
    change (Perm.sumCongr _ _).SameCycle (g x) (g y) ↔ _
    by_cases hx : p x <;> by_cases hy : p y
    · simp only [g, dite_eq_left hx, dite_eq_left hy, sameCycle_sumCongr_inl, Perm.sameCycle_subtypePerm]
    · simp only [g, dite_eq_left hx, dite_eq_right hy]
      exact ⟨fun h => absurd h not_sameCycle_sumCongr_inl_inr,
        fun h => absurd ((hinv h).1 hx) hy⟩
    · simp only [g, dite_eq_right hx, dite_eq_left hy]
      exact ⟨fun h => absurd h not_sameCycle_sumCongr_inr_inl,
        fun h => absurd ((hinv h).2 hy) hx⟩
    · simp only [g, dite_eq_right hx, dite_eq_right hy, sameCycle_sumCongr_inr, Perm.sameCycle_subtypePerm]

namespace CombMap

variable (M : CombMap)

/-- The submap on a set of darts invariant under the rotation and the edge involution.-/
def restrict (p : M.D → Prop) [DecidablePred p] (hσ : ∀ x, p (M.σ x) ↔ p x)
    (hα : ∀ x, p (M.α x) ↔ p x) : CombMap where
  D := {x // p x}
  σ := M.σ.subtypePerm hσ
  α := M.α.subtypePerm hα
  α_α := fun d => Subtype.ext (M.α_α d)
  α_ne := fun d h => M.α_ne d (congrArg Subtype.val h)

variable {M} (p : M.D → Prop) [DecidablePred p]

omit [DecidablePred p] in
/--
@isnad1 id=iff.1h3v.s6.a89288b941aa from=translated src=- shape=3fbc206f vocab=9b99bdeb
-/
theorem not_invariant_σ (hσ : ∀ x, p (M.σ x) ↔ p x) : ∀ x, ¬ p (M.σ x) ↔ ¬ p x := fun x => not_congr (hσ x)

omit [DecidablePred p] in
/--
@isnad1 id=iff.1h3v.s6.78e5f2dff517 from=translated src=- shape=3fbc206f vocab=0060ac1c
-/
theorem not_invariant_α (hα : ∀ x, p (M.α x) ↔ p x) : ∀ x, ¬ p (M.α x) ↔ ¬ p x := fun x => not_congr (hα x)

omit [DecidablePred p] in
/--
@isnad1 id=iff.2h3v.s6.74199e8fc24c from=translated src=- shape=148ed881 vocab=cad90a21
-/
theorem invariant_φ (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : ∀ x, p (M.φ x) ↔ p x := fun x => (hσ _).trans (hα x)

/--
@isnad1 id=eq.2h2v.s6.4bdc4342d2b6 from=translated src=- shape=e9054ec4 vocab=8b0838ce
-/
theorem restrict_φ (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : (M.restrict p hσ hα).φ = M.φ.subtypePerm (invariant_φ p hσ hα) := by
  ext x; rfl

/-- **Additivity of `χ`** over an invariant set of darts and its complement.
@isnad1 id=eq.2h2v.s6.131740bb02ed from=translated src=- shape=59be5317 vocab=f1dabd68
-/
theorem euler_restrict_add (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) : M.euler = (M.restrict p hσ hα).euler +
    (M.restrict (fun x => ¬ p x) (not_invariant_σ p hσ) (not_invariant_α p hα)).euler := by
  have hV := numOrbits_subtypePerm_add M.σ p hσ
  have hE := numOrbits_subtypePerm_add M.α p hα
  have hF := numOrbits_subtypePerm_add M.φ p (invariant_φ p hσ hα)
  have hF1 := restrict_φ p hσ hα
  have hF2 := restrict_φ (fun x => ¬ p x) (not_invariant_σ p hσ) (not_invariant_α p hα)
  unfold euler numVertices numEdges numFaces
  rw [hF1, hF2]
  simp only [restrict] at *
  push_cast [hV, hE, hF]
  ring

omit [DecidablePred p] in
/-- Invariant sets are unions of components.
@isnad1 id=iff.3h4v.s6.c97d5f5e2313 from=translated src=- shape=0ebd9ef1 vocab=4e8424cd
-/
theorem invariant_of_eqvGen (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) {u v : M.D} (h : Relation.EqvGen M.Step u v) : p u ↔ p v := by
  induction h with
  | rel u v h => rcases h with rfl | rfl
                 · exact (hσ u).symm
                 · exact (hα u).symm
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A restriction whose darts are all connected (in `M`) to one of its darts is connected.
@isnad1 id=connecte.3h4v.s6.5e1ba0131b4b from=translated src=- shape=c125fa60 vocab=d79c7ac8
-/
theorem restrict_connected (hσ : ∀ x, p (M.σ x) ↔ p x) (hα : ∀ x, p (M.α x) ↔ p x) (c : M.D) (hc : p c)
    (hreach : ∀ x, p x → Relation.EqvGen M.Step c x) : (M.restrict p hσ hα).Connected := by
  have key : ∀ u v, Relation.EqvGen M.Step u v → ∀ (hu : p u) (hv : p v),
      Relation.EqvGen (M.restrict p hσ hα).Step ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v h
    induction h with
    | rel u v h =>
      intro hu hv
      refine Relation.EqvGen.rel _ _ ?_
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    | refl => intro _ _; exact Relation.EqvGen.refl _
    | symm u v _ ih => intro hu hv; exact (ih hv hu).symm
    | trans u w v huw _ ih₁ ih₂ =>
      intro hu hv
      have hw : p w := (invariant_of_eqvGen p hσ hα huw).1 hu
      exact (ih₁ hu hw).trans _ _ _ (ih₂ hw hv)
  refine connected_of_base _ ⟨c, hc⟩ ?_
  rintro ⟨x, hx⟩
  exact key c x (hreach x hx) hc hx

/-! ### The component of a dart -/

variable (M) (c : M.D)

/--
@isnad1 id=iff.0h3v.s5.ec4000526253 from=translated src=- shape=50839f42 vocab=72dcbec4
-/
theorem component_invariant_σ : ∀ x, Relation.EqvGen M.Step c (M.σ x) ↔
    Relation.EqvGen M.Step c x := fun x =>
  ⟨fun h => h.trans _ _ _ ((Relation.EqvGen.rel x (M.σ x) (Or.inl rfl)).symm _ _),
    fun h => h.trans _ _ _ (Relation.EqvGen.rel x (M.σ x) (Or.inl rfl))⟩

/--
@isnad1 id=iff.0h3v.s5.167c4510a41b from=translated src=- shape=50839f42 vocab=5e50be4f
-/
theorem component_invariant_α : ∀ x, Relation.EqvGen M.Step c (M.α x) ↔
    Relation.EqvGen M.Step c x := fun x =>
  ⟨fun h => h.trans _ _ _ ((Relation.EqvGen.rel x (M.α x) (Or.inr rfl)).symm _ _),
    fun h => h.trans _ _ _ (Relation.EqvGen.rel x (M.α x) (Or.inr rfl))⟩

open Classical in
/-- The connected component of the dart `c`.-/
noncomputable def component : CombMap :=
  M.restrict (fun x => Relation.EqvGen M.Step c x) (M.component_invariant_σ c)
    (M.component_invariant_α c)

open Classical in
/-- The darts not connected to `c`.-/
noncomputable def componentCompl : CombMap :=
  M.restrict (fun x => ¬ Relation.EqvGen M.Step c x)
    (not_invariant_σ _ (M.component_invariant_σ c)) (not_invariant_α _ (M.component_invariant_α c))

/-- `χ` is the sum over the component of `c` and the rest.
@isnad1 id=eq.0h2v.s4.5c592ffa88ce from=translated src=- shape=41e92ff8 vocab=0325ef8f
-/
theorem euler_component_add : M.euler = (M.component c).euler + (M.componentCompl c).euler := by
  classical
  exact euler_restrict_add _ (M.component_invariant_σ c) (M.component_invariant_α c)

/-- The component of a dart is connected.
@isnad1 id=connecte.0h2v.s3.9dc55d94b321 from=translated src=- shape=1f8e965c vocab=768a2536
-/
theorem component_connected : (M.component c).Connected := by
  classical
  exact restrict_connected _ _ _ c (Relation.EqvGen.refl _) fun _ h => h

/-- If every dart outside the component of `c` is connected to `d`, the rest is connected.
@isnad1 id=connecte.2h3v.s5.a94ec0130a97 from=translated src=- shape=529b90cf vocab=7a303e1b
-/
theorem componentCompl_connected (d : M.D) (hd : ¬ Relation.EqvGen M.Step c d)
    (h : ∀ x, ¬ Relation.EqvGen M.Step c x → Relation.EqvGen M.Step d x) :
    (M.componentCompl c).Connected := by
  classical
  exact restrict_connected _ _ _ d hd h

/-! ### Splitting a spherical map inside one face -/

variable {M} {a b : M.D}

end CombMap

end TheoremA.Picture
