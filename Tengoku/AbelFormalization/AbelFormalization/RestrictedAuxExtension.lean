import Tengoku.AbelFormalization.AbelFormalization.ExponentialTowerPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adding unrestricted auxiliary variables

The restricted expression language permits arbitrarily many unrestricted
auxiliary coordinates.  This file embeds an expression base and an entire
finite exponential tower after adjoining a finite block of fresh auxiliary
variables.  Old functions are pulled back by forgetting the new block; all
new coordinates are available in the enlarged base.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Forget the last `k` unrestricted auxiliary coordinates.-/
def restrictedSourceDropAux {m p a : ℕ} (k : ℕ) :
    RestrictedSource m p (a + k) → RestrictedSource m p a :=
  fun x ↦ (x.1, fun i ↦ x.2 (Fin.castAdd k i))

/--
@isnad1 id=eq.0h5v.s6.6ae16f3210b7 from=translated src=- shape=568f8e8a vocab=610b2c34
-/
@[simp]
theorem restrictedSourceDropAux_fst {m p a : ℕ} (k : ℕ)
    (x : RestrictedSource m p (a + k)) :
    (restrictedSourceDropAux k x).1 = x.1 :=
  rfl

/--
@isnad1 id=eq.0h6v.s6.a5509448e814 from=translated src=- shape=174b0845 vocab=57289151
-/
@[simp]
theorem restrictedSourceDropAux_aux {m p a : ℕ} (k : ℕ)
    (x : RestrictedSource m p (a + k)) (i : Fin a) :
    (restrictedSourceDropAux k x).2 i = x.2 (Fin.castAdd k i) :=
  rfl

/-- Pull a set of special generators back after forgetting the fresh
auxiliary block.-/
def restrictedSpecialGeneratorsExtendAux {m p a : ℕ} (k : ℕ)
    (S : Set (RestrictedSource m p a → ℝ)) :
    Set (RestrictedSource m p (a + k) → ℝ) :=
  functionPrecompAlgHom (restrictedSourceDropAux k) '' S

/--
@isnad1 id=eq.0h5v.s8.54fc92bc72ae from=translated src=- shape=576ea113 vocab=63222f0c
-/
theorem precomp_restrictedSCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin m) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedSCoordinate (p := p) (a := a) i) =
      restrictedSCoordinate (p := p) (a := a + k) i :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.dd70d4560b06 from=translated src=- shape=792d8e23 vocab=5c5127fb
-/
theorem precomp_restrictedWCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin p) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedWCoordinate (m := m) (a := a) i) =
      restrictedWCoordinate (m := m) (a := a + k) i :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.f6758f29357d from=translated src=- shape=0e9d6ea2 vocab=26f5e941
-/
theorem precomp_restrictedAuxCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin a) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedAuxCoordinate (m := m) (p := p) i) =
      restrictedAuxCoordinate (m := m) (p := p) (Fin.castAdd k i) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.d5da504ab4aa from=translated src=- shape=23707220 vocab=de326657
-/
theorem precomp_restrictedBoxCoefficientPullback_dropAux
    {m p a : ℕ} (k : ℕ) (f : RestrictedBoxSpace p → ℝ) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedBoxCoefficientPullback (m := m) (a := a) f) =
      restrictedBoxCoefficientPullback (m := m) (a := a + k) f :=
  rfl

/-- Every fixed generator remains a fixed generator after auxiliary
extension.
@isnad1 id=le.0h5v.s8.b705118238eb from=translated src=- shape=fac54b0f vocab=d47bba8a
-/
theorem image_restrictedFixedGenerators_dropAux_subset
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ) :
    functionPrecompAlgHom (restrictedSourceDropAux k) ''
        restrictedFixedGenerators (m := m) (a := a) D ⊆
      restrictedFixedGenerators (m := m) (a := a + k) D := by
  rintro g ⟨f, hf, rfl⟩
  rcases hf with (hf | hf)
  · rcases hf with (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, rfl⟩)
    · exact Or.inl (Or.inr ⟨Fin.castAdd k i, rfl⟩)
  · rcases hf with ⟨f, rfl⟩
    exact Or.inr ⟨f, rfl⟩

/-- Pullback of the old restricted expression base lies in the enlarged
base with the pulled-back special generators.
@isnad1 id=le.0h6v.s8.2f4d7ef82068 from=translated src=- shape=7b183627 vocab=cc15a270
-/
theorem map_restrictedExpressionBase_dropAux_le
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ)
    (S : Set (RestrictedSource m p a → ℝ)) :
    (restrictedExpressionBase D S).map
        (functionPrecompAlgHom (restrictedSourceDropAux k)) ≤
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) := by
  rw [restrictedExpressionBase, AlgHom.map_adjoin]
  apply Algebra.adjoin_mono
  rintro g ⟨f, hf, rfl⟩
  rcases hf with hf | hf
  · exact Or.inl (image_restrictedFixedGenerators_dropAux_subset D k
      ⟨f, hf, rfl⟩)
  · exact Or.inr ⟨f, hf, rfl⟩

/-- Every old special generator, pulled back to the enlarged source, is in
the enlarged expression base.
@isnad1 id=mem.1h7v.s9.877c83b3ca44 from=translated src=- shape=dc2c906f vocab=2a557c8c
-/
theorem precomp_specialGenerator_mem_extendedBase
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ)
    {S : Set (RestrictedSource m p a → ℝ)}
    {f : RestrictedSource m p a → ℝ} (hf : f ∈ S) :
    functionPrecompAlgHom (restrictedSourceDropAux k) f ∈
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) := by
  apply specialGenerator_mem_base D
  exact ⟨f, hf, rfl⟩

/-- The `j`th fresh auxiliary coordinate belongs to the enlarged base.
@isnad1 id=mem.0h7v.s8.23c692abc5e8 from=translated src=- shape=45bdf8ee vocab=9ab650b8
-/
theorem freshAuxCoordinate_mem_extendedBase
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ) (j : Fin k)
    (S : Set (RestrictedSource m p a → ℝ)) :
    restrictedAuxCoordinate (m := m) (p := p) (Fin.natAdd a j) ∈
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) :=
  restrictedAuxCoordinate_mem_base D _ (Fin.natAdd a j)

/-- Extend a restricted expression tower by a fresh block of unrestricted
auxiliary coordinates.-/
def RestrictedExpressionTower.extendAux
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ) :
    RestrictedExpressionTower D
      (restrictedSpecialGeneratorsExtendAux k S) (ell := ell) :=
  T.pullbackChangeBase (restrictedSourceDropAux k)
    (restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S))
    (map_restrictedExpressionBase_dropAux_le D k S)

/-- A function in an old tower level remains in the same level after adding
fresh unrestricted auxiliary coordinates.
@isnad1 id=mem.1h10v.s9.1970a59fcb8f from=translated src=- shape=fb2a537e vocab=0fa57058
-/
theorem RestrictedExpressionTower.precomp_mem_extendAux_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    {j : ℕ} {f : RestrictedSource m p a → ℝ} (hf : f ∈ T.level j) :
    functionPrecompAlgHom (restrictedSourceDropAux k) f ∈
      (T.extendAux k).level j :=
  T.precomp_mem_pullbackChangeBase_level
    (restrictedSourceDropAux k)
    (restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S))
    (map_restrictedExpressionBase_dropAux_le D k S) hf

/--
@isnad1 id=eq.0h10v.s6.7ddbc713d17e from=translated src=- shape=184a42be vocab=19ca8288
-/
@[simp]
theorem RestrictedExpressionTower.extendAux_exponent_apply
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    (i : Fin ell) (x : RestrictedSource m p (a + k)) :
    (T.extendAux k).exponent i x =
      T.exponent i (restrictedSourceDropAux k x) :=
  rfl

/--
@isnad1 id=eq.0h10v.s6.688b421a1641 from=translated src=- shape=184a42be vocab=88dbb672
-/
@[simp]
theorem RestrictedExpressionTower.extendAux_generator_apply
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    (i : Fin ell) (x : RestrictedSource m p (a + k)) :
    (T.extendAux k).generator i x =
      T.generator i (restrictedSourceDropAux k x) :=
  rfl

end AbelFormalization
