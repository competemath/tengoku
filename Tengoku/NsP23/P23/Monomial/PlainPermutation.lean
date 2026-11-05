import Tengoku.NsP23.P23.Monomial.PlainGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace P23.Monomial
noncomputable section
def plainCoordinatePerm (e : Equiv.Perm (Fin 3)) : PlainExp ≃+ PlainExp := Finsupp.domCongr e.symm

/--
@isnad1 id=eq.0h3v.s7.ceb56a49efc1 from=translated src=- shape=c82c63b6 vocab=1587c2fc
-/
@[simp] theorem plainCoordinatePerm_apply (e : Equiv.Perm (Fin 3)) (p : PlainExp) (j : Fin 3) :
    plainCoordinatePerm e p j = p (e j) := by simp [plainCoordinatePerm]

/--
@isnad1 id=iff.0h3v.s7.21a8884afe75 from=translated src=- shape=daedeb4c vocab=c2b9b83d
-/
theorem plainDivides_coordinatePerm_iff (e : Equiv.Perm (Fin 3)) (p q : PlainExp) :
    plainDivides (plainCoordinatePerm e p) (plainCoordinatePerm e q) ↔ plainDivides p q := by
  constructor
  · intro h j; simpa using h (e.symm j)
  · intro h j; simpa using h (e j)

/--
@isnad1 id=iff.0h3v.s7.dfee6ebd08a2 from=translated src=- shape=fa1a2c0a vocab=f0370b56
-/
theorem plainStandard_coordinatePerm_iff (e : Equiv.Perm (Fin 3)) (R : Finset PlainExp) (p : PlainExp) :
    plainCoordinatePerm e p ∈ plainStandardSet (R.image (plainCoordinatePerm e)) ↔
      p ∈ plainStandardSet R := by
  constructor
  · rintro ⟨s,hs,hps⟩
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨t,ht,(plainDivides_coordinatePerm_iff e p t).mp hps⟩
  · rintro ⟨s,hs,hps⟩
    exact ⟨plainCoordinatePerm e s,Finset.mem_image.mpr ⟨s,hs,rfl⟩,
      (plainDivides_coordinatePerm_iff e p s).mpr hps⟩

/--
@isnad1 id=iff.0h3v.s7.78ff1f2bf1d8 from=translated src=- shape=eaea376c vocab=03a3d7e1
-/
theorem plainBorder_coordinatePerm_iff (e : Equiv.Perm (Fin 3)) (R : Finset PlainExp) (p : PlainExp) :
    plainCoordinatePerm e p ∈ plainBorderFinset (R.image (plainCoordinatePerm e)) ↔
      p ∈ plainBorderFinset R := by
  rw [plain_border_iff_minimalKilled,plain_border_iff_minimalKilled]
  constructor
  · rintro ⟨hn,hm⟩
    refine ⟨fun hp => hn ((plainStandard_coordinatePerm_iff e R p).mpr hp),?_⟩
    intro q hqp hne
    apply (plainStandard_coordinatePerm_iff e R q).mp
    exact hm _ ((plainDivides_coordinatePerm_iff e q p).mpr hqp)
      (fun h => hne ((plainCoordinatePerm e).injective h))
  · rintro ⟨hn,hm⟩
    refine ⟨fun hp => hn ((plainStandard_coordinatePerm_iff e R p).mp hp),?_⟩
    intro q hqp hne
    let t := (plainCoordinatePerm e).symm q
    have ht : plainCoordinatePerm e t=q := (plainCoordinatePerm e).apply_symm_apply q
    have htp : plainDivides t p := (plainDivides_coordinatePerm_iff e t p).mp (ht.symm ▸ hqp)
    have htn : t≠p := by intro h; exact hne (by simpa [h] using ht.symm)
    have hs := (plainStandard_coordinatePerm_iff e R t).mpr (hm t htp htn)
    simpa [ht] using hs

/--
@isnad1 id=eq.0h2v.s7.ef280c54076d from=translated src=- shape=c8d8db17 vocab=7b9c8d10
-/
theorem plainBorder_card_permutation (e : Equiv.Perm (Fin 3)) (R : Finset PlainExp) :
    (plainBorderFinset (R.image (plainCoordinatePerm e))).card = (plainBorderFinset R).card := by
  have he : plainBorderFinset (R.image (plainCoordinatePerm e)) =
      (plainBorderFinset R).image (plainCoordinatePerm e) := by
    ext p
    constructor
    · intro hp
      let q := (plainCoordinatePerm e).symm p
      have hq := (plainBorder_coordinatePerm_iff e R q).mp
        (by simpa [q] using hp)
      exact Finset.mem_image.mpr ⟨q,hq,(plainCoordinatePerm e).apply_symm_apply p⟩
    · rintro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact (plainBorder_coordinatePerm_iff e R q).mpr hq
  rw [he,Finset.card_image_of_injective _ (plainCoordinatePerm e).injective]
/--
@isnad1 id=plainroo.1h2v.s7.5c6b2908b7bb from=translated src=- shape=033817e5 vocab=96eae782
-/
theorem plainAntichain_coordinatePerm (e : Equiv.Perm (Fin 3))
    (R : Finset PlainExp) (ha : PlainRootAntichain R) :
    PlainRootAntichain (R.image (plainCoordinatePerm e)) := by
  intro p hp q hq hd
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  exact congrArg (plainCoordinatePerm e)
    (ha s hs t ht ((plainDivides_coordinatePerm_iff e s t).mp hd))

/--
@isnad1 id=hasplain.1h2v.s7.cddfeb1369cc from=translated src=- shape=033817e5 vocab=699752e2
-/
theorem plainCentres_coordinatePerm (e : Equiv.Perm (Fin 3))
    (R : Finset PlainExp) (hc : HasPlainDirectionalCentres R) :
    HasPlainDirectionalCentres (R.image (plainCoordinatePerm e)) := by
  intro j
  obtain ⟨c,hc⟩ := hc (e j)
  refine ⟨plainCoordinatePerm e c,Finset.mem_image.mpr ⟨c,hc.1,rfl⟩,?_⟩
  intro s hs hp
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
  have hb := hc.2 t ht (by simpa using hp)
  intro r
  have hr := hb (e r)
  by_cases h : r = j
  · subst r
    simpa [plainPredecessor_apply] using hr
  · have he : e r ≠ e j := fun he => h (e.injective he)
    simpa [plainPredecessor_apply,h,Ne.symm h,he,Ne.symm he] using hr

/--
@isnad1 id=plaindir.1h4v.s8.fb0e361a6c9a from=translated src=- shape=a6c60503 vocab=1018557b
-/
theorem plainCentre_coordinatePerm (e : Equiv.Perm (Fin 3))
    (R : Finset PlainExp) (j : Fin 3) (c : PlainExp)
    (hc : PlainDirectionalCentre R (e j) c) :
    PlainDirectionalCentre (R.image (plainCoordinatePerm e)) j (plainCoordinatePerm e c) := by
  refine ⟨Finset.mem_image.mpr ⟨c,hc.1,rfl⟩,?_⟩
  intro s hs hp
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
  have hb := hc.2 t ht (by simpa using hp)
  intro r
  have hr := hb (e r)
  by_cases h : r=j
  · subst r; simpa [plainPredecessor_apply] using hr
  · have he : e r ≠ e j := fun he => h (e.injective he)
    simpa [plainPredecessor_apply,h,Ne.symm h,he,Ne.symm he] using hr

/--
@isnad1 id=plainvar.1h2v.s7.e28ba8401963 from=translated src=- shape=033817e5 vocab=1f5ad234
-/
theorem plainVariables_coordinatePerm (e : Equiv.Perm (Fin 3))
    (R : Finset PlainExp) (hv : PlainVariablesSurvive R) :
    PlainVariablesSurvive (R.image (plainCoordinatePerm e)) := by
  intro j
  obtain ⟨s,hs,hjs⟩ := plain_direction_active R hv (e j)
  refine ⟨plainCoordinatePerm e s,Finset.mem_image.mpr ⟨s,hs,rfl⟩,?_⟩
  intro r
  by_cases h : r=j
  · subst r; simp only [plainUnitVector_apply,ite_true,plainCoordinatePerm_apply]; omega
  · simp [plainUnitVector_apply,h,Ne.symm h]

end
end P23.Monomial
