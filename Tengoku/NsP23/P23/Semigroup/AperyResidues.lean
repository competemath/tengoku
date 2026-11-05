import Tengoku.NsP23.P23.Semigroup.FourGenerated
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section

def aperyResidue (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (s : D.AperyIndex i) : ZMod (D.n i) := s.1.1

private theorem apery_eq_of_le_residue (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (s t : D.AperyIndex i) (hle : s.1.1 ≤ t.1.1)
    (he : aperyResidue D i s = aperyResidue D i t) : s=t := by
  have hm : s.1.1 ≡ t.1.1 [MOD D.n i] := (ZMod.natCast_eq_natCast_iff _ _ _).mp he
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hm
  cases k with
  | zero => apply Subtype.ext; apply Subtype.ext; simpa using hk.symm
  | succ k =>
    exfalso
    apply t.2
    refine ⟨s.1 + k • D.base i, ?_⟩
    apply Subtype.ext
    change t.1.1 = D.n i + (s.1.1 + k * D.n i)
    rw [hk]; ring

/--
@isnad1 id=injectiv.0h2v.s4.bea27ead1f1d from=translated src=- shape=57ca8524 vocab=c11da1d3
-/
theorem aperyResidue_injective (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Function.Injective (aperyResidue D i) := by
  intro s t he
  rcases le_total s.1.1 t.1.1 with h | h
  · exact apery_eq_of_le_residue D i s t h he
  · exact (apery_eq_of_le_residue D i t s h he.symm).symm

/--
@isnad1 id=surjecti.0h2v.s4.a71be06e57ce from=translated src=- shape=57ca8524 vocab=ead85631
-/
theorem aperyResidue_surjective (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Function.Surjective (aperyResidue D i) := by
  classical
  letI : NeZero (D.n i) := ⟨Nat.ne_of_gt (D.positive i)⟩
  intro r
  let P : ℕ → Prop := fun s => s ∈ D.Gamma ∧ (s : ZMod (D.n i))=r
  have hex : ∃ s, P s := by
    refine ⟨r.val + D.conductor * D.n i, ?_, ?_⟩
    · apply D.mem_Gamma_of_conductor_le
      have := Nat.mul_le_mul_left D.conductor (D.positive i)
      omega
    · simp
  let s := Nat.find hex
  have hs := Nat.find_spec hex
  have ha : D.IsApery i ⟨s,hs.1⟩ := by
    rintro ⟨h,he⟩
    have hval : s=D.n i+h.1 := congrArg Subtype.val he
    have hp : P h.1 := by
      refine ⟨h.2, ?_⟩
      have hh := hs.2
      change (s : ZMod (D.n i))=r at hh
      rw [hval] at hh
      simpa using hh
    have hh := Nat.find_min' hex hp
    have hq := D.positive i
    omega
  exact ⟨⟨⟨s,hs.1⟩,ha⟩,hs.2⟩

def aperyResidueEquiv (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    D.AperyIndex i ≃ ZMod (D.n i) :=
  Equiv.ofBijective (aperyResidue D i) ⟨aperyResidue_injective D i,aperyResidue_surjective D i⟩

/--
@isnad1 id=eq.0h2v.s4.b36b7f92b0d9 from=translated src=- shape=2eced3fb vocab=dc03a023
-/
theorem aperyIndex_card (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :
    Nat.card (D.AperyIndex i)=D.n i := by
  letI : NeZero (D.n i) := ⟨Nat.ne_of_gt (D.positive i)⟩
  rw [Nat.card_congr (aperyResidueEquiv D i),Nat.card_eq_fintype_card,ZMod.card]

end
end P23.Semigroup.FourGeneratedNumericalSemigroup
