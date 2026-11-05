import Tengoku.NsP23.P23.Semigroup.ChosenBase
import Tengoku.Seed.SetTheory.Cardinal.NatCard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pseudo-Frobenius numbers and Apéry-socle indices

All pseudo-Frobenius translations take place in `ℤ`; no truncated natural
subtraction occurs in the theorem DAG.
-/

namespace P23.Semigroup

noncomputable section

/-- Integer-valued membership in the generated numerical semigroup.-/
def IntInGamma (D : FourGeneratedNumericalSemigroup) (z : ℤ) : Prop :=
  ∃ s : D.Gamma, (s.1 : ℤ) = z

namespace FourGeneratedNumericalSemigroup

variable (D : FourGeneratedNumericalSemigroup)

@[simp] theorem intInGamma_zero : IntInGamma D 0 := ⟨0, by simp⟩

theorem intInGamma_generator (j : Fin 4) : IntInGamma D (D.n j) :=
  ⟨D.generator j, by simp [generator]⟩

theorem intInGamma_add {x y : ℤ} (hx : IntInGamma D x)
    (hy : IntInGamma D y) : IntInGamma D (x + y) := by
  rcases hx with ⟨s, rfl⟩
  rcases hy with ⟨t, rfl⟩
  exact ⟨s + t, by simp⟩

@[simp] theorem intInGamma_natCast (s : ℕ) :
    IntInGamma D (s : ℤ) ↔ s ∈ D.Gamma := by
  constructor
  · rintro ⟨t, ht⟩
    have hts : t.1 = s := by exact_mod_cast ht
    simpa [hts] using t.2
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- Intrinsic integer pseudo-Frobenius condition.-/
def IsPseudoFrobenius (f : ℤ) : Prop :=
  ¬ IntInGamma D f ∧
    ∀ s : D.Gamma, s ≠ 0 → IntInGamma D (f + s.1)

private theorem exists_generator_add_of_ne_zero (s : D.Gamma) (hs : s ≠ 0) :
    ∃ j : Fin 4, ∃ h : D.Gamma, s = D.generator j + h := by
  rcases (D.mem_Gamma_iff s.1).1 s.2 with ⟨u, hu⟩
  have une : u ≠ 0 := by
    intro hz
    subst u
    simp at hu
    apply hs
    exact Subtype.ext hu.symm
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp une
  have hjpos : 0 < u j := Nat.pos_of_ne_zero hj
  let v : Fin 4 →₀ ℕ := u - Finsupp.single j 1
  have huv : u = Finsupp.single j 1 + v := by
    apply Finsupp.ext
    intro l
    by_cases hlj : l = j
    · subst l
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, v,
        Finsupp.tsub_apply]
      omega
    · simp [v, Finsupp.single_apply, hlj]
  have hvGamma : D.weightedDegree v ∈ D.Gamma :=
    (D.mem_Gamma_iff _).2 ⟨v, rfl⟩
  refine ⟨j, ⟨D.weightedDegree v, hvGamma⟩, ?_⟩
  apply Subtype.ext
  change s.1 = D.n j + D.weightedDegree v
  rw [← hu, huv]
  change weightedDegreeOf D.n (Finsupp.single j 1 + v) = _
  rw [weightedDegreeOf_add]
  simpa [generatorFactorization] using
    congrArg (fun z => z + D.weightedDegree v)
      (D.weightedDegree_generatorFactorization j)

/-- The pseudo-Frobenius condition is detected by the four minimal
generators.-/
theorem isPseudoFrobenius_iff_generators (f : ℤ) :
    D.IsPseudoFrobenius f ↔
      (¬ IntInGamma D f ∧ ∀ j : Fin 4, IntInGamma D (f + D.n j)) := by
  constructor
  · rintro ⟨hnot, hpos⟩
    refine ⟨hnot, fun j => hpos (D.generator j) ?_⟩
    intro hz
    have := congrArg Subtype.val hz
    simpa [generator] using (Nat.ne_of_gt (D.positive j) this)
  · rintro ⟨hnot, hgen⟩
    refine ⟨hnot, ?_⟩
    intro s hs
    rcases D.exists_generator_add_of_ne_zero s hs with ⟨j, h, rfl⟩
    have hh : IntInGamma D (h.1 : ℤ) := (D.intInGamma_natCast h.1).2 h.2
    convert D.intInGamma_add (hgen j) hh using 1
    simp only [generator]
    push_cast
    ring

/-- The finite index type of pseudo-Frobenius integers.-/
abbrev PseudoFrobeniusIndex := {f : ℤ // D.IsPseudoFrobenius f}

private def pfToApery (i : Fin 4) (f : D.PseudoFrobeniusIndex) :
    D.AperyIndex i := by
  have hmem : IntInGamma D (f.1 + D.n i) :=
    (D.isPseudoFrobenius_iff_generators f.1).1 f.2 |>.2 i
  let s : D.Gamma := Classical.choose hmem
  have hs : (s.1 : ℤ) = f.1 + D.n i := Classical.choose_spec hmem
  refine ⟨s, ?_⟩
  rintro ⟨h, hh⟩
  apply f.2.1
  refine ⟨h, ?_⟩
  have hv := congrArg (fun z : D.Gamma => (z.1 : ℤ)) hh
  simp only [AddSubmonoid.coe_add, base, generator] at hv
  omega

private theorem pfToApery_val (i : Fin 4) (f : D.PseudoFrobeniusIndex) :
    ((D.pfToApery i f).1.1 : ℤ) = f.1 + D.n i := by
  simp only [pfToApery]
  exact Classical.choose_spec
    ((D.isPseudoFrobenius_iff_generators f.1).1 f.2 |>.2 i)

private theorem pfToApery_injective (i : Fin 4) :
    Function.Injective (D.pfToApery i) := by
  intro f g h
  apply Subtype.ext
  have hv := congrArg (fun s : D.AperyIndex i => (s.1.1 : ℤ)) h
  rw [D.pfToApery_val i f, D.pfToApery_val i g] at hv
  omega

instance pseudoFrobeniusFinite : Finite D.PseudoFrobeniusIndex :=
  Finite.of_injective (D.pfToApery 0) (D.pfToApery_injective 0)

noncomputable instance pseudoFrobeniusFintype : Fintype D.PseudoFrobeniusIndex :=
  Fintype.ofFinite D.PseudoFrobeniusIndex

/-- Numerical-semigroup type as the number of pseudo-Frobenius integers.-/
def semigroupType : ℕ := Fintype.card D.PseudoFrobeniusIndex

/-- Apéry degrees killed by multiplication with each of the three tails.-/
abbrev AperySocleIndex (i : Fin 4) :=
  {s : D.AperyIndex i //
    ∀ j : Fin 3, ¬ D.IsApery i (s.1 + D.tail i j)}

instance aperySocleIndexFinite (i : Fin 4) : Finite (D.AperySocleIndex i) :=
  inferInstance

noncomputable instance aperySocleIndexFintype (i : Fin 4) :
    Fintype (D.AperySocleIndex i) := Fintype.ofFinite _

private def pfToAperySocle (i : Fin 4) (f : D.PseudoFrobeniusIndex) :
    D.AperySocleIndex i := by
  let s := D.pfToApery i f
  refine ⟨s, ?_⟩
  intro j hs
  have htail : IntInGamma D (f.1 + D.n (D.tailIndex i j)) :=
    (D.isPseudoFrobenius_iff_generators f.1).1 f.2 |>.2 _
  rcases htail with ⟨h, hh⟩
  apply hs
  refine ⟨h, ?_⟩
  apply Subtype.ext
  have hsval : (s.1.1 : ℤ) = f.1 + D.n i := D.pfToApery_val i f
  have hh' : (h.1 : ℤ) = f.1 + D.n (D.tailIndex i j) := hh
  simp only [AddSubmonoid.coe_add, base, generator, tail] at *
  omega

private def aperySocleToPf (i : Fin 4) (s : D.AperySocleIndex i) :
    D.PseudoFrobeniusIndex := by
  let f : ℤ := (s.1.1.1 : ℤ) - D.n i
  refine ⟨f, (D.isPseudoFrobenius_iff_generators f).2 ?_⟩
  constructor
  · rintro ⟨h, hh⟩
    apply s.1.2
    refine ⟨h, ?_⟩
    apply Subtype.ext
    have hh' : (h.1 : ℤ) = f := hh
    simp only [base, generator, AddSubmonoid.coe_add]
    exact_mod_cast (show s.1.1.1 = D.n i + h.1 by omega)
  · intro j
    by_cases hji : j = i
    · subst j
      exact ⟨s.1.1, by simp [f]⟩
    · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hji
      subst j
      have hnot := s.2 l
      simp only [IsApery] at hnot
      push_neg at hnot
      rcases hnot with ⟨h, hh⟩
      refine ⟨h, ?_⟩
      have hv := congrArg (fun z : D.Gamma => (z.1 : ℤ)) hh
      simp only [AddSubmonoid.coe_add, base, generator, tail, tailIndex_apply,
        f] at hv ⊢
      omega

/-- Exact pseudo-Frobenius/Apéry-socle index equivalence for every chosen
base.-/
def pseudoFrobeniusEquivAperySocle (i : Fin 4) :
    D.PseudoFrobeniusIndex ≃ D.AperySocleIndex i where
  toFun := D.pfToAperySocle i
  invFun := D.aperySocleToPf i
  left_inv f := by
    apply Subtype.ext
    simp only [aperySocleToPf, pfToAperySocle]
    rw [D.pfToApery_val i f]
    omega
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hv := D.pfToApery_val i (D.aperySocleToPf i s)
    have hz :
        (((D.pfToApery i (D.aperySocleToPf i s)).1.1 : ℤ)) =
          (s.1.1.1 : ℤ) := by
      rw [hv]
      simp only [aperySocleToPf]
      omega
    exact_mod_cast hz

theorem pseudoFrobenius_card_eq_aperySocle_card (i : Fin 4) :
    Fintype.card (D.AperySocleIndex i) = D.semigroupType := by
  rw [semigroupType, Fintype.card_congr (D.pseudoFrobeniusEquivAperySocle i)]

end FourGeneratedNumericalSemigroup

end

end P23.Semigroup
