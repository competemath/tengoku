import Tengoku.NsP23.P23.Semigroup.PseudoFrobenius
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Locality, intrinsic socle, and type of chosen-base quotients
-/

namespace P23.Semigroup

noncomputable section

open FourGeneratedNumericalSemigroup AperyArtin

variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

/-- Tail multiplication kills an Apéry basis monomial exactly when the sum
leaves the Apéry set.-/
theorem tailVariableA_mul_A_eq_zero_iff (s : D.AperyIndex i) (j : Fin 3) :
    tailVariableA (k := k) D i j * A (k := k) s.1 s.2 = 0 ↔
      ¬ D.IsApery i (s.1 + D.tail i j) := by
  classical
  change A (k := k) (D.tail i j) (D.tail_isApery i j) *
      A (k := k) s.1 s.2 = 0 ↔ _
  rw [A_mul_A]
  by_cases h : D.IsApery i (D.tail i j + s.1)
  · rw [dite_eq_left h]
    have h' : D.IsApery i (s.1 + D.tail i j) := by simpa [add_comm] using h
    constructor
    · intro hz
      have hc := congrArg (fun x : AperyArtin k D i =>
        x.coeff ⟨D.tail i j + s.1, h⟩) hz
      simp [coeff_A] at hc
    · intro hn
      exact (hn h').elim
  · have h' : ¬ D.IsApery i (s.1 + D.tail i j) := by simpa [add_comm] using h
    simp [h, h']

private theorem tailVariableA_pow_eq (j : Fin 3) (n : ℕ) :
    (tailVariableA (k := k) D i j) ^ n =
      truncatedAperyMonomial (k := k) D i (n • D.tail i j) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ, hn, ← truncatedAperyMonomial_tail,
        ← truncatedAperyMonomial_add]
      congr 2
      rw [add_nsmul]
      simp [add_comm]

/-- Every tail variable is nilpotent, using the uniform Run20 Apéry degree
bound rather than enumeration.-/
theorem tailVariableA_isNilpotent (j : Fin 3) :
    IsNilpotent (tailVariableA (k := k) D i j) := by
  refine ⟨D.conductor + D.n i, ?_⟩
  rw [tailVariableA_pow_eq]
  simp only [truncatedAperyMonomial]
  split
  · rename_i h
    have hb := D.isApery_lt i h
    have htail : 0 < (D.tail i j).1 := D.tailGen_positive i j
    have hv : (D.conductor + D.n i) ≤
        ((D.conductor + D.n i) • D.tail i j).1 := by
      change D.conductor + D.n i ≤
        (D.conductor + D.n i) * (D.tail i j).1
      exact Nat.le_mul_of_pos_right _ htail
    omega
  · rfl

/-- Degree-zero coefficient, packaged as an algebra homomorphism.-/
def aperyAugmentationAlgHom : AperyArtin k D i →ₐ[k] k :=
  (TrivSqZeroExt.fstHom k k (Fin 3 → k)).comp
    (aperyFirstOrderAlgHom (k := k) D i)

@[simp] theorem aperyAugmentationAlgHom_apply (x : AperyArtin k D i) :
    aperyAugmentationAlgHom (k := k) D i x =
      aperyConstantCoeff (k := k) D i x := rfl

theorem apery_basis_expansion (x : AperyArtin k D i) :
    x = x.coeff.sum fun s r => r • A (k := k) s.1 s.2 := by
  induction x using AperyArtin.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [AperyArtin.coeff_add,
        Finsupp.sum_add_index'
          (fun a => zero_smul k (A (k := k) a.1 a.2))
          (fun a b₁ b₂ => add_smul b₁ b₂ (A (k := k) a.1 a.2)),
        ← hx, ← hy]
  | single s r =>
      change AperyArtin.mk (Finsupp.single s r) =
        (Finsupp.single s r).sum fun t c => c • A (k := k) t.1 t.2
      rw [Finsupp.sum_single_index]
      · exact (AperyArtin.smul_A (k := k) r s.1 s.2).symm
      · simp

private theorem mem_aperyAugmentationIdeal_of_constantCoeff_eq_zero
    (x : AperyArtin k D i) (hx : aperyConstantCoeff (k := k) D i x = 0) :
    x ∈ aperyAugmentationIdeal (k := k) D i := by
  rw [apery_basis_expansion (k := k) D i x]
  apply Submodule.sum_mem
  intro s hs
  by_cases hs0 : s.1 = 0
  · have se : s = ⟨0, D.zero_isApery i⟩ := Subtype.ext hs0
    subst s
    have hc : x.coeff ⟨0, D.zero_isApery i⟩ = 0 := hx
    simp [hc]
  · simpa [Algebra.smul_def] using
      (aperyAugmentationIdeal (k := k) D i).mul_mem_left
        (algebraMap k (AperyArtin k D i) (x.coeff s))
        (A_mem_aperyAugmentationIdeal (k := k) D i s hs0)

/-- The algebra-hom kernel is exactly the frozen Run20 augmentation ideal.-/
theorem aperyAugmentationAlgHom_ker :
    RingHom.ker (aperyAugmentationAlgHom (k := k) D i).toRingHom =
      aperyAugmentationIdeal (k := k) D i := by
  apply le_antisymm
  · intro x hx
    exact mem_aperyAugmentationIdeal_of_constantCoeff_eq_zero
      (k := k) D i x hx
  · rw [aperyAugmentationIdeal_eq_tailVariableIdeal, tailVariableIdeal,
      Ideal.span_le]
    rintro x ⟨j, rfl⟩
    change aperyConstantCoeff (k := k) D i
      (tailVariableA (k := k) D i j) = 0
    simp [tailVariableA, aperyConstantCoeff_A]
    intro h
    have hv := congrArg Subtype.val h
    simpa [FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator] using
      (Nat.ne_of_gt (D.tailGen_positive i j) hv)

theorem aperyAugmentationAlgHom_surjective :
    Function.Surjective (aperyAugmentationAlgHom (k := k) D i) := by
  intro r
  exact ⟨algebraMap k (AperyArtin k D i) r,
    (aperyAugmentationAlgHom (k := k) D i).commutes r⟩

theorem aperyAugmentationIdeal_isMaximal :
    (aperyAugmentationIdeal (k := k) D i).IsMaximal := by
  rw [← aperyAugmentationAlgHom_ker (k := k) D i]
  exact RingHom.ker_isMaximal_of_surjective
    (aperyAugmentationAlgHom (k := k) D i).toRingHom
    (aperyAugmentationAlgHom_surjective (k := k) D i)

/-- Every maximal ideal of the finite Apéry algebra is the augmentation
ideal.-/
theorem aperyMaximalIdeal_eq_augmentationIdeal
    (I : Ideal (AperyArtin k D i)) (hI : I.IsMaximal) :
    I = aperyAugmentationIdeal (k := k) D i := by
  have htail : tailVariableIdeal (k := k) D i ≤ I := by
    rw [tailVariableIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact (nilpotent_iff_mem_prime.mp
      (tailVariableA_isNilpotent (k := k) D i j)) I hI.isPrime
  have haug : aperyAugmentationIdeal (k := k) D i ≤ I := by
    rw [aperyAugmentationIdeal_eq_tailVariableIdeal]
    exact htail
  exact (aperyAugmentationIdeal_isMaximal (k := k) D i).eq_of_le
    hI.ne_top haug |>.symm

/-- The finite Apéry algebra is a local ring.-/
theorem aperyIsLocalRing : IsLocalRing (AperyArtin k D i) := by
  apply IsLocalRing.of_unique_max_ideal
  exact ⟨aperyAugmentationIdeal (k := k) D i,
    aperyAugmentationIdeal_isMaximal (k := k) D i,
    fun I hI => aperyMaximalIdeal_eq_augmentationIdeal (k := k) D i I hI⟩

/-- Intrinsic Apéry socle: the annihilator of the augmentation ideal.-/
def AperySocle : Submodule k (AperyArtin k D i) where
  carrier := {x | ∀ r ∈ aperyAugmentationIdeal (k := k) D i, r * x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy r hr
    simp [mul_add, hx r hr, hy r hr]
  smul_mem' := by
    intro c x hx r hr
    rw [mul_smul_comm, hx r hr, smul_zero]

theorem mem_aperySocle_iff_tail_variables (x : AperyArtin k D i) :
    x ∈ AperySocle (k := k) D i ↔
      ∀ j : Fin 3, tailVariableA (k := k) D i j * x = 0 := by
  constructor
  · intro hx j
    exact hx _ (tailVariableA_mem_aperyAugmentationIdeal (k := k) D i j)
  · intro hx r hr
    rw [aperyAugmentationIdeal_eq_tailVariableIdeal] at hr
    let K : Ideal (AperyArtin k D i) :=
      { carrier := {z | z * x = 0}
        zero_mem' := by simp
        add_mem' := by
          intro a b ha hb
          change (a + b) * x = 0
          rw [add_mul, ha, hb, add_zero]
        smul_mem' := by
          intro a b hb
          change (a * b) * x = 0
          rw [mul_assoc, hb, mul_zero] }
    have hle : tailVariableIdeal (k := k) D i ≤ K := by
      rw [tailVariableIdeal, Ideal.span_le]
      rintro z ⟨j, rfl⟩
      exact hx j
    exact hle hr

theorem A_mem_aperySocle_iff (s : D.AperyIndex i) :
    A (k := k) s.1 s.2 ∈ AperySocle (k := k) D i ↔
      ∀ j : Fin 3, ¬ D.IsApery i (s.1 + D.tail i j) := by
  rw [mem_aperySocle_iff_tail_variables]
  constructor
  · intro h j
    exact (tailVariableA_mul_A_eq_zero_iff (k := k) D i s j).1 (h j)
  · intro h j
    exact (tailVariableA_mul_A_eq_zero_iff (k := k) D i s j).2 (h j)

private theorem coeff_tail_mul (x : AperyArtin k D i)
    (p : D.AperyIndex i) (j : Fin 3)
    (hpt : D.IsApery i (p.1 + D.tail i j)) :
    (tailVariableA (k := k) D i j * x).coeff
        ⟨p.1 + D.tail i j, hpt⟩ = x.coeff p := by
  classical
  induction x using AperyArtin.induction_linear with
  | zero => simp
  | add x y hx hy => simpa [mul_add] using congrArg₂ (· + ·) hx hy
  | single q r =>
      rw [← AperyArtin.smul_A (k := k) r q.1 q.2, mul_smul_comm]
      change (r • (A (k := k) (D.tail i j) (D.tail_isApery i j) *
        A (k := k) q.1 q.2)).coeff _ = _
      rw [A_mul_A]
      by_cases hq : D.IsApery i (D.tail i j + q.1)
      · rw [dite_eq_left hq]
        simp only [AperyArtin.coeff_smul, coeff_A, Finsupp.smul_apply,
          smul_eq_mul]
        by_cases hpq : p = q
        · subst q
          simp [add_comm]
        · have hne : (p.1 + D.tail i j) ≠ (D.tail i j + q.1) := by
            intro he
            apply hpq
            apply Subtype.ext
            have he' : p.1 + D.tail i j = q.1 + D.tail i j := by
              simpa [add_comm] using he
            exact add_right_cancel he'
          have hval : p.1 ≠ q.1 := fun hv => hpq (Subtype.ext hv)
          simp [hne, hval]
      · have hpq : p ≠ q := by
          intro he
          subst q
          exact hq (by simpa [add_comm] using hpt)
        simp [hq, hpq]

private theorem coeff_eq_zero_of_mem_aperySocle_of_not_index
    (x : AperyArtin k D i) (hx : x ∈ AperySocle (k := k) D i)
    (p : D.AperyIndex i)
    (hp : ¬ ∀ j : Fin 3, ¬ D.IsApery i (p.1 + D.tail i j)) :
    x.coeff p = 0 := by
  push_neg at hp
  rcases hp with ⟨j, hpj⟩
  have hz := (mem_aperySocle_iff_tail_variables (k := k) D i x).1 hx j
  rw [← coeff_tail_mul (k := k) D i x p j hpj, hz]
  simp

/-- Ambient basis vector selected by an Apéry-socle index.-/
def aperySocleBasisVector (s : D.AperySocleIndex i) : AperyArtin k D i :=
  A (k := k) s.1.1 s.1.2

def aperySocleRootSet : Set (AperyArtin k D i) :=
  Set.range (aperySocleBasisVector (k := k) D i)

def aperySocleRootSpan : Submodule k (AperyArtin k D i) :=
  Submodule.span k (aperySocleRootSet (k := k) D i)

/-- The intrinsic Apéry socle is exactly the span of Apéry-socle basis
degrees.-/
theorem aperySocle_eq_rootSpan :
    AperySocle (k := k) D i = aperySocleRootSpan (k := k) D i := by
  apply le_antisymm
  · intro x hx
    rw [apery_basis_expansion (k := k) D i x]
    apply Submodule.sum_mem
    intro p hpSupport
    by_cases hp : ∀ j : Fin 3, ¬ D.IsApery i (p.1 + D.tail i j)
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨p, hp⟩, rfl⟩
    · have hc := coeff_eq_zero_of_mem_aperySocle_of_not_index
        (k := k) D i x hx p hp
      simp [hc]
  · apply Submodule.span_le.2
    rintro x ⟨s, rfl⟩
    exact (A_mem_aperySocle_iff (k := k) D i s.1).2 s.2

private def aperySocleBasisIndex (s : D.AperySocleIndex i) :
    D.AperyIndex i := s.1

private theorem aperySocleBasisIndex_injective :
    Function.Injective (aperySocleBasisIndex D i) := Subtype.val_injective

theorem aperySocleBasis_linearIndependent :
    LinearIndependent k (aperySocleBasisVector (k := k) D i) := by
  change LinearIndependent k
    ((AperyArtin.aperyBasis (k := k) (D := D) (i := i)) ∘
      aperySocleBasisIndex D i)
  exact (AperyArtin.aperyBasis (k := k) (D := D) (i := i)).linearIndependent.comp
    (aperySocleBasisIndex D i) (aperySocleBasisIndex_injective D i)

/-- The Apéry-socle basis indexed by pseudo-Frobenius degrees through the
exact combinatorial index equivalence.-/
noncomputable def aperySocleBasis :
    Module.Basis (D.AperySocleIndex i) k (AperySocle (k := k) D i) := by
  rw [aperySocle_eq_rootSpan (k := k) D i]
  exact Module.Basis.span (aperySocleBasis_linearIndependent (k := k) D i)

def aperyType : ℕ := Module.finrank k (AperySocle (k := k) D i)

theorem aperyType_eq_semigroupType :
    aperyType (k := k) D i = D.semigroupType := by
  rw [aperyType, ← pseudoFrobenius_card_eq_aperySocle_card D i,
    ← Module.finrank_eq_card_basis (aperySocleBasis (k := k) D i)]

/-- Locality of the genuine chosen-base quotient, transported across the
frozen Run20 algebra equivalence.-/
theorem chosenBaseIsLocalRing : IsLocalRing (ChosenBaseQuotient (k := k) D i) := by
  letI := aperyIsLocalRing (k := k) D i
  exact RingEquiv.isLocalRing (chosenBaseEquivApery (k := k) D i).symm.toRingEquiv

def chosenBaseAugmentationIdeal : Ideal (ChosenBaseQuotient (k := k) D i) :=
  (aperyAugmentationIdeal (k := k) D i).comap
    (chosenBaseEquivApery (k := k) D i).toRingHom

theorem chosenBaseMaximalIdeal_eq_augmentationIdeal :
    letI := chosenBaseIsLocalRing (k := k) D i
    IsLocalRing.maximalIdeal (ChosenBaseQuotient (k := k) D i) =
      chosenBaseAugmentationIdeal (k := k) D i := by
  letI := chosenBaseIsLocalRing (k := k) D i
  have hmax : (chosenBaseAugmentationIdeal (k := k) D i).IsMaximal :=
    (aperyAugmentationIdeal_isMaximal (k := k) D i).comap_bijective
      (chosenBaseEquivApery (k := k) D i).toRingHom
      (chosenBaseEquivApery (k := k) D i).bijective
  exact (IsLocalRing.eq_maximalIdeal hmax).symm

/-- Intrinsic chosen-base socle, using its own unique maximal ideal.-/
def ChosenBaseSocle : Submodule k (ChosenBaseQuotient (k := k) D i) := by
  letI := chosenBaseIsLocalRing (k := k) D i
  exact {
    carrier := {x | ∀ r ∈ IsLocalRing.maximalIdeal
      (ChosenBaseQuotient (k := k) D i), r * x = 0}
    zero_mem' := by simp
    add_mem' := by intro x y hx hy r hr; simp [mul_add, hx r hr, hy r hr]
    smul_mem' := by intro c x hx r hr; rw [mul_smul_comm, hx r hr, smul_zero]
  }

theorem mem_chosenBaseSocle_iff_equiv_mem_aperySocle
    (x : ChosenBaseQuotient (k := k) D i) :
    x ∈ ChosenBaseSocle (k := k) D i ↔
      chosenBaseEquivApery (k := k) D i x ∈ AperySocle (k := k) D i := by
  let E := chosenBaseEquivApery (k := k) D i
  letI := chosenBaseIsLocalRing (k := k) D i
  change (∀ r ∈ IsLocalRing.maximalIdeal
      (ChosenBaseQuotient (k := k) D i), r * x = 0) ↔
    (∀ r ∈ aperyAugmentationIdeal (k := k) D i, r * E x = 0)
  rw [chosenBaseMaximalIdeal_eq_augmentationIdeal (k := k) D i]
  constructor
  · intro hx r hr
    let q := E.symm r
    have hq : q ∈ chosenBaseAugmentationIdeal (k := k) D i := by
      simpa [q, E, chosenBaseAugmentationIdeal] using hr
    have hz := hx q hq
    have := congrArg E hz
    simpa [q, E] using this
  · intro hx r hr
    have hEr : E r ∈ aperyAugmentationIdeal (k := k) D i := hr
    have hz := hx (E r) hEr
    apply E.injective
    simpa [E] using hz

noncomputable def chosenBaseSocleEquivAperySocle :
    ChosenBaseSocle (k := k) D i ≃ₗ[k] AperySocle (k := k) D i where
  toFun x := ⟨chosenBaseEquivApery (k := k) D i x.1,
    (mem_chosenBaseSocle_iff_equiv_mem_aperySocle (k := k) D i x.1).1 x.2⟩
  invFun y := ⟨(chosenBaseEquivApery (k := k) D i).symm y.1,
    (mem_chosenBaseSocle_iff_equiv_mem_aperySocle (k := k) D i _).2
      (by simpa using y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

def chosenBaseType : ℕ :=
  Module.finrank k (ChosenBaseSocle (k := k) D i)

/-- Main Run21 theorem: the genuine chosen-base quotient has algebraic type
equal to the numerical-semigroup pseudo-Frobenius type.-/
theorem chosenBaseType_eq_semigroupType :
    chosenBaseType (k := k) D i = D.semigroupType := by
  rw [chosenBaseType,
    (chosenBaseSocleEquivAperySocle (k := k) D i).finrank_eq,
    ← aperyType, aperyType_eq_semigroupType (k := k) D i]

theorem chosenBaseType_eq_three_iff :
    chosenBaseType (k := k) D i = 3 ↔ D.semigroupType = 3 := by
  rw [chosenBaseType_eq_semigroupType (k := k) D i]

/-- Scope-explicit Run21 type bridge.  It contains no trace, NG, or Betti
statement.-/
structure ChosenBaseTypeBridge : Prop where
  pfFinite : Finite D.PseudoFrobeniusIndex
  pfAperyEquiv : Nonempty (D.PseudoFrobeniusIndex ≃ D.AperySocleIndex i)
  aperyLocal : IsLocalRing (AperyArtin k D i)
  aperyTypeExact : aperyType (k := k) D i = D.semigroupType
  chosenBaseLocal : IsLocalRing (ChosenBaseQuotient (k := k) D i)
  chosenBaseTypeExact : chosenBaseType (k := k) D i = D.semigroupType

def chosenBaseTypeBridge : ChosenBaseTypeBridge (k := k) D i where
  pfFinite := inferInstance
  pfAperyEquiv := ⟨D.pseudoFrobeniusEquivAperySocle i⟩
  aperyLocal := aperyIsLocalRing (k := k) D i
  aperyTypeExact := aperyType_eq_semigroupType (k := k) D i
  chosenBaseLocal := chosenBaseIsLocalRing (k := k) D i
  chosenBaseTypeExact := chosenBaseType_eq_semigroupType (k := k) D i

end

end P23.Semigroup
