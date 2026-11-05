import Tengoku.NsP23.P23.Semigroup.NearlyGorenstein
import Tengoku.NsP23.P23.Semigroup.ChosenBaseType
import Tengoku.Seed.LinearAlgebra.Dual.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical dual, reflection maps, and ordinary trace of the Apéry algebra
-/

namespace P23.Semigroup

noncomputable section

set_option maxHeartbeats 800000

open FourGeneratedNumericalSemigroup AperyArtin

variable {k : Type*} [Field k]
variable (D : FourGeneratedNumericalSemigroup) (i : Fin 4)

/-- The intrinsic canonical dual of the finite Apéry algebra.-/
abbrev AperyOmega (k : Type*) [Field k]
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4) :=
  Module.Dual k (AperyArtin k D i)

namespace AperyOmega

variable {D i}

/-- Intrinsic contragredient action.-/
def act (a : AperyArtin k D i) (φ : AperyOmega k D i) : AperyOmega k D i where
  toFun x := φ (a * x)
  map_add' x y := by simp [mul_add]
  map_smul' r x := by simp [mul_smul_comm]

instance : SMul (AperyArtin k D i) (AperyOmega k D i) := ⟨act⟩

@[simp] theorem smul_apply (a : AperyArtin k D i) (φ : AperyOmega k D i)
    (x : AperyArtin k D i) : (a • φ) x = φ (a * x) := rfl

instance : Module (AperyArtin k D i) (AperyOmega k D i) where
  one_smul φ := by ext x; simp
  mul_smul a b φ := by ext x; simp [mul_assoc, mul_left_comm]
  smul_zero a := by ext x; simp
  smul_add a φ ψ := by ext x; simp
  zero_smul φ := by ext x; simp
  add_smul a b φ := by ext x; simp [add_mul]

instance : IsScalarTower k (AperyArtin k D i) (AperyOmega k D i) where
  smul_assoc r a φ := by
    ext x
    change φ ((r • a) * x) = r • φ (a * x)
    rw [Algebra.smul_mul_assoc]
    exact φ.map_smul r (a * x)

end AperyOmega

/-- The Kronecker dual basis to the frozen Apéry basis.-/
noncomputable def aperyDualBasis :
    Module.Basis (D.AperyIndex i) k (AperyOmega k D i) :=
  (aperyBasis (k := k) (D := D) (i := i)).dualBasis

@[simp] theorem aperyBasis_apply (p : D.AperyIndex i) :
    aperyBasis (k := k) (D := D) (i := i) p =
      A (k := k) p.1 p.2 := by
  rfl

/-- Kronecker dual at an Apéry degree.-/
def AU (p : D.AperyIndex i) : AperyOmega k D i :=
  aperyDualBasis (k := k) D i p

@[simp] theorem AU_apply_A (p q : D.AperyIndex i) :
    AU (k := k) D i p (A (k := k) q.1 q.2) =
      if p = q then 1 else 0 := by
  rw [← aperyBasis_apply (k := k) D i q]
  simpa [AU, aperyDualBasis] using
    (Module.Basis.dualBasis_apply_self
      (aperyBasis (k := k) (D := D) (i := i)) p q).trans
        (by simp [eq_comm])

/-- Exact coefficient formula for a basis monomial acting on an Apéry dual
basis vector.-/
theorem A_smul_AU_apply_A (h p q : D.AperyIndex i) :
    (A (k := k) h.1 h.2 • AU (k := k) D i p)
        (A (k := k) q.1 q.2) =
      if h.1 + q.1 = p.1 then 1 else 0 := by
  classical
  rw [AperyOmega.smul_apply, A_mul_A]
  by_cases hhq : D.IsApery i (h.1 + q.1)
  · rw [dite_eq_left hhq]
    let t : D.AperyIndex i := ⟨h.1 + q.1, hhq⟩
    change AU (k := k) D i p (A (k := k) t.1 t.2) = _
    rw [AU_apply_A]
    simp [t, Subtype.ext_iff, eq_comm]
  · have hne : h.1 + q.1 ≠ p.1 := by
      intro he
      apply hhq
      simpa [he] using p.2
    simp [hhq, hne]

/-- Exact action when an Apéry predecessor exists.-/
theorem A_smul_AU_eq_AU (h p q : D.AperyIndex i)
    (hp : h.1 + q.1 = p.1) :
    A (k := k) h.1 h.2 • AU (k := k) D i p = AU (k := k) D i q := by
  apply (aperyBasis (k := k) (D := D) (i := i)).ext
  intro r
  simp only [aperyBasis_apply]
  rw [A_smul_AU_apply_A, AU_apply_A]
  have hiff : h.1 + r.1 = p.1 ↔ r = q := by
    constructor
    · intro hr
      apply Subtype.ext
      exact add_left_cancel (hr.trans hp.symm)
    · rintro rfl
      exact hp
  simp [hiff, eq_comm]

/-- Exact zero action when no Apéry predecessor exists.-/
theorem A_smul_AU_eq_zero (h p : D.AperyIndex i)
    (hn : ¬ ∃ q : D.AperyIndex i, h.1 + q.1 = p.1) :
    A (k := k) h.1 h.2 • AU (k := k) D i p = 0 := by
  apply (aperyBasis (k := k) (D := D) (i := i)).ext
  intro q
  simp only [aperyBasis_apply]
  rw [A_smul_AU_apply_A]
  have hne : h.1 + q.1 ≠ p.1 := fun he => hn ⟨q, he⟩
  simp [hne]

/-- Every Apéry degree lies below an Apéry-socle degree.  The construction is
symbolic well-founded induction on the remaining uniform degree bound.-/
theorem exists_aperySocle_above (p : D.AperyIndex i) :
    ∃ s : D.AperySocleIndex i, ∃ h : D.Gamma,
      s.1.1 = p.1 + h := by
  let B := D.conductor + D.n i
  let rec go (p : D.AperyIndex i) :
      ∃ s : D.AperySocleIndex i, ∃ h : D.Gamma,
        s.1.1 = p.1 + h := by
    by_cases hp : ∀ j : Fin 3, ¬ D.IsApery i (p.1 + D.tail i j)
    · exact ⟨⟨p, hp⟩, 0, by simp⟩
    · push_neg at hp
      rcases hp with ⟨j, hpj⟩
      let p' : D.AperyIndex i := ⟨p.1 + D.tail i j, hpj⟩
      have hpBound : p.1.1 < B := D.isApery_lt i p.2
      have hp'Bound : p'.1.1 < B := D.isApery_lt i p'.2
      have htail : 0 < (D.tail i j).1 := D.tailGen_positive i j
      rcases go p' with ⟨s, h, hs⟩
      refine ⟨s, D.tail i j + h, ?_⟩
      rw [hs]
      simp only [p']
      ac_rfl
  termination_by D.conductor + D.n i - p.1.1
  decreasing_by
    simp only [p', AddSubmonoid.coe_add]
    omega
  exact go p

/-- An integer center reflecting every Apéry-socle degree into `Gamma`.-/
def IsAperyReflectionCenter (C : ℤ) : Prop :=
  ∀ s : D.AperySocleIndex i,
    IntInGamma D (C - (s.1.1.1 : ℤ))

/-- A center admissible on socle degrees is admissible on every Apéry degree.
The proof extends the degree to a socle degree and adds back the extension.-/
theorem reflectionCenter_all_apery {C : ℤ}
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) :
    IntInGamma D (C - (p.1.1 : ℤ)) := by
  rcases exists_aperySocle_above D i p with ⟨s, h, hs⟩
  have hh : IntInGamma D (h.1 : ℤ) :=
    (D.intInGamma_natCast h.1).2 h.2
  have hadd := D.intInGamma_add (hC s) hh
  convert hadd using 1
  have hsv := congrArg Subtype.val hs
  simp only [AddSubmonoid.coe_add] at hsv
  omega

/-- The genuine semigroup degree representing the reflected integer `C-p`.-/
noncomputable def reflectionGamma (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) : D.Gamma :=
  Classical.choose (reflectionCenter_all_apery D i hC p)

@[simp] theorem reflectionGamma_val (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) :
    ((reflectionGamma D i C hC p).1 : ℤ) = C - (p.1.1 : ℤ) :=
  Classical.choose_spec (reflectionCenter_all_apery D i hC p)

/-- The reflected semigroup monomial, truncated only if its genuine reflected
degree lies outside the Apéry set.-/
noncomputable def reflectionMonomial (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) :
    AperyArtin k D i :=
  truncatedAperyMonomial (k := k) D i (reflectionGamma D i C hC p)

/-- The `k`-linear reflection map, specified on the intrinsic Apéry dual
basis.-/
noncomputable def reflectionLinearMap (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) :
    AperyOmega k D i →ₗ[k] AperyArtin k D i :=
  (aperyDualBasis (k := k) D i).constr k
    (fun p => reflectionMonomial (k := k) D i C hC p)

@[simp] theorem reflectionLinearMap_AU (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) :
    reflectionLinearMap (k := k) D i C hC (AU (k := k) D i p) =
      reflectionMonomial (k := k) D i C hC p := by
  exact Module.Basis.constr_basis (aperyDualBasis (k := k) D i) k
    (fun q => reflectionMonomial (k := k) D i C hC q) p

private def dualBasisSmulLinearMap (h : D.AperyIndex i) :
    AperyOmega k D i →ₗ[k] AperyOmega k D i where
  toFun φ := A (k := k) h.1 h.2 • φ
  map_add' φ ψ := by simp
  map_smul' r φ := by ext x; rfl

private def basisMulLinearMap (h : D.AperyIndex i) :
    AperyArtin k D i →ₗ[k] AperyArtin k D i where
  toFun x := A (k := k) h.1 h.2 * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := by simp [mul_smul_comm]

/-- The reflection identity for one algebra basis vector and one dual basis
vector.  The zero branch is the load-bearing socle-extension argument.-/
private theorem reflection_basis_identity (C : ℤ)
    (hC : IsAperyReflectionCenter D i C)
    (h p : D.AperyIndex i) :
    reflectionLinearMap (k := k) D i C hC
        (A (k := k) h.1 h.2 • AU (k := k) D i p) =
      A (k := k) h.1 h.2 *
        reflectionMonomial (k := k) D i C hC p := by
  classical
  by_cases hpred : ∃ q : D.AperyIndex i, h.1 + q.1 = p.1
  · rcases hpred with ⟨q, hq⟩
    rw [A_smul_AU_eq_AU (k := k) D i h p q hq,
      reflectionLinearMap_AU]
    have hAh : truncatedAperyMonomial (k := k) D i h.1 =
        A (k := k) h.1 h.2 := by
      simp [truncatedAperyMonomial, h.2]
    rw [← hAh]
    simp only [reflectionMonomial]
    rw [← truncatedAperyMonomial_add]
    congr 2
    apply Subtype.ext
    have hpq := congrArg Subtype.val hq
    have hrp := reflectionGamma_val D i C hC p
    have hrq := reflectionGamma_val D i C hC q
    simp only [AddSubmonoid.coe_add] at hpq ⊢
    exact_mod_cast (show
      ((reflectionGamma D i C hC q).1 : ℤ) =
        (h.1.1 : ℤ) + (reflectionGamma D i C hC p).1 by omega)
  · rw [A_smul_AU_eq_zero (k := k) D i h p hpred, map_zero]
    have hnot : ¬ D.IsApery i
        (h.1 + reflectionGamma D i C hC p) := by
      intro hsurv
      let t : D.AperyIndex i :=
        ⟨h.1 + reflectionGamma D i C hC p, hsurv⟩
      rcases exists_aperySocle_above D i t with ⟨s, v, hsv⟩
      rcases hC s with ⟨c, hc⟩
      let d : D.Gamma := c + v
      have hsum : h.1 + d = p.1 := by
        apply Subtype.ext
        have hsv' := congrArg Subtype.val hsv
        have hrp := reflectionGamma_val D i C hC p
        simp only [t, AddSubmonoid.coe_add] at hsv' ⊢
        change (c.1 : ℤ) = C - (s.1.1.1 : ℤ) at hc
        exact_mod_cast (show
          (h.1.1 : ℤ) + ((d.1 : ℕ) : ℤ) = (p.1.1 : ℤ) by
            simp only [d, AddSubmonoid.coe_add]
            omega)
      have hdA : D.IsApery i d := by
        apply isApery_of_add_right
        rw [hsum]
        exact p.2
      exact hpred ⟨⟨d, hdA⟩, hsum⟩
    have hAh : truncatedAperyMonomial (k := k) D i h.1 =
        A (k := k) h.1 h.2 := by
      simp [truncatedAperyMonomial, h.2]
    rw [← hAh]
    simp only [reflectionMonomial]
    rw [← truncatedAperyMonomial_add]
    simp [truncatedAperyMonomial, hnot]

/-- Reflection commutes with multiplication by one Apéry basis monomial.-/
private theorem reflection_basis_smul (C : ℤ)
    (hC : IsAperyReflectionCenter D i C)
    (h : D.AperyIndex i) (φ : AperyOmega k D i) :
    reflectionLinearMap (k := k) D i C hC
        (A (k := k) h.1 h.2 • φ) =
      A (k := k) h.1 h.2 *
        reflectionLinearMap (k := k) D i C hC φ := by
  let L : AperyOmega k D i →ₗ[k] AperyArtin k D i :=
    (reflectionLinearMap (k := k) D i C hC).comp
      (dualBasisSmulLinearMap (k := k) D i h)
  let R : AperyOmega k D i →ₗ[k] AperyArtin k D i :=
    (basisMulLinearMap (k := k) D i h).comp
      (reflectionLinearMap (k := k) D i C hC)
  have heq : L = R := (aperyDualBasis (k := k) D i).ext fun p => by
    change reflectionLinearMap (k := k) D i C hC
        (A (k := k) h.1 h.2 • AU (k := k) D i p) =
      A (k := k) h.1 h.2 *
        reflectionLinearMap (k := k) D i C hC (AU (k := k) D i p)
    rw [reflectionLinearMap_AU]
    exact reflection_basis_identity (k := k) D i C hC h p
  exact LinearMap.congr_fun heq φ

/-- The reflection map is linear over the full Apéry algebra.-/
theorem reflectionLinearMap_map_smul (C : ℤ)
    (hC : IsAperyReflectionCenter D i C)
    (a : AperyArtin k D i) (φ : AperyOmega k D i) :
    reflectionLinearMap (k := k) D i C hC (a • φ) =
      a * reflectionLinearMap (k := k) D i C hC φ := by
  induction a using AperyArtin.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_smul, add_mul, ha, hb]
  | single p r =>
      rw [← smul_A (k := k) r p.1 p.2, smul_assoc,
        map_smul, reflection_basis_smul (k := k) D i C hC p,
        smul_mul_assoc]

/-- The reflection map as an intrinsic canonical homomorphism.-/
noncomputable def reflectionCanonicalHom (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) :
    AperyOmega k D i →ₗ[AperyArtin k D i] AperyArtin k D i where
  toFun := reflectionLinearMap (k := k) D i C hC
  map_add' φ ψ := by simp
  map_smul' a φ := reflectionLinearMap_map_smul (k := k) D i C hC a φ

@[simp] theorem reflectionCanonicalHom_AU (C : ℤ)
    (hC : IsAperyReflectionCenter D i C) (p : D.AperyIndex i) :
    reflectionCanonicalHom (k := k) D i C hC (AU (k := k) D i p) =
      reflectionMonomial (k := k) D i C hC p :=
  reflectionLinearMap_AU (k := k) D i C hC p

/-- Public Run22 value wrapper for the frozen PF/Apéry-socle equivalence.-/
theorem pseudoFrobeniusEquivAperySocle_val
    (f : D.PseudoFrobeniusIndex) :
    ((((D.pseudoFrobeniusEquivAperySocle i) f).1.1.1 : ℕ) : ℤ) =
      f.1 + D.n i := by
  simp only [FourGeneratedNumericalSemigroup.pseudoFrobeniusEquivAperySocle]
  exact Classical.choose_spec
    ((D.isPseudoFrobenius_iff_generators f.1).1 f.2 |>.2 i)

/-- The reflection center selected by a tail NG witness.-/
def tailReflectionCenter (j : Fin 3) (f : D.PseudoFrobeniusIndex) : ℤ :=
  (D.tailGen i j : ℤ) + f.1 + D.n i

/-- A tail NG witness makes its selected reflection center admissible on all
Apéry-socle degrees.-/
theorem tail_ngWitness_reflectionCenter (j : Fin 3)
    (f : D.PseudoFrobeniusIndex)
    (hf : NGWitnessForGenerator D (D.tailIndex i j) f) :
    IsAperyReflectionCenter D i (tailReflectionCenter D i j f) := by
  intro s
  let g : D.PseudoFrobeniusIndex :=
    (D.pseudoFrobeniusEquivAperySocle i).symm s
  have hgval := pseudoFrobeniusEquivAperySocle_val D i g
  have hgs : (D.pseudoFrobeniusEquivAperySocle i) g = s := by
    exact (D.pseudoFrobeniusEquivAperySocle i).apply_symm_apply s
  have hsval : ((s.1.1.1 : ℕ) : ℤ) = g.1 + D.n i := by
    rw [← hgs]
    exact hgval
  have hw := hf g
  convert hw using 1
  simp only [tailReflectionCenter, FourGeneratedNumericalSemigroup.tailGen]
  omega

/-- For the witness-selected center, the chosen PF root dual maps exactly to
the chosen tail variable.-/
theorem reflectionCanonicalHom_AU_pf_eq_tailVariableA (j : Fin 3)
    (f : D.PseudoFrobeniusIndex)
    (hf : NGWitnessForGenerator D (D.tailIndex i j) f) :
    let C := tailReflectionCenter D i j f
    let hC := tail_ngWitness_reflectionCenter D i j f hf
    reflectionCanonicalHom (k := k) D i C hC
        (AU (k := k) D i ((D.pseudoFrobeniusEquivAperySocle i) f).1) =
      tailVariableA (k := k) D i j := by
  dsimp only
  rw [reflectionCanonicalHom_AU]
  have href : reflectionGamma D i (tailReflectionCenter D i j f)
      (tail_ngWitness_reflectionCenter D i j f hf)
      ((D.pseudoFrobeniusEquivAperySocle i f).1) = D.tail i j := by
    apply Subtype.ext
    have hv := reflectionGamma_val D i (tailReflectionCenter D i j f)
      (tail_ngWitness_reflectionCenter D i j f hf)
      ((D.pseudoFrobeniusEquivAperySocle i) f).1
    have hs := pseudoFrobeniusEquivAperySocle_val D i f
    have hv' :
        ((reflectionGamma D i (tailReflectionCenter D i j f)
          (tail_ngWitness_reflectionCenter D i j f hf)
          ((D.pseudoFrobeniusEquivAperySocle i) f).1).1 : ℤ) =
            D.n (D.tailIndex i j) := by
      calc
        _ = (D.n (D.tailIndex i j) : ℤ) + f.1 + D.n i -
            ((((D.pseudoFrobeniusEquivAperySocle i) f).1.1.1 : ℕ) : ℤ) := by
              simpa [tailReflectionCenter,
                FourGeneratedNumericalSemigroup.tailGen] using hv
        _ = D.n (D.tailIndex i j) := by rw [hs]; omega
    simp only [
      FourGeneratedNumericalSemigroup.tailGen,
      FourGeneratedNumericalSemigroup.tail,
      FourGeneratedNumericalSemigroup.generator] at hv ⊢
    exact_mod_cast hv'
  simp [reflectionMonomial, href, truncatedAperyMonomial,
    D.tail_isApery i j, tailVariableA]

/-- Ordinary trace of the intrinsic Apéry canonical dual.-/
def AperyTraceSubmodule :
    Submodule (AperyArtin k D i) (AperyArtin k D i) :=
  ⨆ F : AperyOmega k D i →ₗ[AperyArtin k D i] AperyArtin k D i,
    F.range

theorem aperyTrace_range_le
    (F : AperyOmega k D i →ₗ[AperyArtin k D i] AperyArtin k D i) :
    F.range ≤ AperyTraceSubmodule (k := k) D i :=
  le_iSup (fun G : AperyOmega k D i →ₗ[AperyArtin k D i]
    AperyArtin k D i => G.range) F

/-- Every tail variable belongs to ordinary Apéry trace under the semigroup
NG-vector hypothesis.-/
theorem tailVariableA_mem_aperyTrace
    (hng : SemigroupNearlyGorenstein D) (j : Fin 3) :
    tailVariableA (k := k) D i j ∈ AperyTraceSubmodule (k := k) D i := by
  rcases exists_tail_ngWitness D hng i j with ⟨f, hf⟩
  let C := tailReflectionCenter D i j f
  let hC := tail_ngWitness_reflectionCenter D i j f hf
  let F := reflectionCanonicalHom (k := k) D i C hC
  apply aperyTrace_range_le (k := k) D i F
  refine ⟨AU (k := k) D i ((D.pseudoFrobeniusEquivAperySocle i) f).1, ?_⟩
  exact reflectionCanonicalHom_AU_pf_eq_tailVariableA
    (k := k) D i j f hf

/-- Intrinsic nearly-Gorenstein condition for the finite Apéry algebra.-/
def AperyNearlyGorenstein : Prop :=
  aperyAugmentationIdeal (k := k) D i ≤ AperyTraceSubmodule (k := k) D i

/-- Main Apéry bridge: the standard PF NG-vector criterion puts the full
augmentation ideal in the ordinary canonical-dual trace.-/
theorem semigroupNearlyGorenstein_to_aperyNearlyGorenstein
    (hng : SemigroupNearlyGorenstein D) :
    AperyNearlyGorenstein (k := k) D i := by
  rw [AperyNearlyGorenstein, aperyAugmentationIdeal_eq_tailVariableIdeal,
    tailVariableIdeal, Ideal.span_le]
  rintro x ⟨j, rfl⟩
  exact tailVariableA_mem_aperyTrace (k := k) D i hng j

end

end P23.Semigroup
