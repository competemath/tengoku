import Tengoku.Hellingerrepolean4.Hellinger.FiniteInformation
import Tengoku.Hellingerrepolean4.Hellinger.TranslationInformation
import Tengoku.Hellingerrepolean4.Hellinger.ClassInformation
import Tengoku.Hellingerrepolean4.Hellinger.FourPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The manuscript information theorems for genuine KL mutual information of
Boolean outputs of uniform-input product binary symmetric channels. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.ProbabilityContracts
open PaperSpecs FiniteInformation

/-- The biased entropy transfer stated for the actual BSC probability model.
@isnad1 id=le.3h3v.s6.b6ce2f4f31b5 from=translated src=- shape=751380ee vocab=f12bdd30
-/
theorem entropy_transfer {n : ℕ} (f : Cube n → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hH : HellingerBound f ρ hρ) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) :=
  bscMutualInformation_le_of_hellinger f hf ρ hρ hH

/-- The information bound for every nonempty sign-reversing translation, with
exactly the signed dictators on the reversed coordinate set as interior-noise
maximizers.
@isnad1 id=and.4h4v.s7.f7c1b4d56747 from=translated src=- shape=09434dd5 vocab=699ca9b3
-/
theorem translation_information (n : ℕ) (f : Cube n → ℝ) (hf : IsBoolean f)
    (S : Finset (Fin n)) (hS : S.Nonempty) (hs : SignReversing f S)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → ρ < 1 →
        (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
          SignedDictatorOn f S)) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact TranslationInformation.translation_information n f hf S hS hs ρ hρ

/-- Every positive-dimensional bent Boolean function has strictly smaller
information than a dictator whenever the channel has positive correlation.
@isnad1 id=and.4h3v.s7.5ac432e567c8 from=translated src=- shape=dbdd1cff vocab=de567cb2
-/
theorem bent_information (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → bscMutualInformation f ρ hρ < 1 - binaryEntropyBits ((1 - ρ) / 2)) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact ClassInformation.bent_information n hn f hf hb ρ hρ

/-- All positive-dimensional quadratic Boolean phases satisfy the information
bound, and their interior-noise maximizers are exactly the signed dictators.
@isnad1 id=and.3h3v.s7.46e5dee8fa6c from=translated src=- shape=5fe43170 vocab=9447bcc6
-/
theorem quadratic_information (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ)
    (hq : IsQuadratic f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) ∧
      (0 < ρ → ρ < 1 →
        (bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2) ↔
          SignedDictatorOn f Finset.univ)) := by
  rw [bscMutualInformation_eq_posteriorInformation f (ClassInformation.quadratic_isBoolean hq)]
  exact ClassInformation.quadratic_information n hn f hq ρ hρ

/--
@isnad1 id=lt.3h3v.s7.b4b11506cde4 from=translated src=- shape=e1eae687 vocab=8185e99d
-/
theorem strict_entropy_transfer {n : ℕ} (f : Cube n → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hH : objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) :
    bscMutualInformation f ρ hρ < 1 - binaryEntropyBits ((1 - ρ) / 2) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact EntropyTransfer.strict_hellinger_implies_strict_ck f hf ρ hρ hH

/--
@isnad1 id=eq.4h3v.s7.0c92561d1b13 from=translated src=- shape=93641e50 vocab=3dee4add
-/
theorem information_equality_implies_hellinger_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : IsBoolean f) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hH : HellingerBound f ρ hρ)
    (hI : bscMutualInformation f ρ hρ = 1 - binaryEntropyBits ((1 - ρ) / 2)) :
    objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ := by
  rw [bscMutualInformation_eq_posteriorInformation f hf] at hI
  exact EntropyTransfer.ck_equality_implies_hellinger_equality f hf ρ hρ hH hI

/--
@isnad1 id=eq.1h4v.s6.559d97ec9f17 from=translated src=- shape=eb12c99f vocab=465e1106
-/
theorem signed_dictator_information (n : ℕ) (i : Fin n) (negative : Bool)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    bscMutualInformation
      (fun x : Cube n => if negative then -boolSign (x i) else boolSign (x i)) ρ hρ =
        1 - binaryEntropyBits ((1 - ρ) / 2) := by
  have hf : IsBoolean
      (fun x : Cube n => if negative then -boolSign (x i) else boolSign (x i)) := by
    intro x
    cases negative <;> cases hx : x i <;> norm_num [boolSign, hx]
  rw [bscMutualInformation_eq_posteriorInformation _ hf]
  exact EntropyTransfer.signed_dictator_information n i negative ρ hρ

/-- The exceptional-four-point class also satisfies the bound for actual
Boolean-output mutual information.
@isnad1 id=and.10h5v.s9.30616ca089a4 from=translated src=- shape=a93fc272 vocab=f1b1e73a
-/
theorem four_point_information (n : ℕ) (f : Cube n → ℝ)
    (hf : IsBoolean f) (hmean : mean f = 0) (x y : Cube n)
    (hyx : y ≠ x) (hyax : y ≠ antipode n x)
    (hfx : f x = 1) (hfax : f (antipode n x) = 1)
    (hfy : f y = -1) (hfay : f (antipode n y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y →
      f (antipode n z) = -f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    HellingerBound f ρ hρ ∧
      bscMutualInformation f ρ hρ ≤ 1 - binaryEntropyBits ((1 - ρ) / 2) := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  exact FourPoint.four_point_bounds n f hf hmean x y hyx hyax hfx hfax hfy hfay hother ρ hρ

/-- The zero-dimensional quotient channel is the identity on its singleton
input space.
@isnad1 id=eq.1h2v.s6.7088a0d768a1 from=translated src=- shape=0672b8c9 vocab=27c2596a
-/
theorem zero_dimension_noise (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : (cubeBSC 0 ρ hρ).apply f = f := by
  funext y
  calc
    _ = ∑ x : Cube 0, (cubeBSC 0 ρ hρ).weight y x * f y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Subsingleton.elim x y]
    _ = f y := by rw [← Finset.sum_mul, UniformChannel.row_sum, one_mul]

/--
@isnad1 id=eq.1h2v.s7.94dd77e58561 from=translated src=- shape=cd76652b vocab=6cb6da91
-/
theorem zero_dimension_objective (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : objective ((cubeBSC 0 ρ hρ).apply f) = 0 := by
  rw [zero_dimension_noise]
  have hc : f = fun _ => f default := by
    funext x
    exact congrArg f (Subsingleton.elim x default)
  rw [hc]
  simp only [objective, mean_const, sub_self]

/--
@isnad1 id=eq.2h2v.s5.1a9b66aaeffd from=translated src=- shape=a8b32ab3 vocab=c8988395
-/
theorem zero_dimension_information (f : Cube 0 → ℝ) (hf : IsBoolean f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : bscMutualInformation f ρ hρ = 0 := by
  rw [bscMutualInformation_eq_posteriorInformation f hf]
  unfold posteriorInformation
  rw [zero_dimension_noise]
  have hc : f = fun _ => f default := by
    funext x
    exact congrArg f (Subsingleton.elim x default)
  rw [hc]
  simp only [mean_const, sub_self]

/--
@isnad1 id=lt.2h2v.s7.24901735d8f2 from=translated src=- shape=1c927c42 vocab=0aa9840a
-/
theorem zero_dimension_strict_hellinger (f : Cube 0 → ℝ)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hp : 0 < ρ) :
    objective ((cubeBSC 0 ρ hρ).apply f) < 1 - root ρ := by
  rw [zero_dimension_objective]
  have hr : root ρ < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by nlinarith)
  linarith

end Hellinger.ProbabilityContracts
