import Tengoku.PaperCLean.PaperCV282.MassPushforward
import Tengoku.Seed.Data.Finsupp.Basic
import Tengoku.Seed.Data.Finsupp.Encodable
import Tengoku.Seed.MeasureTheory.Constructions.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact reindexing from excess marks to moving integer levels

All labels, including position and sign, are retained. This is a bijection
of finite configurations and therefore preserves half-L1 total variation
exactly. It introduces no approximation or probabilistic input.
-/
namespace PaperC.V282.MovingMarkedLevels

open FiniteFieldTotalVariation MassPushforward MeasureTheory

noncomputable section

/-- The retained levels start at minus the depth.-/
def MovingLevel (d : ℕ) := {r : ℤ // -(d : ℤ) ≤ r}

/--
@isnad1 id=countabl.0h1v.s2.1cf8ce9971ac from=translated src=- shape=76a08d12 vocab=2f4c3d7f
-/
instance instCountableMovingLevel (d : ℕ) : Countable (MovingLevel d) :=
  inferInstanceAs (Countable {r : ℤ // -(d : ℤ) ≤ r})

/-- An excess e represents the integer level e-d.-/
def levelEquiv (d : ℕ) : ℕ ≃ MovingLevel d where
  toFun e := ⟨(e : ℤ)-d, by omega⟩
  invFun r := (r.val+d).toNat
  left_inv e := by simp
  right_inv r := by
    apply Subtype.ext
    have hr := r.property
    dsimp
    rw [Int.toNat_of_nonneg (by omega)]
    omega

/--
@isnad1 id=eq.0h2v.s5.6e840ee0172a from=translated src=- shape=a7ef6b94 vocab=f7b4e838
-/
theorem levelEquiv_val (d e : ℕ) : ((levelEquiv d e).val : ℤ) = (e : ℤ)-d := rfl

/--
@isnad1 id=eq.0h2v.s6.2f18893eeaff from=translated src=- shape=988bd85b vocab=ebbe8cfc
-/
theorem levelEquiv_symm_val (d : ℕ) (r : MovingLevel d) :
    ((levelEquiv d).symm r : ℤ) = r.val+d := by
  exact Int.toNat_of_nonneg (by have := r.property; omega)

/-- The physical run length is unchanged by moving-level notation.
@isnad1 id=eq.1h3v.s6.50fdbe5dd53a from=translated src=- shape=2e8c9ea3 vocab=92b5623b
-/
theorem runLength_eq (b d e : ℕ) (hd : d ≤ b) :
    ((b-d+e : ℕ) : ℤ) = (b : ℤ)+(levelEquiv d e).val := by
  rw [levelEquiv_val]
  omega

/-- Retain both the position and the sign while changing the excess coordinate.-/
def labelledLevelEquiv (α σ : Type*) (d : ℕ) :
    α × (ℕ × σ) ≃ α × (MovingLevel d × σ) :=
  Equiv.prodCongr (Equiv.refl α) (Equiv.prodCongr (levelEquiv d) (Equiv.refl σ))

/-- Reindex a finite configuration without aggregating any coordinate.-/
def configurationEquiv (α σ : Type*) (d : ℕ) :
    (α × (ℕ × σ) →₀ ℕ) ≃ (α × (MovingLevel d × σ) →₀ ℕ) :=
  Finsupp.equivCongrLeft (labelledLevelEquiv α σ d)

/--
@isnad1 id=eq.0h7v.s8.03c3a2d1c05c from=translated src=- shape=1265ed64 vocab=dcb8ecaf
-/
theorem configurationEquiv_apply (α σ : Type*) (d : ℕ)
    (c : α × (ℕ × σ) →₀ ℕ) (x : α) (e : ℕ) (s : σ) :
    configurationEquiv α σ d c (x,levelEquiv d e,s) = c (x,e,s) := by
  simp [configurationEquiv, Finsupp.equivCongrLeft_apply,
    Finsupp.equivMapDomain_apply, labelledLevelEquiv]

/-- Injective maps preserve singleton masses on their image.
@isnad1 id=eq.1h5v.s5.8cecf9b36d7e from=translated src=- shape=c67791c1 vocab=547f3735
-/
theorem pushforwardMass_injective_apply {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p : α → ℝ) (a : α) :
    pushforwardMass f p (f a) = p a := by
  classical
  rw [pushforwardMass_eq_restricted]
  simp only [hf.eq_iff]
  simp

/--
@isnad1 id=eq.1h5v.s5.e2fc28d738b0 from=translated src=- shape=c4952412 vocab=37c30584
-/
theorem pushforwardMass_zero_off_range {α β : Type*} (f : α → β) (p : α → ℝ)
    {b : β} (hb : b ∉ Set.range f) : pushforwardMass f p b = 0 := by
  classical
  rw [pushforwardMass_eq_restricted]
  have he : ∀ a, f a ≠ b := fun a h => hb ⟨a,h⟩
  simp [he]

/-- In particular, viewing a supported path as a full function loses no TV.
@isnad1 id=eq.1h5v.s5.fbd3a80303c3 from=translated src=- shape=ad2e5481 vocab=dcecc6a3
-/
theorem massTotalVariation_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p q : α → ℝ) :
    massTotalVariation (pushforwardMass f p) (pushforwardMass f q) =
      massTotalVariation p q := by
  unfold massTotalVariation
  congr 1
  have hs : Function.support (fun b => |pushforwardMass f p b-pushforwardMass f q b|) ⊆
      Set.range f := by
    intro b hb
    by_contra h
    have hp := pushforwardMass_zero_off_range f p h
    have hq := pushforwardMass_zero_off_range f q h
    simp [Function.mem_support,hp,hq] at hb
  have h := hf.tsum_eq hs
  simpa only [pushforwardMass_injective_apply f hf] using h.symm

/-- Countable configurations give a measurable bijection for any discrete sigma-algebras.
@isnad1 id=measurab.0h3v.s7.240050634cb6 from=translated src=- shape=abe28d98 vocab=c67dcf1a
-/
theorem measurable_configurationEquiv (α σ : Type*) [Countable α] [Countable σ]
    (d : ℕ) [MeasurableSpace (α × (ℕ × σ) →₀ ℕ)]
    [MeasurableSingletonClass (α × (ℕ × σ) →₀ ℕ)]
    [MeasurableSpace (α × (MovingLevel d × σ) →₀ ℕ)] :
    Measurable (configurationEquiv α σ d) := by
  exact measurable_of_countable _

/--
@isnad1 id=measurab.0h3v.s7.ec0430944f2a from=translated src=- shape=f5a33441 vocab=c7e15b16
-/
theorem measurable_configurationEquiv_symm (α σ : Type*) [Countable α] [Countable σ]
    (d : ℕ) [MeasurableSpace (α × (MovingLevel d × σ) →₀ ℕ)]
    [MeasurableSingletonClass (α × (MovingLevel d × σ) →₀ ℕ)]
    [MeasurableSpace (α × (ℕ × σ) →₀ ℕ)] :
    Measurable (configurationEquiv α σ d).symm := by
  exact measurable_of_countable _

end
end PaperC.V282.MovingMarkedLevels
