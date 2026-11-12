import Tengoku.Seed.Analysis.Analytic.ChangeOrigin
import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv
import Tengoku.Seed.RingTheory.Adjoin.Basic
import Tengoku.Seed.Topology.Order.Compact
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Restricted analytic boxes and finite exponential towers

This scratch module implements the representation layer used by the
restricted-analytic base and exponential-adjunction argument.  It contains no
finiteness or o-minimality hypothesis.

The tower is deliberately parameterized by an arbitrary real subalgebra of
functions.  A later Abel-specific module can use `restrictedExpressionBase`
with the Abel-jet functions as its `specialGenerators`, without changing any
of the level or analyticity lemmas proved here.
-/

set_option autoImplicit false

noncomputable section

namespace AbelFormalization

open Set

/-! ## Finite boxes -/

/-- The Euclidean coordinate space used for the bounded variables.-/
abbrev RestrictedBoxSpace (p : ℕ) := Fin p → ℝ

/-- A nondegenerate coordinate box.  Dimension zero is allowed and gives the
one-point space `Fin 0 → ℝ`.-/
structure RestrictedBox (p : ℕ) where
  lower : RestrictedBoxSpace p
  upper : RestrictedBoxSpace p
  lower_lt_upper : ∀ i, lower i < upper i

namespace RestrictedBox

variable {p : ℕ} (D : RestrictedBox p)

/-- The product of the open coordinate intervals.-/
def openBox : Set (RestrictedBoxSpace p) :=
  Set.univ.pi fun i ↦ Set.Ioo (D.lower i) (D.upper i)

/-- The product of the closed coordinate intervals.-/
def closedBox : Set (RestrictedBoxSpace p) :=
  Set.univ.pi fun i ↦ Set.Icc (D.lower i) (D.upper i)

/--
@isnad1 id=iff.0h3v.s5.97300b08a439 from=translated src=- shape=6372556b vocab=28290a0d
-/
@[simp]
theorem mem_openBox {w : RestrictedBoxSpace p} :
    w ∈ D.openBox ↔ ∀ i, D.lower i < w i ∧ w i < D.upper i := by
  simp [openBox]

/--
@isnad1 id=iff.0h3v.s5.d48980d34e85 from=translated src=- shape=6372556b vocab=650913ab
-/
@[simp]
theorem mem_closedBox {w : RestrictedBoxSpace p} :
    w ∈ D.closedBox ↔ ∀ i, D.lower i ≤ w i ∧ w i ≤ D.upper i := by
  simp only [closedBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]

/--
@isnad1 id=isopen.0h2v.s4.c7ba1b25e961 from=translated src=- shape=71337308 vocab=d2bab4db
-/
theorem isOpen_openBox : IsOpen D.openBox := by
  exact isOpen_set_pi Set.finite_univ fun i _ ↦ isOpen_Ioo

/--
@isnad1 id=iscompac.0h2v.s4.6361b40024ba from=translated src=- shape=71337308 vocab=424e8d63
-/
theorem isCompact_closedBox : IsCompact D.closedBox := by
  exact isCompact_univ_pi fun i ↦ isCompact_Icc

/--
@isnad1 id=isclosed.0h2v.s4.121d8bb19588 from=translated src=- shape=71337308 vocab=ce98bcde
-/
theorem isClosed_closedBox : IsClosed D.closedBox :=
  D.isCompact_closedBox.isClosed

/--
@isnad1 id=le.0h2v.s4.f850c931d834 from=translated src=- shape=78aadca9 vocab=bc918d25
-/
theorem openBox_subset_closedBox : D.openBox ⊆ D.closedBox := by
  intro w hw
  rw [D.mem_closedBox]
  rw [D.mem_openBox] at hw
  exact fun i ↦ ⟨(hw i).1.le, (hw i).2.le⟩

/--
@isnad1 id=nonempty.0h2v.s3.ae2a5b923740 from=translated src=- shape=71337308 vocab=5f00249d
-/
theorem openBox_nonempty : D.openBox.Nonempty := by
  refine ⟨fun i ↦ (D.lower i + D.upper i) / 2, ?_⟩
  rw [D.mem_openBox]
  intro i
  constructor <;> linarith [D.lower_lt_upper i]

/--
@isnad1 id=nonempty.0h2v.s3.f5f288d39a63 from=translated src=- shape=71337308 vocab=ca5df2bf
-/
theorem closedBox_nonempty : D.closedBox.Nonempty :=
  D.openBox_nonempty.mono D.openBox_subset_closedBox

/--
@isnad1 id=eq.0h1v.s4.b593113e2850 from=translated src=- shape=2fa031cc vocab=47b83a94
-/
@[simp]
theorem openBox_zero_eq_univ (D : RestrictedBox 0) : D.openBox = Set.univ := by
  ext w
  simp

/--
@isnad1 id=eq.0h1v.s4.c87107bea97e from=translated src=- shape=2fa031cc vocab=a107bcea
-/
@[simp]
theorem closedBox_zero_eq_univ (D : RestrictedBox 0) : D.closedBox = Set.univ := by
  ext w
  simp

/-! ## Functions analytic near the closed box -/

/-- A total representative which is analytic on some open neighborhood of
the closed box.  Its values away from that neighborhood are irrelevant.-/
def AnalyticNearClosedBox (f : RestrictedBoxSpace p → ℝ) : Prop :=
  ∃ U : Set (RestrictedBoxSpace p),
    IsOpen U ∧ D.closedBox ⊆ U ∧ AnalyticOnNhd ℝ f U

/-- Since the locus of analyticity is open, being analytic at every point of
the closed box is equivalent to having one open analytic neighborhood of it.
No compactness argument is needed for this equivalence.
@isnad1 id=iff.0h3v.s6.3086d0f6f839 from=translated src=- shape=3ef47b7d vocab=c26e336f
-/
theorem analyticNearClosedBox_iff {f : RestrictedBoxSpace p → ℝ} :
    D.AnalyticNearClosedBox f ↔ AnalyticOnNhd ℝ f D.closedBox := by
  constructor
  · rintro ⟨U, _, hDU, hf⟩
    exact hf.mono hDU
  · intro hf
    refine ⟨{w | AnalyticAt ℝ f w}, isOpen_analyticAt ℝ f, ?_, ?_⟩
    · exact fun w hw ↦ hf w hw
    · exact fun w hw ↦ hw

/--
@isnad1 id=analytic.0h3v.s3.90767bac01db from=translated src=- shape=69dac64e vocab=e8158f87
-/
theorem analyticNearClosedBox_const (c : ℝ) :
    D.AnalyticNearClosedBox (fun _ ↦ c) := by
  rw [D.analyticNearClosedBox_iff]
  exact analyticOnNhd_const

/--
@isnad1 id=analytic.0h2v.s4.50d406788c6e from=translated src=- shape=4687dfb6 vocab=e8158f87
-/
theorem analyticNearClosedBox_zero :
    D.AnalyticNearClosedBox (0 : RestrictedBoxSpace p → ℝ) := by
  change D.AnalyticNearClosedBox (fun _ ↦ 0)
  exact D.analyticNearClosedBox_const 0

/--
@isnad1 id=analytic.0h2v.s4.fbdc7cae6b4d from=translated src=- shape=4687dfb6 vocab=e8158f87
-/
theorem analyticNearClosedBox_one :
    D.AnalyticNearClosedBox (1 : RestrictedBoxSpace p → ℝ) := by
  change D.AnalyticNearClosedBox (fun _ ↦ 1)
  exact D.analyticNearClosedBox_const 1

/--
@isnad1 id=analytic.2h4v.s5.97795ee5c488 from=translated src=- shape=6fdb9f81 vocab=f51988a3
-/
theorem AnalyticNearClosedBox.add {f g : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f) (hg : D.AnalyticNearClosedBox g) :
    D.AnalyticNearClosedBox (f + g) := by
  rw [D.analyticNearClosedBox_iff] at hf hg ⊢
  exact hf.add hg

/--
@isnad1 id=analytic.2h4v.s5.19ac47ef62a7 from=translated src=- shape=6fdb9f81 vocab=bb6d4222
-/
theorem AnalyticNearClosedBox.mul {f g : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f) (hg : D.AnalyticNearClosedBox g) :
    D.AnalyticNearClosedBox (f * g) := by
  rw [D.analyticNearClosedBox_iff] at hf hg ⊢
  exact hf.mul hg

/--
@isnad1 id=analytic.1h3v.s5.494e4a5ef976 from=translated src=- shape=d5668c82 vocab=26c71139
-/
theorem AnalyticNearClosedBox.neg {f : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f) : D.AnalyticNearClosedBox (-f) := by
  rw [D.analyticNearClosedBox_iff] at hf ⊢
  exact hf.neg

/--
@isnad1 id=analytic.2h4v.s5.589be9af86c3 from=translated src=- shape=6fdb9f81 vocab=2a0ba0f6
-/
theorem AnalyticNearClosedBox.sub {f g : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f) (hg : D.AnalyticNearClosedBox g) :
    D.AnalyticNearClosedBox (f - g) := by
  rw [D.analyticNearClosedBox_iff] at hf hg ⊢
  exact hf.sub hg

/--
@isnad1 id=analytic.1h4v.s5.2aa76cea9a20 from=translated src=- shape=81f3f26f vocab=a1b98c9e
-/
theorem AnalyticNearClosedBox.smul (c : ℝ)
    {f : RestrictedBoxSpace p → ℝ} (hf : D.AnalyticNearClosedBox f) :
    D.AnalyticNearClosedBox (c • f) := by
  rw [D.analyticNearClosedBox_iff] at hf ⊢
  exact hf.const_smul

/--
@isnad1 id=analytic.1h4v.s5.9f63bb3fcecd from=translated src=- shape=fe58a4b6 vocab=85f7a4e0
-/
theorem AnalyticNearClosedBox.pow {f : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f) (n : ℕ) :
    D.AnalyticNearClosedBox (f ^ n) := by
  rw [D.analyticNearClosedBox_iff] at hf ⊢
  exact hf.pow n

/--
@isnad1 id=analytic.0h3v.s4.ca90de7b13f9 from=translated src=- shape=69958c24 vocab=95876a3b
-/
theorem analyticNearClosedBox_apply (i : Fin p) :
    D.AnalyticNearClosedBox (fun w ↦ w i) := by
  rw [D.analyticNearClosedBox_iff]
  intro w _
  exact (ContinuousLinearMap.proj (R := ℝ) i).analyticAt w

/-- Reciprocal closure needs nonvanishing only on the closed box.  Analyticity
and nonvanishing are both open conditions, so they yield a common open
neighborhood on which the reciprocal is analytic.
@isnad1 id=analytic.2h3v.s5.59c3fcfc2d39 from=translated src=- shape=bd92224a vocab=090a9bea
-/
theorem AnalyticNearClosedBox.inv {f : RestrictedBoxSpace p → ℝ}
    (hf : D.AnalyticNearClosedBox f)
    (hzero : ∀ w ∈ D.closedBox, f w ≠ 0) :
    D.AnalyticNearClosedBox fun w ↦ (f w)⁻¹ := by
  rcases hf with ⟨U, hUopen, hDU, hfU⟩
  let V := U ∩ f ⁻¹' ({0} : Set ℝ)ᶜ
  have hVopen : IsOpen V :=
    hfU.continuousOn.isOpen_inter_preimage hUopen isClosed_singleton.isOpen_compl
  refine ⟨V, hVopen, ?_, ?_⟩
  · intro w hw
    exact ⟨hDU hw, by simpa using hzero w hw⟩
  · have hfV : AnalyticOnNhd ℝ f V := hfU.mono inter_subset_left
    exact hfV.inv fun w hw ↦ by simpa [V] using hw.2

/-- The real subalgebra of total representatives analytic near the closed
box.-/
def analyticNearClosedBoxSubalgebra :
    Subalgebra ℝ (RestrictedBoxSpace p → ℝ) where
  carrier := {f | D.AnalyticNearClosedBox f}
  zero_mem' := D.analyticNearClosedBox_zero
  one_mem' := D.analyticNearClosedBox_one
  add_mem' := fun hf hg ↦ AnalyticNearClosedBox.add (D := D) hf hg
  mul_mem' := fun hf hg ↦ AnalyticNearClosedBox.mul (D := D) hf hg
  algebraMap_mem' := by
    intro c
    change D.AnalyticNearClosedBox (fun _ ↦ c)
    exact D.analyticNearClosedBox_const c

/--
@isnad1 id=iff.0h3v.s6.e6a0254fe4df from=translated src=- shape=190294aa vocab=aec45bae
-/
@[simp]
theorem mem_analyticNearClosedBoxSubalgebra
    {f : RestrictedBoxSpace p → ℝ} :
    f ∈ analyticNearClosedBoxSubalgebra D ↔ D.AnalyticNearClosedBox f :=
  Iff.rfl

/--
@isnad1 id=mem.2h3v.s7.c18fc39c52ed from=translated src=- shape=25bee911 vocab=3d9a3dba
-/
theorem inv_mem_analyticNearClosedBoxSubalgebra
    {f : RestrictedBoxSpace p → ℝ}
    (hf : f ∈ analyticNearClosedBoxSubalgebra D)
    (hzero : ∀ w ∈ D.closedBox, f w ≠ 0) :
    (fun w ↦ (f w)⁻¹) ∈ analyticNearClosedBoxSubalgebra D :=
  AnalyticNearClosedBox.inv (D := D) hf hzero

end RestrictedBox

/-! ## A generic analytic function subalgebra -/

section AnalyticFunctionAlgebra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Real-valued functions analytic at every point of `s` form a real
subalgebra.-/
def analyticOnNhdSubalgebra (s : Set X) : Subalgebra ℝ (X → ℝ) where
  carrier := {f | AnalyticOnNhd ℝ f s}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun hf hg ↦ AnalyticOnNhd.add hf hg
  mul_mem' := fun hf hg ↦ AnalyticOnNhd.mul hf hg
  algebraMap_mem' := by
    intro c
    change AnalyticOnNhd ℝ (fun _ ↦ c) s
    exact analyticOnNhd_const

/--
@isnad1 id=iff.0h3v.s6.c0bcac8b3a55 from=translated src=- shape=a17f0c92 vocab=a5b1fdac
-/
@[simp]
theorem mem_analyticOnNhdSubalgebra {s : Set X} {f : X → ℝ} :
    f ∈ analyticOnNhdSubalgebra s ↔ AnalyticOnNhd ℝ f s :=
  Iff.rfl

end AnalyticFunctionAlgebra

/-! ## Restricted source coordinates and the initial algebra -/

/-- Coordinates are ordered as `((s,w),y)`: positive/unbounded Abel
coordinates, bounded box coordinates, and unrestricted auxiliary
coordinates.-/
abbrev RestrictedSource (m p a : ℕ) :=
  ((Fin m → ℝ) × RestrictedBoxSpace p) × (Fin a → ℝ)

def restrictedSCoordinate {m p a : ℕ} (i : Fin m) :
    RestrictedSource m p a → ℝ := fun x ↦ x.1.1 i

def restrictedWCoordinate {m p a : ℕ} (j : Fin p) :
    RestrictedSource m p a → ℝ := fun x ↦ x.1.2 j

def restrictedAuxCoordinate {m p a : ℕ} (k : Fin a) :
    RestrictedSource m p a → ℝ := fun x ↦ x.2 k

def restrictedBoxCoefficientPullback {m p a : ℕ}
    (f : RestrictedBoxSpace p → ℝ) : RestrictedSource m p a → ℝ :=
  fun x ↦ f x.1.2

/-- The fixed generators: every `s` coordinate, every auxiliary coordinate,
and the pullback of every coefficient representative analytic near the closed
box.  The bounded `w` coordinates are already among the last class.-/
def restrictedFixedGenerators {m p a : ℕ} (D : RestrictedBox p) :
    Set (RestrictedSource m p a → ℝ) :=
  Set.range (restrictedSCoordinate (p := p) (a := a)) ∪
    Set.range (restrictedAuxCoordinate (m := m) (p := p)) ∪
      Set.range (fun f : RestrictedBox.analyticNearClosedBoxSubalgebra D ↦
        restrictedBoxCoefficientPullback (m := m) (a := a) (f : RestrictedBoxSpace p → ℝ))

/-- The initial expression algebra, with an additional set of special
generators.  In the Abel application these are exactly the permitted Abel-jet
functions.-/
def restrictedExpressionBase {m p a : ℕ} (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ)) :
    Subalgebra ℝ (RestrictedSource m p a → ℝ) :=
  Algebra.adjoin ℝ (restrictedFixedGenerators D ∪ specialGenerators)

/--
@isnad1 id=mem.0h6v.s7.203ed68d2d1b from=translated src=- shape=e58dd970 vocab=21b16d56
-/
theorem restrictedSCoordinate_mem_base {m p a : ℕ} (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ)) (i : Fin m) :
    restrictedSCoordinate (p := p) (a := a) i ∈
      restrictedExpressionBase D specialGenerators := by
  apply Algebra.subset_adjoin
  exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))

/--
@isnad1 id=mem.0h6v.s7.0f3986129033 from=translated src=- shape=fd854323 vocab=a7c29c36
-/
theorem restrictedAuxCoordinate_mem_base {m p a : ℕ} (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ)) (k : Fin a) :
    restrictedAuxCoordinate (m := m) (p := p) k ∈
      restrictedExpressionBase D specialGenerators := by
  apply Algebra.subset_adjoin
  exact Or.inl (Or.inl (Or.inr ⟨k, rfl⟩))

/--
@isnad1 id=mem.0h6v.s8.87b3080b50b9 from=translated src=- shape=e2754ee2 vocab=ce91f643
-/
theorem restrictedBoxCoefficientPullback_mem_base {m p a : ℕ}
    (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ))
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedBoxCoefficientPullback (m := m) (a := a)
        (f : RestrictedBoxSpace p → ℝ) ∈
      restrictedExpressionBase D specialGenerators := by
  apply Algebra.subset_adjoin
  exact Or.inl (Or.inr ⟨f, rfl⟩)

/--
@isnad1 id=mem.0h6v.s7.34660546c199 from=translated src=- shape=d49283e4 vocab=ea835636
-/
theorem restrictedWCoordinate_mem_base {m p a : ℕ} (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ)) (j : Fin p) :
    restrictedWCoordinate (m := m) (a := a) j ∈
      restrictedExpressionBase D specialGenerators := by
  change restrictedBoxCoefficientPullback (m := m) (a := a)
    (fun w ↦ w j) ∈ restrictedExpressionBase D specialGenerators
  exact restrictedBoxCoefficientPullback_mem_base D specialGenerators
    ⟨fun w ↦ w j, D.analyticNearClosedBox_apply j⟩

/--
@isnad1 id=mem.1h6v.s7.1b0703b4f526 from=translated src=- shape=14f41f7b vocab=c668d4df
-/
theorem specialGenerator_mem_base {m p a : ℕ} (D : RestrictedBox p)
    {specialGenerators : Set (RestrictedSource m p a → ℝ)}
    {f : RestrictedSource m p a → ℝ} (hf : f ∈ specialGenerators) :
    f ∈ restrictedExpressionBase D specialGenerators := by
  exact Algebra.subset_adjoin (Or.inr hf)

/--
@isnad1 id=le.1h6v.s7.13aa2e6134a3 from=translated src=- shape=6c01670c vocab=254a4ae8
-/
theorem restrictedExpressionBase_mono {m p a : ℕ} (D : RestrictedBox p)
    {S T : Set (RestrictedSource m p a → ℝ)} (hST : S ⊆ T) :
    restrictedExpressionBase D S ≤ restrictedExpressionBase D T := by
  apply Algebra.adjoin_mono
  rintro f (hf | hf)
  · exact Or.inl hf
  · exact Or.inr (hST hf)

/-! ## Finite exponential towers -/

section ExponentialTower

variable {X : Type*}

/-- The exponential of one proposed exponent.-/
def exponentialGenerator {ell : ℕ} (exponent : Fin ell → X → ℝ)
    (i : Fin ell) : X → ℝ :=
  fun x ↦ Real.exp (exponent i x)

/-- At step `j`, there is one new generator if `j < ell`, and none after the
declared tower length.  Quantifying over the proof `j < ell` avoids a default
value when `j ≥ ell`.-/
def exponentialStepGenerators {ell : ℕ}
    (exponent : Fin ell → X → ℝ) (j : ℕ) : Set (X → ℝ) :=
  {f | ∃ hj : j < ell,
    f = exponentialGenerator exponent ⟨j, hj⟩}

/--
@isnad1 id=eq.1h4v.s5.ab98886d85d4 from=translated src=- shape=6ca4d865 vocab=9d446c76
-/
theorem exponentialStepGenerators_eq_empty {ell : ℕ}
    (exponent : Fin ell → X → ℝ) {j : ℕ} (hj : ell ≤ j) :
    exponentialStepGenerators exponent j = ∅ := by
  ext f
  change (∃ h : j < ell, f = exponentialGenerator exponent ⟨j, h⟩) ↔ False
  constructor
  · rintro ⟨h, _⟩
    exact (not_lt_of_ge hj h).elim
  · exact False.elim

/--
@isnad1 id=eq.0h4v.s5.9cc5d616dff4 from=translated src=- shape=b7e41730 vocab=f4e91670
-/
theorem exponentialStepGenerators_at_index {ell : ℕ}
    (exponent : Fin ell → X → ℝ) (i : Fin ell) :
    exponentialStepGenerators exponent i.val =
      {exponentialGenerator exponent i} := by
  ext f
  constructor
  · rintro ⟨hi, hf⟩
    rw [Set.mem_singleton_iff]
    have heq : (⟨i.val, hi⟩ : Fin ell) = i := Fin.ext rfl
    simpa [heq] using hf
  · intro hf
    rw [Set.mem_singleton_iff] at hf
    refine ⟨i.isLt, ?_⟩
    have heq : (⟨i.val, i.isLt⟩ : Fin ell) = i := Fin.ext rfl
    simpa [heq] using hf

/-- Successively adjoin the step generators to `base`.  Levels after `ell`
are defined too and will be proved equal to the terminal level.-/
def exponentialLevels (base : Subalgebra ℝ (X → ℝ)) {ell : ℕ}
    (exponent : Fin ell → X → ℝ) : ℕ → Subalgebra ℝ (X → ℝ)
  | 0 => base
  | j + 1 => exponentialLevels base exponent j ⊔
      Algebra.adjoin ℝ (exponentialStepGenerators exponent j)

/-- A finite exponential tower stores exponents `g_i` and requires
`g_i ∈ B_i`.  Its generated function is `exp ∘ g_i`, and `B_{i+1}` is
definitionally obtained by adjoining that function.-/
structure FiniteExponentialTower (base : Subalgebra ℝ (X → ℝ)) (ell : ℕ) where
  exponent : Fin ell → X → ℝ
  exponent_mem_level : ∀ i,
    exponent i ∈ exponentialLevels base exponent i.val

namespace FiniteExponentialTower

variable {base : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
    (T : FiniteExponentialTower base ell)

def level (j : ℕ) : Subalgebra ℝ (X → ℝ) :=
  exponentialLevels base T.exponent j

def generator (i : Fin ell) : X → ℝ :=
  exponentialGenerator T.exponent i

/--
@isnad1 id=eq.0h4v.s6.b43a6b05bbf3 from=translated src=- shape=1190b89e vocab=f9502a04
-/
@[simp]
theorem level_zero : T.level 0 = base :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.d1df7d0e4220 from=translated src=- shape=e9c77038 vocab=2427a113
-/
theorem level_succ (j : ℕ) :
    T.level (j + 1) = T.level j ⊔
      Algebra.adjoin ℝ (exponentialStepGenerators T.exponent j) :=
  rfl

/--
@isnad1 id=le.0h5v.s7.f2d4c844e9b3 from=translated src=- shape=f4d41da3 vocab=9ff9fc79
-/
theorem level_le_succ (j : ℕ) : T.level j ≤ T.level (j + 1) := by
  rw [T.level_succ]
  exact le_sup_left

/--
@isnad1 id=monotone.0h4v.s6.7d22af49e0ba from=translated src=- shape=f2501f12 vocab=70bdce9c
-/
theorem level_mono : Monotone T.level :=
  monotone_nat_of_le_succ T.level_le_succ

/--
@isnad1 id=le.0h5v.s7.9a3829f2c8f1 from=translated src=- shape=a57a1e37 vocab=9fca4fee
-/
theorem base_le_level (j : ℕ) : base ≤ T.level j := by
  simpa only [T.level_zero] using T.level_mono (Nat.zero_le j)

/--
@isnad1 id=mem.1h6v.s7.a5920a28065c from=translated src=- shape=32e6daa9 vocab=f621c312
-/
theorem base_mem_level {f : X → ℝ} (hf : f ∈ base) (j : ℕ) :
    f ∈ T.level j :=
  T.base_le_level j hf

/--
@isnad1 id=mem.0h5v.s6.dbb01beb0689 from=translated src=- shape=4d86d63d vocab=6430952a
-/
theorem exponent_mem (i : Fin ell) : T.exponent i ∈ T.level i.val :=
  T.exponent_mem_level i

/--
@isnad1 id=mem.1h6v.s7.436fa2e115e7 from=translated src=- shape=67d5e125 vocab=54991b55
-/
theorem exponent_mem_level_of_le (i : Fin ell) {j : ℕ} (hij : i.val ≤ j) :
    T.exponent i ∈ T.level j :=
  T.level_mono hij (T.exponent_mem i)

/--
@isnad1 id=eq.0h5v.s8.fdab42f5eab5 from=translated src=- shape=ca214648 vocab=8001004f
-/
theorem level_succ_eq_adjoin (i : Fin ell) :
    T.level (i.val + 1) = T.level i.val ⊔
      Algebra.adjoin ℝ {T.generator i} := by
  rw [T.level_succ, exponentialStepGenerators_at_index]
  rfl

/--
@isnad1 id=mem.0h5v.s7.b9eb40d57da1 from=translated src=- shape=93c79ef0 vocab=a36285fb
-/
theorem generator_mem_level_succ (i : Fin ell) :
    T.generator i ∈ T.level (i.val + 1) := by
  rw [T.level_succ_eq_adjoin i]
  apply (show Algebra.adjoin ℝ {T.generator i} ≤
    T.level i.val ⊔ Algebra.adjoin ℝ {T.generator i} from le_sup_right)
  exact Algebra.subset_adjoin (Set.mem_singleton (T.generator i))

/--
@isnad1 id=mem.1h6v.s7.532296641e8e from=translated src=- shape=67d5e125 vocab=4a1cd193
-/
theorem generator_mem_level_of_lt (i : Fin ell) {j : ℕ} (hij : i.val < j) :
    T.generator i ∈ T.level j := by
  exact T.level_mono (Nat.succ_le_iff.mpr hij) (T.generator_mem_level_succ i)

/--
@isnad1 id=eq.1h5v.s6.cbc74b02534d from=translated src=- shape=7cf69ab8 vocab=9ff9fc79
-/
theorem level_succ_eq_of_length_le {j : ℕ} (hj : ell ≤ j) :
    T.level (j + 1) = T.level j := by
  rw [T.level_succ, exponentialStepGenerators_eq_empty T.exponent hj,
    Algebra.adjoin_empty, sup_bot_eq]

/--
@isnad1 id=eq.1h5v.s6.dcf1b801fd12 from=translated src=- shape=17c40e65 vocab=9fca4fee
-/
theorem level_eq_terminal {j : ℕ} (hj : ell ≤ j) :
    T.level j = T.level ell := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, T.level_succ_eq_of_length_le (by omega), ih (by omega)]

end FiniteExponentialTower

/-! ### Analyticity of every level -/

namespace FiniteExponentialTower

section AnalyticTower

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
  {base : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
  (T : FiniteExponentialTower base ell) {s : Set X}

/-- If every base function is analytic on `s`, all functions in every tower
level are analytic on `s`.  The prefix condition `g_i ∈ B_i` is exactly what
makes the induction close.
@isnad1 id=le.1h6v.s8.91d25c2bfc00 from=translated src=- shape=9a2beac6 vocab=068300a1
-/
theorem level_le_analyticOnNhdSubalgebra
    (hbase : base ≤ analyticOnNhdSubalgebra s) :
    ∀ j, T.level j ≤ analyticOnNhdSubalgebra s := by
  intro j
  induction j with
  | zero =>
      simpa only [T.level_zero] using hbase
  | succ j ih =>
      rw [T.level_succ]
      refine sup_le ih (Algebra.adjoin_le ?_)
      rintro f ⟨hj, rfl⟩
      change AnalyticOnNhd ℝ
        (fun x ↦ Real.exp (T.exponent ⟨j, hj⟩ x)) s
      exact (ih (T.exponent_mem ⟨j, hj⟩)).rexp

/--
@isnad1 id=analytic.2h7v.s8.3752672e3e11 from=translated src=- shape=be6cdc9f vocab=717e5364
-/
theorem analyticOnNhd_of_mem_level
    (hbase : base ≤ analyticOnNhdSubalgebra s)
    {j : ℕ} {f : X → ℝ} (hf : f ∈ T.level j) :
    AnalyticOnNhd ℝ f s :=
  T.level_le_analyticOnNhdSubalgebra hbase j hf

end AnalyticTower

end FiniteExponentialTower

end ExponentialTower

/-! ## Towers over the closed-box analytic algebra -/

/-- A convenient specialization whose base is exactly the algebra of
coefficient representatives analytic near the closed box.-/
abbrev ClosedBoxExponentialTower {p ell : ℕ} (D : RestrictedBox p) :=
  FiniteExponentialTower (RestrictedBox.analyticNearClosedBoxSubalgebra D) ell

/--
@isnad1 id=analytic.1h6v.s7.3dac60e4f9e4 from=translated src=- shape=30d5078f vocab=8c2db0b6
-/
theorem ClosedBoxExponentialTower.analyticNearClosedBox_of_mem_level
    {p ell : ℕ} {D : RestrictedBox p}
    (T : ClosedBoxExponentialTower (ell := ell) D) {j : ℕ}
    {f : RestrictedBoxSpace p → ℝ} (hf : f ∈ T.level j) :
    D.AnalyticNearClosedBox f := by
  rw [D.analyticNearClosedBox_iff]
  apply T.analyticOnNhd_of_mem_level (s := D.closedBox) _ hf
  intro g hg
  change AnalyticOnNhd ℝ g D.closedBox
  exact D.analyticNearClosedBox_iff.mp hg

/-- Towers used on a full restricted source, with the initial algebra defined
above.-/
abbrev RestrictedExpressionTower {m p a ell : ℕ} (D : RestrictedBox p)
    (specialGenerators : Set (RestrictedSource m p a → ℝ)) :=
  FiniteExponentialTower (restrictedExpressionBase D specialGenerators) ell

end AbelFormalization
