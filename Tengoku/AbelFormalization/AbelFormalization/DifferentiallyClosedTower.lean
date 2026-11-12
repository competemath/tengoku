import Tengoku.AbelFormalization.AbelFormalization.RestrictedLastGeneratorLift
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional differentiation in finite exponential towers

The expression algebras in the manuscript are closed under coordinate
derivatives.  The reusable algebraic content is slightly more general: if a
base algebra has derivatives along a fixed direction and each exponential
obeys the chain rule, every level of a finite exponential tower has the same
closure property.  Derivatives are recorded only on a chosen domain, so no
global differentiability assumption is imposed on the total representatives.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `df` is the derivative of `f` along the fixed vector `v`, at every point
of `Omega`.-/
def HasDirectionalDerivOn (Omega : Set X) (v : X)
    (f df : X → ℝ) : Prop :=
  ∀ x ∈ Omega,
    DifferentiableAt ℝ f x ∧ fderiv ℝ f x v = df x

/--
@isnad1 id=hasdirec.2h6v.s5.94a1b215596b from=translated src=- shape=4cc5057a vocab=fbda0099
-/
theorem HasDirectionalDerivOn.mono
    {Omega Omega' : Set X} {v : X} {f df : X → ℝ}
    (h : HasDirectionalDerivOn Omega v f df) (hsub : Omega' ⊆ Omega) :
    HasDirectionalDerivOn Omega' v f df :=
  fun x hx ↦ h x (hsub hx)

/--
@isnad1 id=hasdirec.0h4v.s5.b1fc472d04dd from=translated src=- shape=0ee35710 vocab=406a3d22
-/
theorem hasDirectionalDerivOn_const (Omega : Set X) (v : X) (c : ℝ) :
    HasDirectionalDerivOn Omega v (fun _ ↦ c) 0 := by
  intro x hx
  constructor
  · exact differentiableAt_const c
  · simp

/--
@isnad1 id=hasdirec.2h7v.s6.68405b5917d5 from=translated src=- shape=73743518 vocab=54284b7e
-/
theorem HasDirectionalDerivOn.add
    {Omega : Set X} {v : X} {f df g dg : X → ℝ}
    (hf : HasDirectionalDerivOn Omega v f df)
    (hg : HasDirectionalDerivOn Omega v g dg) :
    HasDirectionalDerivOn Omega v (f + g) (df + dg) := by
  intro x hx
  have hfx := hf x hx
  have hgx := hg x hx
  constructor
  · exact hfx.1.add hgx.1
  · rw [fderiv_add hfx.1 hgx.1]
    simp [hfx.2, hgx.2]

/--
@isnad1 id=hasdirec.2h7v.s7.5f9425f90694 from=translated src=- shape=fa68ed50 vocab=8b774233
-/
theorem HasDirectionalDerivOn.mul
    {Omega : Set X} {v : X} {f df g dg : X → ℝ}
    (hf : HasDirectionalDerivOn Omega v f df)
    (hg : HasDirectionalDerivOn Omega v g dg) :
    HasDirectionalDerivOn Omega v (f * g) (df * g + f * dg) := by
  intro x hx
  have hfx := hf x hx
  have hgx := hg x hx
  have hmul := hfx.1.hasFDerivAt.mul hgx.1.hasFDerivAt
  constructor
  · exact hfx.1.mul hgx.1
  · have h := congrArg (fun L : X →L[ℝ] ℝ ↦ L v) hmul.fderiv
    simpa [hfx.2, hgx.2, add_comm, mul_comm] using h

/--
@isnad1 id=hasdirec.1h5v.s6.4c14c3fc7464 from=translated src=- shape=56461497 vocab=3c409823
-/
theorem HasDirectionalDerivOn.exp
    {Omega : Set X} {v : X} {g dg : X → ℝ}
    (hg : HasDirectionalDerivOn Omega v g dg) :
    HasDirectionalDerivOn Omega v (fun x ↦ Real.exp (g x))
      ((fun x ↦ Real.exp (g x)) * dg) := by
  intro x hx
  have hgx := hg x hx
  have hexp := hgx.1.hasFDerivAt.exp
  constructor
  · exact hgx.1.exp
  · have h := congrArg (fun L : X →L[ℝ] ℝ ↦ L v) hexp.fderiv
    simpa [hgx.2] using h

/-- Every member of `B` has a directional derivative represented by another
member of `B`.-/
def DirectionallyClosedOn (B : Subalgebra ℝ (X → ℝ))
    (Omega : Set X) (v : X) : Prop :=
  ∀ f : X → ℝ, f ∈ B →
    ∃ df : X → ℝ, df ∈ B ∧ HasDirectionalDerivOn Omega v f df

/-- Closure on a generating set propagates through algebra adjunction.
@isnad1 id=directio.1h4v.s7.d9811a5b51e2 from=translated src=- shape=79688e43 vocab=8f6dfc1c
-/
theorem directionallyClosedOn_adjoin
    {Omega : Set X} {v : X} (s : Set (X → ℝ))
    (hgen : ∀ f ∈ s, ∃ df : X → ℝ,
      df ∈ Algebra.adjoin ℝ s ∧ HasDirectionalDerivOn Omega v f df) :
    DirectionallyClosedOn (Algebra.adjoin ℝ s) Omega v := by
  intro f hf
  exact Algebra.adjoin_induction
    (p := fun f _ ↦ ∃ df : X → ℝ,
      df ∈ Algebra.adjoin ℝ s ∧ HasDirectionalDerivOn Omega v f df)
    (fun f hf ↦ hgen f hf)
    (fun c ↦ by
      refine ⟨0, (Algebra.adjoin ℝ s).zero_mem, ?_⟩
      change HasDirectionalDerivOn Omega v (fun _ : X ↦ c) 0
      exact hasDirectionalDerivOn_const Omega v c)
    (fun f g hf hg hdf hdg ↦ by
      obtain ⟨df, hdfmem, hdfderiv⟩ := hdf
      obtain ⟨dg, hdgmem, hdgderiv⟩ := hdg
      exact ⟨df + dg, (Algebra.adjoin ℝ s).add_mem hdfmem hdgmem,
        hdfderiv.add hdgderiv⟩)
    (fun f g hf hg hdf hdg ↦ by
      obtain ⟨df, hdfmem, hdfderiv⟩ := hdf
      obtain ⟨dg, hdgmem, hdgderiv⟩ := hdg
      exact ⟨df * g + f * dg,
        (Algebra.adjoin ℝ s).add_mem
          ((Algebra.adjoin ℝ s).mul_mem hdfmem
            hg)
          ((Algebra.adjoin ℝ s).mul_mem
            hf hdgmem),
        hdfderiv.mul hdgderiv⟩)
    hf

/-- Adjoining generators whose derivatives lie in the enlarged algebra
preserves directional closure of the old algebra.
@isnad1 id=directio.2h5v.s9.30af72b69245 from=translated src=- shape=413a73dc vocab=d0272db5
-/
theorem directionallyClosedOn_sup_adjoin
    {Omega : Set X} {v : X} (B : Subalgebra ℝ (X → ℝ))
    (s : Set (X → ℝ)) (hB : DirectionallyClosedOn B Omega v)
    (hgen : ∀ f ∈ s, ∃ df : X → ℝ,
      df ∈ B ⊔ Algebra.adjoin ℝ s ∧
        HasDirectionalDerivOn Omega v f df) :
    DirectionallyClosedOn (B ⊔ Algebra.adjoin ℝ s) Omega v := by
  have hsup : B ⊔ Algebra.adjoin ℝ s =
      Algebra.adjoin ℝ ((B : Set (X → ℝ)) ∪ s) := by
    apply le_antisymm
    · apply sup_le
      · intro f hf
        exact Algebra.subset_adjoin (Or.inl hf)
      · apply Algebra.adjoin_le
        intro f hf
        exact Algebra.subset_adjoin (Or.inr hf)
    · apply Algebra.adjoin_le
      rintro f (hf | hf)
      · exact (show B ≤ B ⊔ Algebra.adjoin ℝ s from le_sup_left) hf
      · exact (show Algebra.adjoin ℝ s ≤ B ⊔ Algebra.adjoin ℝ s from
          le_sup_right) (Algebra.subset_adjoin hf)
  rw [hsup]
  apply directionallyClosedOn_adjoin
  intro f hf
  rcases hf with hf | hf
  · obtain ⟨df, hdfmem, hdf⟩ := hB f hf
    refine ⟨df, ?_, hdf⟩
    rw [← hsup]
    exact (show B ≤ B ⊔ Algebra.adjoin ℝ s from le_sup_left) hdfmem
  · obtain ⟨df, hdfmem, hdf⟩ := hgen f hf
    refine ⟨df, ?_, hdf⟩
    rwa [← hsup]

/-- Directional derivative closure propagates through every level of a
finite exponential tower.
@isnad1 id=directio.1h7v.s6.c415caa95011 from=translated src=- shape=becb7c1f vocab=c3195a3c
-/
theorem FiniteExponentialTower.directionallyClosedOn_level
    {base : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
    (T : FiniteExponentialTower base ell)
    {Omega : Set X} {v : X}
    (hbase : DirectionallyClosedOn base Omega v) :
    ∀ j, DirectionallyClosedOn (T.level j) Omega v := by
  intro j
  induction j with
  | zero => simpa only [T.level_zero] using hbase
  | succ j ih =>
      by_cases hj : j < ell
      · let i : Fin ell := ⟨j, hj⟩
        obtain ⟨dg, hdgmem, hdg⟩ := ih (T.exponent i) (T.exponent_mem i)
        have hgenDeriv : HasDirectionalDerivOn Omega v
            (T.generator i) (T.generator i * dg) := by
          exact hdg.exp
        have hgenMem : T.generator i * dg ∈
            T.level i.val ⊔ Algebra.adjoin ℝ {T.generator i} := by
          apply (T.level i.val ⊔
            Algebra.adjoin ℝ {T.generator i}).mul_mem
          · exact (show Algebra.adjoin ℝ {T.generator i} ≤
              T.level i.val ⊔ Algebra.adjoin ℝ {T.generator i} from
                le_sup_right)
              (Algebra.subset_adjoin (Set.mem_singleton (T.generator i)))
          · exact (show T.level i.val ≤
              T.level i.val ⊔ Algebra.adjoin ℝ {T.generator i} from
                le_sup_left) hdgmem
        rw [show j + 1 = i.val + 1 by rfl, T.level_succ_eq_adjoin i]
        apply directionallyClosedOn_sup_adjoin (T.level i.val)
          {T.generator i} ih
        intro f hf
        rw [Set.mem_singleton_iff] at hf
        subst f
        exact ⟨T.generator i * dg, hgenMem, hgenDeriv⟩
      · have hjle : ell ≤ j := Nat.le_of_not_gt hj
        rw [T.level_succ_eq_of_length_le hjle]
        exact ih

end AbelFormalization
