module

public import Tengoku.Seed.RingTheory.ClassGroup.ExtendedHom
import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.Conjugation
import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.FixedAssociate
public import Tengoku.Seed.NumberTheory.NumberField.CMField
public import Tengoku.Seed.NumberTheory.NumberField.ClassNumber
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic CM data for the totally real subfield

This file packages the CM-structure, degree formulas, unit-index computation,
and the local class-number notation `h` / `h⁺`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Notation for the maximal totally real subfield of `K`. Scoped to this
section; `K` refers to the ambient variable introduced above.-/
local notation3 "K⁺" => NumberField.maximalRealSubfield K

include hp_odd in
/-- Any `p`-th cyclotomic extension of `ℚ` is a CM field for `p` an odd
prime.
@isnad1 id=iscmfiel.1h2v.s5.bd72e894946a from=translated src=- shape=17123208 vocab=a505d507
-/
theorem isCMField_of_cyclotomic : IsCMField K :=
  Rat.isCMField (S := {p}) _ ⟨p, by grind [hp.1.two_le]⟩

/-- `[K: K⁺] = 2`.
@isnad1 id=eq.0h1v.s7.b06ff2dc916f from=translated src=- shape=a47e6312 vocab=57fb6d60
-/
theorem finrank_K_over_Kplus [IsCMField K] :
    Module.finrank (K⁺) K = 2 :=
  IsQuadraticExtension.finrank_eq_two _ _

/-- `[K⁺: ℚ] = (p-1)/2`.
@isnad1 id=eq.0h2v.s8.8487e6025d16 from=translated src=- shape=f744b933 vocab=f6bb593b
-/
theorem finrank_Kplus_over_rat [IsCMField K] :
    Module.finrank ℚ (K⁺) = (p - 1) / 2 := by
  have h1 : Module.finrank (K⁺) K = 2 := finrank_K_over_Kplus K
  have h2 : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
        Nat.totient_prime hp.1]
  have htow := Module.finrank_mul_finrank ℚ (K⁺) K
  rw [h1, h2] at htow
  exact (Nat.div_eq_of_eq_mul_left (by omega) htow.symm).symm

/-- The class number of `K`, written locally as `h`.-/
noncomputable def h : ℕ := Fintype.card (ClassGroup (𝓞 K))

/-- The class number of the totally real subfield `K⁺`, written locally as `h⁺`.-/
noncomputable def hPlus [IsCMField K] : ℕ := Fintype.card (ClassGroup (𝓞 (K⁺)))

end CyclotomicSetup

end KummerCriterion

end

/-!
# Class-group descent for the totally real subfield

This file finishes the descent from `𝒪_K` to `𝒪_{K⁺}`, proves injectivity of
`Cl(𝒪_{K⁺}) → Cl(𝒪_K)`, and packages `h⁻`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Extending and contracting ideals along `𝓞(L⁺) ⊆ 𝓞 L` is the identity.
@isnad1 id=eq.0h2v.s10.ceeeaa81693d from=translated src=- shape=1a897872 vocab=2940338c
-/
theorem map_comap_eq_ringOfIntegers
    (L : Type*) [Field L] [NumberField L]
    (J : Ideal (𝓞 (NumberField.maximalRealSubfield L))) :
    (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L))).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L)) = J := by
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat J

/-- If `I · 𝒪_K = (b)` with `b` descending from `𝒪_{K⁺}`, then `I` is principal.
@isnad1 id=isprinci.1h3v.s10.13de64207213 from=translated src=- shape=33912a6d vocab=b8494ea2
-/
theorem isPrincipal_of_map_eq_span_singleton_of_mem
    (I : Ideal (𝓞 (K⁺)))
    (b₀ : 𝓞 (K⁺))
    (hb : I.map (algebraMap (𝓞 (K⁺)) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 (K⁺)) (𝓞 K) b₀}) :
    I.IsPrincipal := by
  refine ⟨b₀, ?_⟩
  let f : 𝓞 (K⁺) →+* 𝓞 K := algebraMap (𝓞 (K⁺)) (𝓞 K)
  have hbc := congrArg (Ideal.comap f) hb
  have hspan : Ideal.comap f (Ideal.span {f b₀}) = Ideal.span {b₀} := by
    calc
      Ideal.comap f (Ideal.span {f b₀}) = Ideal.comap f ((Ideal.span {b₀}).map f) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {b₀} := map_comap_eq_ringOfIntegers K (Ideal.span {b₀})
  calc
    I = Ideal.comap f (I.map f) := (map_comap_eq_ringOfIntegers K I).symm
    _ = Ideal.comap f (Ideal.span {f b₀}) := hbc
    _ = Ideal.span {b₀} := hspan

local notation3 "h" => KummerCriterion.h K
local notation3 "h⁺" => KummerCriterion.hPlus K

/-- The *relative class number* `h⁻:= h / h⁺`, written locally as `h⁻`.-/
noncomputable def hMinus [IsCMField K] : ℕ := h / h⁺

local notation3 "h⁻" => KummerCriterion.hMinus K

end CyclotomicSetup

end KummerCriterion

end
