import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ArchType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section Generic

variable {G : Type*} [Group G]

def RightTranslatesSpanFinite (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ),
    ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

/--
@isnad1 id=righttra.0h3v.s4.e0fd845cb400 from=translated src=- shape=aa10bef6 vocab=59cc842f
-/
theorem rightTranslatesSpanFinite_const (K : Subgroup G) (c : ℂ) :
    RightTranslatesSpanFinite K (fun _ : G => c) := by
  refine ⟨{fun _ => c}, fun k _hk => ?_⟩
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

/--
@isnad1 id=righttra.0h2v.s4.a69bbb5f596d from=translated src=- shape=77aac30d vocab=888ae21c
-/
theorem rightTranslatesSpanFinite_bot (f : G → ℂ) :
    RightTranslatesSpanFinite (⊥ : Subgroup G) f := by
  refine ⟨{f}, fun k hk => ?_⟩
  rw [Subgroup.mem_bot] at hk; subst hk
  have h1 : (fun x : G => f (x * 1)) = f := by funext x; rw [mul_one]
  rw [h1]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

def archRowIsometrySubgroup (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup w.Completion).map (adelicArchGLInclAt F w)

def IsArchKFiniteAt (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  RightTranslatesSpanFinite (archRowIsometrySubgroup F w) φ

def IsArchKFinite (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, IsArchKFiniteAt F w φ

/--
@isnad1 id=isarchkf.0h2v.s4.e26ddfcb8d1e from=translated src=- shape=463f944c vocab=af9eaa1d
-/
theorem isArchKFinite_const (c : ℂ) : IsArchKFinite F (fun _ => c) :=
  fun w => rightTranslatesSpanFinite_const (archRowIsometrySubgroup F w) c

/--
@isnad1 id=isarchkf.0h1v.s5.30ca3703cc48 from=translated src=- shape=a284a31e vocab=af9eaa1d
-/
theorem isArchKFinite_zero : IsArchKFinite F (fun _ => (0 : ℂ)) := isArchKFinite_const F 0

/--
@isnad1 id=isarchkf.1h3v.s11.c29a236c17ae from=translated src=- shape=c521b479 vocab=56b29a84
-/
theorem isArchKFinite_of_hasArchType
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : HasArchType F χ φ) :
    IsArchKFinite F φ := by
  intro w
  refine ⟨{φ}, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hχ : (fun x => φ (x * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)))
      = ((χ w ⟨k, hk⟩ : ℂˣ) : ℂ) • φ := by
    funext x
    exact hφ w ⟨k, hk⟩ x
  rw [hχ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _)))

end Arch

end AutomorphicForm
