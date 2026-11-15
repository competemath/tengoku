import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped NumberField

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def twistedAdelicKernel {M : Type*} [AddCommMonoid M]
    (σA : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F)
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ : Matrix.GeneralLinearGroup (Fin 2) F,
    f (x⁻¹ * globalPoints (𝓞 F) F γ * σA y)

/--
@isnad1 id=eq.0h5v.s7.2489885f6aa3 from=translated src=- shape=7a7f7e27 vocab=e0466bc7
-/
theorem twistedAdelicKernel_id {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F (MonoidHom.id _) f x y = adelicKernel F f x y :=
  rfl

/--
@isnad1 id=eq.0h6v.s10.4b832979bbbe from=translated src=- shape=6c833939 vocab=504b6834
-/
theorem twistedAdelicKernel_one {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y y' : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F 1 f x y = twistedAdelicKernel F 1 f x y' :=
  rfl

end AutomorphicForm
