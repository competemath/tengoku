import Tengoku.Seed.RingTheory.Trace.Basic
import Tengoku.FltAnthropic.Definitions.Def_NumberField_StandardGlobalAddCharRat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace
open AutomorphicForm

noncomputable section

namespace NumberField.StandardAddChar

/--
@isnad1 id=eq.0h1v.s7.06db93437e32 from=translated src=- shape=ef3e8d53 vocab=8ebceecb
-/
theorem trace_rat_apply (x : ℚ) : Algebra.trace ℚ ℚ x = x := by
  have h := Algebra.trace_algebraMap (R := ℚ) (S := ℚ) x
  rw [Module.finrank_self, one_smul] at h
  rw [show algebraMap ℚ ℚ x = x from by
    rw [eq_ratCast (algebraMap ℚ ℚ) x, Rat.cast_id]] at h
  exact h

variable (F : Type) [Field F] [NumberField F]

structure AdelicTraceData where

  traceFin : FiniteAdeleRing (𝓞 F) F →+ FiniteAdeleRing (𝓞 ℚ) ℚ

  traceInf : InfiniteAdeleRing F →+ InfiniteAdeleRing ℚ

  traceFin_algebraMap (x : F) : traceFin (algebraMap F (FiniteAdeleRing (𝓞 F) F) x)
    = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x)

  traceInf_algebraMap (x : F) : traceInf (algebraMap F (InfiniteAdeleRing F) x)
    = algebraMap ℚ (InfiniteAdeleRing ℚ) (Algebra.trace ℚ F x)

  continuous_traceFin : Continuous traceFin

  continuous_traceInf : Continuous traceInf

  traceInf_surjective : Function.Surjective traceInf

namespace AdelicTraceData

variable {F}
variable (T : AdelicTraceData F)

def adelicTrace : AdeleRing (𝓞 F) F →+ AdeleRing (𝓞 ℚ) ℚ :=
  AddMonoidHom.prodMap T.traceInf T.traceFin

/--
@isnad1 id=eq.0h3v.s10.50b979830657 from=translated src=- shape=964ba96c vocab=ea731f80
-/
theorem adelicTrace_apply (u : AdeleRing (𝓞 F) F) :
    T.adelicTrace u = (T.traceInf u.1, T.traceFin u.2) := rfl

/--
@isnad1 id=eq.0h3v.s10.a5a31627c08a from=translated src=- shape=7fb4f565 vocab=a217d0ae
-/
theorem adelicTrace_algebraMap (x : F) :
    T.adelicTrace (algebraMap F (AdeleRing (𝓞 F) F) x)
      = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (Algebra.trace ℚ F x) := by
  refine Prod.ext ?_ ?_
  · exact T.traceInf_algebraMap x
  · exact T.traceFin_algebraMap x

/--
@isnad1 id=continuo.0h2v.s9.b43863728b9b from=translated src=- shape=d36d4176 vocab=5ca0e8c6
-/
theorem continuous_adelicTrace : Continuous T.adelicTrace :=
  T.continuous_traceInf.prodMap T.continuous_traceFin

def psiK : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  psiQ.compAddMonoidHom T.adelicTrace

/--
@isnad1 id=eq.0h3v.s9.3964a13e2880 from=translated src=- shape=581970ad vocab=8a162ee9
-/
theorem psiK_apply (u : AdeleRing (𝓞 F) F) : T.psiK u = psiQ (T.adelicTrace u) := rfl

/--
@isnad1 id=eq.0h3v.s9.0ab87110f8cb from=translated src=- shape=7d51f8c0 vocab=1786d89b
-/
theorem psiK_algebraMap (x : F) : T.psiK (algebraMap F (AdeleRing (𝓞 F) F) x) = 1 := by
  rw [psiK_apply, adelicTrace_algebraMap]
  exact psiQ_algebraMap (Algebra.trace ℚ F x)

/--
@isnad1 id=continuo.0h2v.s8.0875c8ffeff3 from=translated src=- shape=888be449 vocab=b548e87c
-/
theorem continuous_psiK : Continuous T.psiK :=
  continuous_psiQ.comp T.continuous_adelicTrace

end AdelicTraceData

def ratTraceData : AdelicTraceData ℚ where
  traceFin := AddMonoidHom.id _
  traceInf := AddMonoidHom.id _
  traceFin_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  traceInf_algebraMap x := by
    rw [AddMonoidHom.id_apply]; congr 1; exact (trace_rat_apply x).symm
  continuous_traceFin := continuous_id
  continuous_traceInf := continuous_id
  traceInf_surjective := Function.surjective_id

/--
@isnad1 id=eq.0h0v.s6.61e7e7287013 from=translated src=- shape=d12697b0 vocab=84f765ac
-/
theorem ratTraceData_psiK : ratTraceData.psiK = psiQ := by
  ext u
  rfl

end NumberField.StandardAddChar

end
