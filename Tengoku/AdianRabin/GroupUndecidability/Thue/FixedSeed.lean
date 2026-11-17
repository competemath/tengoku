import Tengoku.AdianRabin.GroupUndecidability.Machine.FixedTuringMachine
import Tengoku.AdianRabin.GroupUndecidability.Machine.SupportedTM1Thue
import Tengoku.AdianRabin.GroupUndecidability.Thue.FiniteReindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Undecidability
namespace FixedMachine

open Turing

/-- The canonical binary block code used to feed the finite Post bridge.-/
noncomputable def thueBinaryCode : TM1BinaryAdapter.Code TapeSymbol :=
  TM1BinaryAdapter.canonicalCode TapeSymbol

noncomputable abbrev ThueAlphabet (c : ToPartrec.Code) :=
  SupportedTM1Thue.Alphabet thueBinaryCode oneTapeProgram (oneTapeSupport c)

noncomputable def thuePostMachine (c : ToPartrec.Code) :
    PostMachine.Machine
      (TM0PostAdapter.Phase
        (SupportedTM1Thue.State thueBinaryCode oneTapeProgram
          (oneTapeSupport c))) := by
  letI : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.postMachine thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

noncomputable def thueSystem (c : ToPartrec.Code) :
    ThueSystem (ThueAlphabet c) :=
  PostMachine.system (thuePostMachine c)

noncomputable def thueStart (c : ToPartrec.Code) (input : List TapeSymbol) :
    List (ThueAlphabet c) := by
  letI : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.start thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c) input

theorem thue_iff_oneTape_eval_dom (c : ToPartrec.Code)
    (input : List TapeSymbol) :
    ThueEq (thueSystem c) (thueStart c input)
        (PostMachine.target : List (ThueAlphabet c)) ↔
      letI : Inhabited OneTapeState := oneTapeStateInhabited c
      (TM1.eval oneTapeProgram input).Dom := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.thue_iff_eval_dom thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c) input

theorem thueSystem_finite (c : ToPartrec.Code) : (thueSystem c).Finite := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.system_finite thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

noncomputable instance thueAlphabetFintype (c : ToPartrec.Code) :
    Fintype (ThueAlphabet c) := Fintype.ofFinite _

noncomputable instance thueAlphabetPrimcodable (c : ToPartrec.Code) :
    Primcodable (ThueAlphabet c) :=
  Primcodable.ofEquiv (Fin (Fintype.card (ThueAlphabet c)))
    (Fintype.equivFin (ThueAlphabet c))

theorem thueStart_computable (c : ToPartrec.Code) :
    Computable (thueStart c) := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.start_computable thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

end FixedMachine
end Undecidability
