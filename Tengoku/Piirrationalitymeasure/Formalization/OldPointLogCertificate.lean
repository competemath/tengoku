import Tengoku.Piirrationalitymeasure.Formalization.RoundedLogApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Kernel-checked rational 120-term logarithm certificates for the old-point bounds. -/

namespace PiIrrationality

def oldLogInput (i : Fin 8) : ℚ :=
  match i.val with
  | 0 => 66339501 / 10 ^ 6
  | 1 => 66339502 / 10 ^ 6
  | 2 => (66339501 / 10 ^ 6) ^ 2 + 6 * (66339501 / 10 ^ 6) + 25
  | 3 => (66339502 / 10 ^ 6) ^ 2 + 6 * (66339502 / 10 ^ 6) + 25
  | 4 => 66339501 / 10 ^ 6 - 25
  | 5 => 66339502 / 10 ^ 6 - 25
  | 6 => 2
  | _ => 3

def oldLogScale (i : Fin 8) : ℤ :=
  match i.val with
  | 0 | 1 => 6
  | 2 | 3 => 12
  | 4 | 5 => 5
  | _ => 1

def oldLogRounded (i : Fin 8) : ℤ :=
  match i.val with
  | 0 => 4194785511633517262675207823073799464929520738397053590989409
  | 1 => 4194785526707492456775814969411702120057295593078362295742951
  | 2 => 8481351772986618815033519970012993030104452464916246384542698
  | 3 => 8481351801734538999017916834949151295085259567184747292564875
  | 4 => 3721818483547002769971992561005464307818417660094045155189243
  | 5 => 3721818507736941296444065494994774577436040479167487248360939
  | 6 => 693147180559945309417232121458176568075500134360255254120652
  | _ => 1098612288668109691395245236922525704647490557822749451734643

set_option maxRecDepth 100000 in
/--
@isnad1 id=and.0h1v.s6.19c8544dd8d6 from=translated src=- shape=88957e64 vocab=0efcffd9
-/
theorem oldLogInput_range (i : Fin 8) :
    2 ^ oldLogScale i ≤ oldLogInput i ∧
      oldLogInput i ≤ 2 * 2 ^ oldLogScale i ∧ |oldLogScale i| ≤ 12 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/--
@isnad1 id=eq.0h1v.s5.6ad67ef50e6c from=translated src=- shape=731b817d vocab=3d0c3ec0
-/
theorem oldLogRounded_value (i : Fin 8) :
    roundedScaledLog (oldLogInput i) (oldLogScale i) 120 (10 ^ 60) = oldLogRounded i := by
  revert i
  decide +kernel

/--
@isnad1 id=lt.0h1v.s6.4b03fa05d028 from=translated src=- shape=12d06da1 vocab=2f864641
-/
theorem oldLog_enclosure (i : Fin 8) :
    |Real.log (oldLogInput i : ℝ) - (oldLogRounded i : ℝ) / 10 ^ 60| <
      (2000 : ℝ) / 10 ^ 60 := by
  obtain ⟨hL, hU, hk⟩ := oldLogInput_range i
  have h := roundedScaledLog_real_error (oldLogScale i) hL hU
  rw [oldLogRounded_value] at h
  have hk' : |(oldLogScale i : ℝ)| ≤ 12 := by exact_mod_cast hk
  apply h.trans_le
  calc
    _ ≤ 13 * ((964 : ℝ) / 10 ^ 120 + 120 / 10 ^ 60) := by gcongr; linarith
    _ ≤ _ := by norm_num

end PiIrrationality
