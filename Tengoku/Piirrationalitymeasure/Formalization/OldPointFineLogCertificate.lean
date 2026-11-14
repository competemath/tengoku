import Tengoku.Piirrationalitymeasure.Formalization.OldPointLogCertificate
import Tengoku.Piirrationalitymeasure.Formalization.OldPointRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Refined root and finite logarithm certificates for the comparison (5.24). -/

namespace PiIrrationality

def oldFineRootLower : ℚ := 663395015246214081837884661997839984532988 / 10 ^ 40

def oldFineRootUpper : ℚ := 663395015246214081837884661997839984532989 / 10 ^ 40

/--
@isnad1 id=and.0h0v.s4.44d04490f23a from=translated src=- shape=e057f9cf vocab=12fea7ec
-/
theorem oldStationaryRoot_fine_isolation :
    (oldFineRootLower : ℝ) < oldStationaryRoot ∧ oldStationaryRoot < (oldFineRootUpper : ℝ) := by
  have hy : oldStationaryRoot ∈ Set.Ici (125 / 2 : ℝ) :=
    (oldStationaryCubic_root_gt oldStationaryRoot_spec.1 oldStationaryRoot_spec.2).le
  have hL : (oldFineRootLower : ℝ) ∈ Set.Ici (125 / 2 : ℝ) := by
    norm_num [Set.mem_Ici, oldFineRootLower]
  have hU : (oldFineRootUpper : ℝ) ∈ Set.Ici (125 / 2 : ℝ) := by
    norm_num [Set.mem_Ici, oldFineRootUpper]
  have hsL : oldStationaryCubic oldFineRootLower < 0 := by
    norm_num [oldStationaryCubic, oldFineRootLower]
  have hsU : 0 < oldStationaryCubic oldFineRootUpper := by
    norm_num [oldStationaryCubic, oldFineRootUpper]
  constructor
  · by_contra h
    have hm := oldStationaryCubic_strictMonoOn.monotoneOn hy hL (le_of_not_gt h)
    linarith [oldStationaryRoot_spec.2]
  · by_contra h
    have hm := oldStationaryCubic_strictMonoOn.monotoneOn hU hy (le_of_not_gt h)
    linarith [oldStationaryRoot_spec.2]

def oldFineLogInput (i : Fin 6) : ℚ :=
  match i.val with
  | 0 => oldFineRootLower
  | 1 => oldFineRootUpper
  | 2 => oldFineRootLower ^ 2 + 6 * oldFineRootLower + 25
  | 3 => oldFineRootUpper ^ 2 + 6 * oldFineRootUpper + 25
  | 4 => oldFineRootLower - 25
  | _ => oldFineRootUpper - 25

def oldFineLogScale (i : Fin 6) : ℤ :=
  match i.val with
  | 0 | 1 => 6
  | 2 | 3 => 12
  | _ => 5

def oldFineLogRounded (i : Fin 6) : ℤ :=
  match i.val with
  | 0 => 4194785519541647384265982054087055773404711859260253562468992
  | 1 => 4194785519541647384265982054087055773404713366657772413070399
  | 2 => 8481351788068393235666527852023115266260645437282965716520493
  | 3 => 8481351788068393235666527852023115266260648312074983100936459
  | 4 => 3721818496237562456575825213155616284345990927188012821417107
  | _ => 3721818496237562456575825213155616284345993346181864027894887

set_option maxRecDepth 100000 in
/--
@isnad1 id=and.0h1v.s6.a591fd07928e from=translated src=- shape=88957e64 vocab=d4eb1349
-/
theorem oldFineLogInput_range (i : Fin 6) :
    2 ^ oldFineLogScale i ≤ oldFineLogInput i ∧
      oldFineLogInput i ≤ 2 * 2 ^ oldFineLogScale i ∧ |oldFineLogScale i| ≤ 12 := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/--
@isnad1 id=eq.0h1v.s5.34ab06af4326 from=translated src=- shape=731b817d vocab=46370c25
-/
theorem oldFineLogRounded_value (i : Fin 6) :
    roundedScaledLog (oldFineLogInput i) (oldFineLogScale i) 120 (10 ^ 60) =
      oldFineLogRounded i := by
  revert i
  decide +kernel

/--
@isnad1 id=lt.0h1v.s6.d495e4462ab5 from=translated src=- shape=12d06da1 vocab=8300d37a
-/
theorem oldFineLog_enclosure (i : Fin 6) :
    |Real.log (oldFineLogInput i : ℝ) - (oldFineLogRounded i : ℝ) / 10 ^ 60| <
      (2000 : ℝ) / 10 ^ 60 := by
  obtain ⟨hL, hU, hk⟩ := oldFineLogInput_range i
  have h := roundedScaledLog_real_error (oldFineLogScale i) hL hU
  rw [oldFineLogRounded_value] at h
  have hk' : |(oldFineLogScale i : ℝ)| ≤ 12 := by exact_mod_cast hk
  apply h.trans_le
  calc
    _ ≤ 13 * ((964 : ℝ) / 10 ^ 120 + 120 / 10 ^ 60) := by gcongr; linarith
    _ ≤ _ := by norm_num

end PiIrrationality
