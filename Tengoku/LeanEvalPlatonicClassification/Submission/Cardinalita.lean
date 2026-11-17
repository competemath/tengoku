import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
CAMPAGNA #50, DIMENSIONI ALTE — LE TRE CARDINALITÀ SONO DISTINTE
(19 lug 2026).

In dimensione `d ≥ 5` i politopi regolari sono tre: il simplesso
(`d+1` vertici), l'ortoplesso (`2d`) e l'ipercubo (`2^d`). Per applicare
il minorante generico basta che le tre cardinalità siano distinte, e con
il numero di vertici come invariante separatore non serve dimostrare a
mano le non-similarità.

Qui il mattone aritmetico. La disuguaglianza chiave è `2d < 2^d` per
`d ≥ 5`, che si dimostra per induzione (base: 10 < 32; passo: se
`2d < 2^d` allora `2(d+1) = 2d + 2 < 2^d + 2^d = 2^(d+1)`, usando
`2 ≤ 2^d`).
-/

namespace LeanEval.Geometry.PlatonicClassification

/-- Per `d ≥ 3`, il doppio è strettamente minore della potenza.
@isnad1 id=lt.1h1v.s5.600b08a58561 from=translated src=- shape=63c02f1f vocab=2a3f5b88
-/
theorem due_mul_lt_two_pow : ∀ d : ℕ, 3 ≤ d → 2 * d < 2 ^ d := by
  intro d hd
  induction d with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · -- casi base: n+1 ∈ {3}
      interval_cases n <;> first | omega | norm_num
    · have hstep := ih (by omega)
      have hpow : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 * (n + 1) = 2 * n + 2 := by ring
        _ < 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-- **LE TRE CARDINALITÀ SONO DISTINTE** per `d ≥ 5`:
simplesso `d+1`, ortoplesso `2d`, ipercubo `2^d`.
@isnad1 id=and.1h1v.s6.ce918e94615c from=translated src=- shape=0addf515 vocab=3f16b8dd
-/
theorem cardinalita_distinte (d : ℕ) (hd : 5 ≤ d) :
    d + 1 < 2 * d ∧ 2 * d < 2 ^ d := by
  refine ⟨by omega, due_mul_lt_two_pow d (by omega)⟩

/-- La funzione che assegna a ciascuno dei tre il proprio numero di
vertici è iniettiva.
@isnad1 id=injectiv.1h1v.s6.7f1ea4e3be44 from=translated src=- shape=dd7807c4 vocab=61802828
-/
theorem card_tre_iniettiva (d : ℕ) (hd : 5 ≤ d) :
    Function.Injective (fun i : Fin 3 => ![d + 1, 2 * d, 2 ^ d] i) := by
  obtain ⟨h1, h2⟩ := cardinalita_distinte d hd
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

end LeanEval.Geometry.PlatonicClassification
