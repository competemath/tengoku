import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.AureoBase
import Tengoku.LeanEvalPlatonicClassification.Submission.CellVentiquattro
import Tengoku.LeanEvalPlatonicClassification.Submission.Ortoplesse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
I VERTICI DEL 120-CELL (21 lug 2026) — sette famiglie parametriche,
tutte cosferiche di raggio `2√2` (le norme quadre valgono 8 con
`φ² = φ+1`):

* **P1** (24): `2 · (24-cell)` — riuso di `vertVentiquattro`;
* **P2** (64): `(±1, ±1, ±1, ±√5)`, posizione di `√5` × segni;
* **P3** (64): `(±φ⁻², ±φ, ±φ, ±φ)` con `φ⁻² = 2−φ`;
* **P4** (64): `(±φ⁻¹, ±φ⁻¹, ±φ⁻¹, ±φ²)` con `φ⁻¹ = φ−1`, `φ² = φ+1`;
* **P5** (96): permutazioni PARI di `(0, ±φ⁻², ±1, ±φ²)`;
* **P6** (96): permutazioni PARI di `(0, ±φ⁻¹, ±φ, ±√5)`;
* **P7** (192): permutazioni PARI di `(±φ⁻¹, ±1, ±φ, ±2)`, segni pieni.

ATTENZIONE ALLA PARITÀ: le basi delle famiglie pari sono prese
nell'ordine classico (lo `0` in testa dove la referenza lo colloca):
riordinare la base cambierebbe il coset e darebbe l'orbita chirale
sbagliata.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-! ## Le sette famiglie -/

/-- P1: il 24-cell raddoppiato.-/
noncomputable def vertP1 (c : CodiceVentiquattro) : E 4 :=
  (2 : ℝ) • vertVentiquattro c

/-- P2: `√5` in posizione `i`, `±1` altrove.-/
noncomputable def vertP2 (i : Fin 4) (s : Fin 4 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => (if s j then 1 else -1) *
      (if j = i then Real.sqrt 5 else 1))

/--
@isnad1 id=eq.0h3v.s7.3a468411d2c5 from=translated src=- shape=ddaf9110 vocab=9d0275dd
-/
@[simp] theorem vertP2_apply (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    vertP2 i s j = (if s j then (1 : ℝ) else -1) *
      (if j = i then Real.sqrt 5 else 1) := by
  simp [vertP2]

/-- P3: `φ⁻² = 2−φ` in posizione `i`, `φ` altrove.-/
noncomputable def vertP3 (i : Fin 4) (s : Fin 4 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => (if s j then 1 else -1) *
      (if j = i then 2 - aureo else aureo))

/--
@isnad1 id=eq.0h3v.s7.3c3face72b74 from=translated src=- shape=2920018b vocab=3579625c
-/
@[simp] theorem vertP3_apply (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    vertP3 i s j = (if s j then (1 : ℝ) else -1) *
      (if j = i then 2 - aureo else aureo) := by
  simp [vertP3]

/-- P4: `φ² = φ+1` in posizione `i`, `φ⁻¹ = φ−1` altrove.-/
noncomputable def vertP4 (i : Fin 4) (s : Fin 4 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => (if s j then 1 else -1) *
      (if j = i then aureo + 1 else aureo - 1))

/--
@isnad1 id=eq.0h3v.s7.e84885ed29e3 from=translated src=- shape=14815629 vocab=f9417da2
-/
@[simp] theorem vertP4_apply (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    vertP4 i s j = (if s j then (1 : ℝ) else -1) *
      (if j = i then aureo + 1 else aureo - 1) := by
  simp [vertP4]

/-- La base della famiglia P5, nell'ordine classico.-/
noncomputable def base5 : Fin 4 → ℝ := ![0, 2 - aureo, 1, aureo + 1]

/-- La base della famiglia P6, nell'ordine classico.-/
noncomputable def base6 : Fin 4 → ℝ := ![0, aureo - 1, aureo, Real.sqrt 5]

/-- La base della famiglia P7, nell'ordine classico.-/
noncomputable def base7 : Fin 4 → ℝ := ![aureo - 1, 1, aureo, 2]

/-- Segni per basi con lo zero in testa (slot 0 fisso a `1`).-/
noncomputable def segnoZeroTesta (s : Fin 3 → Bool) : Fin 4 → ℝ :=
  ![1, if s 0 then 1 else -1, if s 1 then 1 else -1,
    if s 2 then 1 else -1]

/-- Segni pieni sulle quattro coordinate.-/
noncomputable def segnoPieno (s : Fin 4 → Bool) : Fin 4 → ℝ :=
  ![if s 0 then 1 else -1, if s 1 then 1 else -1,
    if s 2 then 1 else -1, if s 3 then 1 else -1]

/--
@isnad1 id=eq.0h2v.s5.d56f7a62b29b from=translated src=- shape=b4164dab vocab=044a4b04
-/
theorem segnoZeroTesta_sq (s : Fin 3 → Bool) (k : Fin 4) :
    segnoZeroTesta s k ^ 2 = 1 := by
  fin_cases k <;> simp [segnoZeroTesta] <;> split_ifs <;> norm_num

/--
@isnad1 id=eq.0h2v.s5.847a97daf7b9 from=translated src=- shape=b4164dab vocab=69f80227
-/
theorem segnoPieno_sq (s : Fin 4 → Bool) (k : Fin 4) :
    segnoPieno s k ^ 2 = 1 := by
  fin_cases k <;> simp [segnoPieno] <;> split_ifs <;> norm_num

/-- P5: permutazione pari della base `(0, φ⁻², 1, φ²)` coi segni.-/
noncomputable def vertP5 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => segnoZeroTesta s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base5 ((σ : Equiv.Perm (Fin 4)).symm j))

/-- P6: permutazione pari della base `(0, φ⁻¹, φ, √5)` coi segni.-/
noncomputable def vertP6 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => segnoZeroTesta s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base6 ((σ : Equiv.Perm (Fin 4)).symm j))

/-- P7: permutazione pari della base `(φ⁻¹, 1, φ, 2)` coi segni pieni.-/
noncomputable def vertP7 (σ : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => segnoPieno s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base7 ((σ : Equiv.Perm (Fin 4)).symm j))

/--
@isnad1 id=eq.0h3v.s9.525666867fb2 from=translated src=- shape=0de02669 vocab=bb10e3a5
-/
@[simp] theorem vertP5_apply (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (j : Fin 4) :
    vertP5 σ s j = segnoZeroTesta s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base5 ((σ : Equiv.Perm (Fin 4)).symm j) := by
  simp [vertP5]

/--
@isnad1 id=eq.0h3v.s9.382790caca49 from=translated src=- shape=0de02669 vocab=2c513461
-/
@[simp] theorem vertP6_apply (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (j : Fin 4) :
    vertP6 σ s j = segnoZeroTesta s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base6 ((σ : Equiv.Perm (Fin 4)).symm j) := by
  simp [vertP6]

/--
@isnad1 id=eq.0h3v.s9.7a67d176e144 from=translated src=- shape=0de02669 vocab=41b4a4e2
-/
@[simp] theorem vertP7_apply (σ : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) (j : Fin 4) :
    vertP7 σ s j = segnoPieno s ((σ : Equiv.Perm (Fin 4)).symm j) *
      base7 ((σ : Equiv.Perm (Fin 4)).symm j) := by
  simp [vertP7]

/-! ## Le norme: tutti su sfera di raggio `2√2` (norma quadra 8) -/

/--
@isnad1 id=eq.0h1v.s6.be9676d2b46a from=translated src=- shape=7b9ddabb vocab=146586ac
-/
theorem norm_sq_vertP1 (c : CodiceVentiquattro) : ‖vertP1 c‖ ^ 2 = 8 := by
  rw [vertP1, norm_smul, norm_vertVentiquattro]
  rw [Real.norm_eq_abs]
  rw [mul_pow, sq_abs, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/--
@isnad1 id=eq.0h2v.s6.23961bd84357 from=translated src=- shape=ca0e4976 vocab=12239c55
-/
theorem norm_sq_vertP2 (i : Fin 4) (s : Fin 4 → Bool) :
    ‖vertP2 i s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP2_apply]
  have hterm : ∀ j : Fin 4,
      ‖(if s j then (1 : ℝ) else -1) *
        (if j = i then Real.sqrt 5 else 1)‖ ^ 2
      = (if j = i then 5 else 1) := by
    intro j
    rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
    have h1 : (if s j then (1 : ℝ) else -1) ^ 2 = 1 := by
      split_ifs <;> norm_num
    rw [h1, one_mul]
    split_ifs
    · exact Real.sq_sqrt (by norm_num)
    · norm_num
  simp_rw [hterm]
  fin_cases i <;> rw [Fin.sum_univ_four] <;> simp <;> norm_num

/--
@isnad1 id=eq.0h2v.s6.de1ef4e24513 from=translated src=- shape=ca0e4976 vocab=8cfed055
-/
theorem norm_sq_vertP3 (i : Fin 4) (s : Fin 4 → Bool) :
    ‖vertP3 i s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP3_apply]
  have hterm : ∀ j : Fin 4,
      ‖(if s j then (1 : ℝ) else -1) *
        (if j = i then 2 - aureo else aureo)‖ ^ 2
      = (if j = i then (2 - aureo) ^ 2 else aureo ^ 2) := by
    intro j
    rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
    have h1 : (if s j then (1 : ℝ) else -1) ^ 2 = 1 := by
      split_ifs <;> norm_num
    rw [h1, one_mul]
    split_ifs <;> rfl
  simp_rw [hterm]
  fin_cases i <;> rw [Fin.sum_univ_four] <;> simp <;> nlinarith [aureo_sq]

/--
@isnad1 id=eq.0h2v.s6.98b12270501e from=translated src=- shape=ca0e4976 vocab=4b7683e7
-/
theorem norm_sq_vertP4 (i : Fin 4) (s : Fin 4 → Bool) :
    ‖vertP4 i s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP4_apply]
  have hterm : ∀ j : Fin 4,
      ‖(if s j then (1 : ℝ) else -1) *
        (if j = i then aureo + 1 else aureo - 1)‖ ^ 2
      = (if j = i then (aureo + 1) ^ 2 else (aureo - 1) ^ 2) := by
    intro j
    rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
    have h1 : (if s j then (1 : ℝ) else -1) ^ 2 = 1 := by
      split_ifs <;> norm_num
    rw [h1, one_mul]
    split_ifs <;> rfl
  simp_rw [hterm]
  fin_cases i <;> rw [Fin.sum_univ_four] <;> simp <;> nlinarith [aureo_sq]

/--
@isnad1 id=eq.2h3v.s9.6852d2cca61a from=translated src=- shape=1d2a736f vocab=74f45fb5
-/
theorem norm_sq_perm_block {sg : Fin 4 → ℝ} {bs : Fin 4 → ℝ}
    (σ : alternatingGroup (Fin 4))
    (hsg : ∀ k, sg k ^ 2 = 1)
    (htot : bs 0 ^ 2 + bs 1 ^ 2 + bs 2 ^ 2 + bs 3 ^ 2 = 8) :
    ∑ j : Fin 4, ‖sg ((σ : Equiv.Perm (Fin 4)).symm j) *
      bs ((σ : Equiv.Perm (Fin 4)).symm j)‖ ^ 2 = 8 := by
  have hre : ∑ j : Fin 4, ‖sg ((σ : Equiv.Perm (Fin 4)).symm j) *
        bs ((σ : Equiv.Perm (Fin 4)).symm j)‖ ^ 2
      = ∑ k : Fin 4, ‖sg k * bs k‖ ^ 2 :=
    Fintype.sum_equiv (σ : Equiv.Perm (Fin 4)).symm _ _ (fun j => rfl)
  rw [hre]
  have hterm : ∀ k : Fin 4, ‖sg k * bs k‖ ^ 2 = bs k ^ 2 := by
    intro k
    rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, hsg, one_mul]
  simp_rw [hterm]
  rw [Fin.sum_univ_four]
  exact htot

/--
@isnad1 id=eq.0h2v.s7.682fb6399cd7 from=translated src=- shape=e72b7806 vocab=4ec5005d
-/
theorem norm_sq_vertP5 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : ‖vertP5 σ s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP5_apply]
  apply norm_sq_perm_block σ (segnoZeroTesta_sq s)
  have h0 : base5 0 = 0 := rfl
  have h1 : base5 1 = 2 - aureo := rfl
  have h2 : base5 2 = 1 := rfl
  have h3 : base5 3 = aureo + 1 := rfl
  rw [h0, h1, h2, h3]
  nlinarith [aureo_sq]

/--
@isnad1 id=eq.0h2v.s7.b83b02e970df from=translated src=- shape=e72b7806 vocab=2893501b
-/
theorem norm_sq_vertP6 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : ‖vertP6 σ s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP6_apply]
  apply norm_sq_perm_block σ (segnoZeroTesta_sq s)
  have h0 : base6 0 = 0 := rfl
  have h1 : base6 1 = aureo - 1 := rfl
  have h2 : base6 2 = aureo := rfl
  have h3 : base6 3 = Real.sqrt 5 := rfl
  rw [h0, h1, h2, h3, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  nlinarith [aureo_sq]

/--
@isnad1 id=eq.0h2v.s7.1a915783b004 from=translated src=- shape=e72b7806 vocab=39944ebd
-/
theorem norm_sq_vertP7 (σ : alternatingGroup (Fin 4))
    (s : Fin 4 → Bool) : ‖vertP7 σ s‖ ^ 2 = 8 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vertP7_apply]
  apply norm_sq_perm_block σ (segnoPieno_sq s)
  have h0 : base7 0 = aureo - 1 := rfl
  have h1 : base7 1 = 1 := rfl
  have h2 : base7 2 = aureo := rfl
  have h3 : base7 3 = 2 := rfl
  rw [h0, h1, h2, h3]
  nlinarith [aureo_sq]

/-! ## Iniettività: due pattern generali, sette istanze -/

/-- Iniettività del pattern posizionale: valore speciale `a` in posizione
`i`, valore comune `b` altrove, segni liberi.
@isnad1 id=injectiv.3h2v.s11.6ab1ef412601 from=translated src=- shape=cb8bac7b vocab=5b7df472
-/
theorem inj_posizionale {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    Function.Injective (fun p : Fin 4 × (Fin 4 → Bool) =>
      ((EuclideanSpace.equiv (Fin 4) ℝ).symm
        (fun j => (if p.2 j then (1 : ℝ) else -1) *
          (if j = p.1 then a else b)) : E 4)) := by
  rintro ⟨i, s⟩ ⟨i', s'⟩ h
  simp only at h
  have happ : ∀ j : Fin 4,
      (if s j then (1 : ℝ) else -1) * (if j = i then a else b)
      = (if s' j then (1 : ℝ) else -1) * (if j = i' then a else b) := by
    intro j
    simpa using congrArg (fun v : E 4 => v j) h
  have hii : i = i' := by
    by_contra hne
    have h1 := happ i
    rw [ite_eq_left rfl, ite_eq_right hne] at h1
    have habs := congrArg abs h1
    rw [abs_mul, abs_mul] at habs
    have hs1 : |if s i then (1 : ℝ) else -1| = 1 := by
      split_ifs <;> norm_num
    have hs2 : |if s' i then (1 : ℝ) else -1| = 1 := by
      split_ifs <;> norm_num
    rw [hs1, hs2, one_mul, one_mul, abs_of_pos ha, abs_of_pos hb] at habs
    exact hab habs
  subst hii
  have hss : s = s' := by
    funext j
    by_cases hji : j = i
    · have h1 := happ j
      rw [ite_eq_left hji] at h1
      have h2 := mul_right_cancel₀ (ne_of_gt ha) h1
      cases hs : s j <;> cases hs' : s' j <;> rw [hs, hs'] at h2 <;>
        first | rfl | (exfalso; norm_num at h2)
    · have h1 := happ j
      rw [ite_eq_right hji] at h1
      have h2 := mul_right_cancel₀ (ne_of_gt hb) h1
      cases hs : s j <;> cases hs' : s' j <;> rw [hs, hs'] at h2 <;>
        first | rfl | (exfalso; norm_num at h2)
  rw [hss]

/-- Iniettività del pattern permutativo: base con valori assoluti
distinti, segni recuperabili dalle coordinate non nulle.
@isnad1 id=injectiv.4h3v.s11.71628489aaed from=translated src=- shape=f567e1bb vocab=b7a580f3
-/
theorem inj_permutativo {S : Type*} (bs : Fin 4 → ℝ) (sg : S → Fin 4 → ℝ)
    (hbs_nn : ∀ k, 0 ≤ bs k)
    (hbs_inj : ∀ k k' : Fin 4, bs k = bs k' → k = k')
    (hsg : ∀ s k, |sg s k| = 1)
    (hrec : ∀ s s' : S, (∀ k, bs k ≠ 0 → sg s k = sg s' k) → s = s') :
    Function.Injective (fun p : alternatingGroup (Fin 4) × S =>
      ((EuclideanSpace.equiv (Fin 4) ℝ).symm
        (fun j => sg p.2 ((p.1 : Equiv.Perm (Fin 4)).symm j) *
          bs ((p.1 : Equiv.Perm (Fin 4)).symm j)) : E 4)) := by
  rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
  simp only at h
  have happ : ∀ j : Fin 4,
      sg s ((σ : Equiv.Perm (Fin 4)).symm j) *
        bs ((σ : Equiv.Perm (Fin 4)).symm j)
      = sg s' ((σ' : Equiv.Perm (Fin 4)).symm j) *
        bs ((σ' : Equiv.Perm (Fin 4)).symm j) := by
    intro j
    simpa using congrArg (fun v : E 4 => v j) h
  have hσσ : ∀ k : Fin 4, (σ : Equiv.Perm (Fin 4)) k =
      (σ' : Equiv.Perm (Fin 4)) k := by
    intro k
    have h1 := happ ((σ : Equiv.Perm (Fin 4)) k)
    rw [Equiv.symm_apply_apply] at h1
    have habs := congrArg abs h1
    rw [abs_mul, abs_mul, hsg, hsg, one_mul, one_mul,
      abs_of_nonneg (hbs_nn _), abs_of_nonneg (hbs_nn _)] at habs
    have hk := hbs_inj _ _ habs
    have h2 := congrArg (σ' : Equiv.Perm (Fin 4)) hk
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm
  have hσ : σ = σ' := Subtype.ext (Equiv.ext hσσ)
  subst hσ
  have hs : s = s' := by
    apply hrec
    intro k hbk
    have h1 := happ ((σ : Equiv.Perm (Fin 4)) k)
    rw [Equiv.symm_apply_apply] at h1
    exact mul_right_cancel₀ hbk h1
  rw [hs]

/-- Recupero dei segni per il pattern zero-in-testa (slot 1,2,3 attivi).
@isnad1 id=eq.4h3v.s7.e86ecde06c08 from=translated src=- shape=b9e1856a vocab=8fd31c8f
-/
theorem rec_segnoZeroTesta {bs : Fin 4 → ℝ}
    (h1 : bs 1 ≠ 0) (h2 : bs 2 ≠ 0) (h3 : bs 3 ≠ 0) :
    ∀ s s' : Fin 3 → Bool,
      (∀ k, bs k ≠ 0 → segnoZeroTesta s k = segnoZeroTesta s' k) →
      s = s' := by
  intro s s' hk
  funext m
  fin_cases m
  · show s 0 = s' 0
    have h := hk 1 h1
    have h0 : (if s 0 then (1 : ℝ) else -1)
        = (if s' 0 then 1 else -1) := h
    cases hs : s 0 <;> cases hs' : s' 0 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)
  · show s 1 = s' 1
    have h := hk 2 h2
    have h0 : (if s 1 then (1 : ℝ) else -1)
        = (if s' 1 then 1 else -1) := h
    cases hs : s 1 <;> cases hs' : s' 1 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)
  · show s 2 = s' 2
    have h := hk 3 h3
    have h0 : (if s 2 then (1 : ℝ) else -1)
        = (if s' 2 then 1 else -1) := h
    cases hs : s 2 <;> cases hs' : s' 2 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)

/-- Recupero dei segni per il pattern pieno (tutti gli slot attivi).
@isnad1 id=eq.2h3v.s6.ff67a19668b0 from=translated src=- shape=8340b7da vocab=fe7efd26
-/
theorem rec_segnoPieno {bs : Fin 4 → ℝ} (hbs : ∀ k, bs k ≠ 0) :
    ∀ s s' : Fin 4 → Bool,
      (∀ k, bs k ≠ 0 → segnoPieno s k = segnoPieno s' k) → s = s' := by
  intro s s' hk
  funext m
  fin_cases m
  · show s 0 = s' 0
    have h := hk 0 (hbs 0)
    have h0 : (if s 0 then (1 : ℝ) else -1)
        = (if s' 0 then 1 else -1) := h
    cases hs : s 0 <;> cases hs' : s' 0 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)
  · show s 1 = s' 1
    have h := hk 1 (hbs 1)
    have h0 : (if s 1 then (1 : ℝ) else -1)
        = (if s' 1 then 1 else -1) := h
    cases hs : s 1 <;> cases hs' : s' 1 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)
  · show s 2 = s' 2
    have h := hk 2 (hbs 2)
    have h0 : (if s 2 then (1 : ℝ) else -1)
        = (if s' 2 then 1 else -1) := h
    cases hs : s 2 <;> cases hs' : s' 2 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)
  · show s 3 = s' 3
    have h := hk 3 (hbs 3)
    have h0 : (if s 3 then (1 : ℝ) else -1)
        = (if s' 3 then 1 else -1) := h
    cases hs : s 3 <;> cases hs' : s' 3 <;>
      first
        | rfl
        | (exfalso; rw [hs, hs'] at h0; norm_num at h0)

/-! ## Le sette iniettività -/

/--
@isnad1 id=eq.0h2v.s4.2882188e4ede from=translated src=- shape=8ac8adb9 vocab=a9d23f2c
-/
theorem segnoZeroTesta_abs (s : Fin 3 → Bool) (k : Fin 4) :
    |segnoZeroTesta s k| = 1 := by
  fin_cases k <;> simp [segnoZeroTesta] <;> split_ifs <;> norm_num

/--
@isnad1 id=eq.0h2v.s4.fda647f5add8 from=translated src=- shape=8ac8adb9 vocab=13e0248b
-/
theorem segnoPieno_abs (s : Fin 4 → Bool) (k : Fin 4) :
    |segnoPieno s k| = 1 := by
  fin_cases k <;> simp [segnoPieno] <;> split_ifs <;> norm_num

/--
@isnad1 id=le.0h1v.s4.bc17843f4d43 from=translated src=- shape=de9abb23 vocab=10cddf90
-/
theorem base5_nonneg (k : Fin 4) : 0 ≤ base5 k := by
  have hb := aureo_bounds
  fin_cases k
  · exact le_rfl
  · show (0 : ℝ) ≤ 2 - aureo
    linarith [hb.2]
  · show (0 : ℝ) ≤ 1
    norm_num
  · show (0 : ℝ) ≤ aureo + 1
    linarith [hb.1]

/--
@isnad1 id=le.0h1v.s4.5bd44c832669 from=translated src=- shape=de9abb23 vocab=605bd9ca
-/
theorem base6_nonneg (k : Fin 4) : 0 ≤ base6 k := by
  have hb := aureo_bounds
  fin_cases k
  · exact le_rfl
  · show (0 : ℝ) ≤ aureo - 1
    linarith [hb.1]
  · show (0 : ℝ) ≤ aureo
    linarith [hb.1]
  · show (0 : ℝ) ≤ Real.sqrt 5
    exact Real.sqrt_nonneg 5

/--
@isnad1 id=le.0h1v.s4.5fbdc384edbe from=translated src=- shape=de9abb23 vocab=749d8987
-/
theorem base7_nonneg (k : Fin 4) : 0 ≤ base7 k := by
  have hb := aureo_bounds
  fin_cases k
  · show (0 : ℝ) ≤ aureo - 1
    linarith [hb.1]
  · show (0 : ℝ) ≤ 1
    norm_num
  · show (0 : ℝ) ≤ aureo
    linarith [hb.1]
  · show (0 : ℝ) ≤ 2
    norm_num

/--
@isnad1 id=eq.1h2v.s4.3c853adb9431 from=translated src=- shape=e8c15deb vocab=4d9511ca
-/
theorem base5_inj : ∀ k k' : Fin 4, base5 k = base5 k' → k = k' := by
  have hb := aureo_bounds
  intro k k' h
  fin_cases k <;> fin_cases k' <;>
    first
      | rfl
      | (exfalso; simp [base5] at h; done)
      | (exfalso; simp [base5] at h; nlinarith [hb.1, hb.2])

/--
@isnad1 id=eq.1h2v.s4.149b57d59075 from=translated src=- shape=e8c15deb vocab=1be5e3af
-/
theorem base6_inj : ∀ k k' : Fin 4, base6 k = base6 k' → k = k' := by
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  intro k k' h
  fin_cases k <;> fin_cases k' <;>
    first
      | rfl
      | (exfalso; simp [base6] at h; done)
      | (exfalso; simp [base6] at h; nlinarith [hb.1, hb.2, lo, hi])

/--
@isnad1 id=eq.1h2v.s4.b4976a4984b5 from=translated src=- shape=e8c15deb vocab=7be3362d
-/
theorem base7_inj : ∀ k k' : Fin 4, base7 k = base7 k' → k = k' := by
  have hb := aureo_bounds
  intro k k' h
  fin_cases k <;> fin_cases k' <;>
    first
      | rfl
      | (exfalso; simp [base7] at h; done)
      | (exfalso; simp [base7] at h; nlinarith [hb.1, hb.2])

/--
@isnad1 id=injectiv.0h0v.s3.b7fa23978ca5 from=translated src=- shape=d3a93718 vocab=efc51a86
-/
theorem vertP1_injective : Function.Injective vertP1 := by
  intro c c' h
  apply vertVentiquattro_injective
  exact smul_right_injective (E 4) (by norm_num : (2 : ℝ) ≠ 0) h

/--
@isnad1 id=injectiv.0h0v.s6.7697e3972363 from=translated src=- shape=b020afa6 vocab=1d916067
-/
theorem vertP2_injective :
    Function.Injective (fun p : Fin 4 × (Fin 4 → Bool) =>
      vertP2 p.1 p.2) := by
  have h5 : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  exact inj_posizionale h5 one_pos (by intro h; linarith)

/--
@isnad1 id=injectiv.0h0v.s6.59c9bb92bf9f from=translated src=- shape=b020afa6 vocab=fcebd8e2
-/
theorem vertP3_injective :
    Function.Injective (fun p : Fin 4 × (Fin 4 → Bool) =>
      vertP3 p.1 p.2) := by
  have hb := aureo_bounds
  exact inj_posizionale (by linarith [hb.2]) aureo_pos
    (by intro h; linarith [hb.1, hb.2])

/--
@isnad1 id=injectiv.0h0v.s6.80e846a1d600 from=translated src=- shape=b020afa6 vocab=8ed0b7a0
-/
theorem vertP4_injective :
    Function.Injective (fun p : Fin 4 × (Fin 4 → Bool) =>
      vertP4 p.1 p.2) := by
  have hb := aureo_bounds
  exact inj_posizionale (by linarith [hb.1]) aureo_sub_one_pos
    (by intro h; linarith [hb.1])

/--
@isnad1 id=injectiv.0h0v.s8.ce0d6812ebfc from=translated src=- shape=3e84d5f1 vocab=47d189c5
-/
theorem vertP5_injective :
    Function.Injective (fun p :
      alternatingGroup (Fin 4) × (Fin 3 → Bool) => vertP5 p.1 p.2) := by
  have hb := aureo_bounds
  exact inj_permutativo base5 segnoZeroTesta base5_nonneg base5_inj
    segnoZeroTesta_abs
    (rec_segnoZeroTesta
      (by show (2 : ℝ) - aureo ≠ 0; intro h; linarith [hb.2])
      (by show (1 : ℝ) ≠ 0; norm_num)
      (by show aureo + 1 ≠ 0; intro h; linarith [hb.1]))

/--
@isnad1 id=injectiv.0h0v.s8.84c6af5293c9 from=translated src=- shape=3e84d5f1 vocab=0a5b67b4
-/
theorem vertP6_injective :
    Function.Injective (fun p :
      alternatingGroup (Fin 4) × (Fin 3 → Bool) => vertP6 p.1 p.2) := by
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  exact inj_permutativo base6 segnoZeroTesta base6_nonneg base6_inj
    segnoZeroTesta_abs
    (rec_segnoZeroTesta
      (by show aureo - 1 ≠ 0; intro h; linarith [hb.1])
      (by show aureo ≠ 0; intro h; linarith [hb.1])
      (by show Real.sqrt 5 ≠ 0; intro h; linarith))

/--
@isnad1 id=injectiv.0h0v.s8.a1b8b41bf1e5 from=translated src=- shape=3e84d5f1 vocab=c2af76c4
-/
theorem vertP7_injective :
    Function.Injective (fun p :
      alternatingGroup (Fin 4) × (Fin 4 → Bool) => vertP7 p.1 p.2) := by
  have hb := aureo_bounds
  refine inj_permutativo base7 segnoPieno base7_nonneg base7_inj
    segnoPieno_abs (rec_segnoPieno ?_)
  intro k
  fin_cases k
  · show aureo - 1 ≠ 0
    intro h
    linarith [hb.1]
  · show (1 : ℝ) ≠ 0
    norm_num
  · show aureo ≠ 0
    intro h
    linarith [hb.1]
  · show (2 : ℝ) ≠ 0
    norm_num

/-! ## Range dei valori assoluti e testimoni per le disgiunzioni -/

/--
@isnad1 id=eq.0h1v.s4.689ce2f36bd3 from=translated src=- shape=562e4a6d vocab=5dab1f6e
-/
theorem abs_segnoVentiquattro (b : Bool) : |segnoVentiquattro b| = 1 := by
  cases b <;> simp [segnoVentiquattro] <;> norm_num

/--
@isnad1 id=eq.0h2v.s7.528ccd982c1c from=translated src=- shape=0a1efeba vocab=77eb31e2
-/
theorem vertP1_coord (c : CodiceVentiquattro) (j : Fin 4) :
    vertP1 c j = 2 * vertVentiquattro c j := by
  rw [vertP1, PiLp.smul_apply, smul_eq_mul]

/--
@isnad1 id=or.0h2v.s7.f0d8b33399ca from=translated src=- shape=05abdeb2 vocab=67f57783
-/
theorem vertP1_range (c : CodiceVentiquattro) (j : Fin 4) :
    |vertP1 c j| = 0 ∨ |vertP1 c j| = 2 := by
  rw [vertP1_coord, abs_mul, vertVentiquattro_apply]
  by_cases h1 : j = indicePrimoVentiquattro c
  · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; exact indicePrimo_ne_indiceSecondo c),
      add_zero, abs_segnoVentiquattro]
    right
    norm_num
  · by_cases h2 : j = indiceSecondoVentiquattro c
    · rw [ite_eq_right h1, ite_eq_left h2, zero_add, abs_segnoVentiquattro]
      right
      norm_num
    · rw [ite_eq_right h1, ite_eq_right h2, add_zero]
      left
      norm_num

/--
@isnad1 id=eq.0h1v.s6.72d4989a8d17 from=translated src=- shape=6a7a9117 vocab=50bf82bb
-/
theorem vertP1_testimone (c : CodiceVentiquattro) :
    |vertP1 c (indicePrimoVentiquattro c)| = 2 := by
  rw [vertP1_coord, vertVentiquattro_apply_primo, abs_mul,
    abs_segnoVentiquattro]
  norm_num

/--
@isnad1 id=ex.0h1v.s6.d5f17cab96d9 from=translated src=- shape=21441992 vocab=67f57783
-/
theorem vertP1_testimone_zero (c : CodiceVentiquattro) :
    ∃ j, |vertP1 c j| = 0 := by
  classical
  have hne : ({indicePrimoVentiquattro c,
      indiceSecondoVentiquattro c}ᶜ : Finset (Fin 4)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    have hle : ({indicePrimoVentiquattro c,
        indiceSecondoVentiquattro c} : Finset (Fin 4)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have hcard : Fintype.card (Fin 4) = 4 := by simp
    omega
  obtain ⟨j, hj⟩ := hne
  rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hj
  push Not at hj
  refine ⟨j, ?_⟩
  rw [vertP1_coord, abs_mul, vertVentiquattro_apply,
    ite_eq_right hj.1, ite_eq_right hj.2, add_zero]
  norm_num

/--
@isnad1 id=or.0h3v.s7.f21379686ba6 from=translated src=- shape=205311e5 vocab=1b7a4d00
-/
theorem vertP2_range (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    |vertP2 i s j| = 1 ∨ |vertP2 i s j| = Real.sqrt 5 := by
  rw [vertP2_apply, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  by_cases hji : j = i
  · right
    rw [ite_eq_left hji]
    exact abs_of_nonneg (Real.sqrt_nonneg 5)
  · left
    rw [ite_eq_right hji]
    norm_num

/--
@isnad1 id=eq.0h2v.s6.7dc640dad5a5 from=translated src=- shape=98e15901 vocab=1b7a4d00
-/
theorem vertP2_testimone (i : Fin 4) (s : Fin 4 → Bool) :
    |vertP2 i s i| = Real.sqrt 5 := by
  rw [vertP2_apply, ite_eq_left rfl, abs_mul]
  have hsg : |if s i then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  exact abs_of_nonneg (Real.sqrt_nonneg 5)

/--
@isnad1 id=ex.0h2v.s6.66323287d7cc from=translated src=- shape=c06cf930 vocab=5cfcf23e
-/
theorem vertP2_testimone_uno (i : Fin 4) (s : Fin 4 → Bool) :
    ∃ j, |vertP2 i s j| = 1 := by
  obtain ⟨j, hj⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [vertP2_apply, ite_eq_right hj, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg]
  norm_num

/--
@isnad1 id=or.0h3v.s7.5cf6abcc2d87 from=translated src=- shape=5682a07d vocab=555cd7f7
-/
theorem vertP3_range (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    |vertP3 i s j| = 2 - aureo ∨ |vertP3 i s j| = aureo := by
  have hb := aureo_bounds
  rw [vertP3_apply, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  by_cases hji : j = i
  · left
    rw [ite_eq_left hji]
    exact abs_of_nonneg (by linarith [hb.2])
  · right
    rw [ite_eq_right hji]
    exact abs_of_nonneg (by linarith [hb.1])

/--
@isnad1 id=eq.0h2v.s7.9180ddabe1d8 from=translated src=- shape=373c68aa vocab=555cd7f7
-/
theorem vertP3_testimone (i : Fin 4) (s : Fin 4 → Bool) :
    |vertP3 i s i| = 2 - aureo := by
  have hb := aureo_bounds
  rw [vertP3_apply, ite_eq_left rfl, abs_mul]
  have hsg : |if s i then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  exact abs_of_nonneg (by linarith [hb.2])

/--
@isnad1 id=ex.0h2v.s6.a963fe04ddfb from=translated src=- shape=56c7b03e vocab=0160584f
-/
theorem vertP3_testimone_aureo (i : Fin 4) (s : Fin 4 → Bool) :
    ∃ j, |vertP3 i s j| = aureo := by
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [vertP3_apply, ite_eq_right hj, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  exact abs_of_nonneg (by linarith [hb.1])

/--
@isnad1 id=or.0h3v.s7.7e5e9f8cf716 from=translated src=- shape=3fd991a1 vocab=0d8fb0e1
-/
theorem vertP4_range (i : Fin 4) (s : Fin 4 → Bool) (j : Fin 4) :
    |vertP4 i s j| = aureo - 1 ∨ |vertP4 i s j| = aureo + 1 := by
  have hb := aureo_bounds
  rw [vertP4_apply, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  by_cases hji : j = i
  · right
    rw [ite_eq_left hji]
    exact abs_of_nonneg (by linarith [hb.1])
  · left
    rw [ite_eq_right hji]
    exact abs_of_nonneg (by linarith [hb.1])

/--
@isnad1 id=eq.0h2v.s6.6f454bfc0b16 from=translated src=- shape=d9241e17 vocab=2215d1de
-/
theorem vertP4_testimone (i : Fin 4) (s : Fin 4 → Bool) :
    |vertP4 i s i| = aureo + 1 := by
  have hb := aureo_bounds
  rw [vertP4_apply, ite_eq_left rfl, abs_mul]
  have hsg : |if s i then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  exact abs_of_nonneg (by linarith [hb.1])

/--
@isnad1 id=ex.0h2v.s7.74b86a343dde from=translated src=- shape=47e9cdea vocab=c8d64b06
-/
theorem vertP4_testimone_inv (i : Fin 4) (s : Fin 4 → Bool) :
    ∃ j, |vertP4 i s j| = aureo - 1 := by
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := exists_ne i
  refine ⟨j, ?_⟩
  rw [vertP4_apply, ite_eq_right hj, abs_mul]
  have hsg : |if s j then (1 : ℝ) else -1| = 1 := by
    split_ifs <;> norm_num
  rw [hsg, one_mul]
  exact abs_of_nonneg (by linarith [hb.1])

/-- Il valore assoluto di un blocco permutativo in posizione `σ k`.
@isnad1 id=eq.2h4v.s9.ed6c8b35e8bd from=translated src=- shape=a3c93d17 vocab=f4617edb
-/
theorem perm_at_abs {sg : Fin 4 → ℝ} {bs : Fin 4 → ℝ}
    (σ : alternatingGroup (Fin 4))
    (hsg : ∀ k, |sg k| = 1) (hnn : ∀ k, 0 ≤ bs k) (k : Fin 4) :
    |sg ((σ : Equiv.Perm (Fin 4)).symm ((σ : Equiv.Perm (Fin 4)) k)) *
      bs ((σ : Equiv.Perm (Fin 4)).symm ((σ : Equiv.Perm (Fin 4)) k))|
      = bs k := by
  rw [Equiv.symm_apply_apply, abs_mul, hsg, one_mul,
    abs_of_nonneg (hnn k)]

/--
@isnad1 id=or.0h3v.s8.da43a06a6845 from=translated src=- shape=d0508033 vocab=3b908855
-/
theorem vertP5_range (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool)
    (j : Fin 4) :
    |vertP5 σ s j| = 0 ∨ |vertP5 σ s j| = 2 - aureo ∨
      |vertP5 σ s j| = 1 ∨ |vertP5 σ s j| = aureo + 1 := by
  rw [vertP5_apply, abs_mul, segnoZeroTesta_abs, one_mul,
    abs_of_nonneg (base5_nonneg _)]
  have hk : ∀ k : Fin 4, base5 k = 0 ∨ base5 k = 2 - aureo ∨
      base5 k = 1 ∨ base5 k = aureo + 1 := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  exact hk _

/--
@isnad1 id=ex.0h2v.s7.c1c8ab7996eb from=translated src=- shape=c4726c37 vocab=18bda3df
-/
theorem vertP5_testimone_zero (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : ∃ j, |vertP5 σ s j| = 0 := by
  refine ⟨(σ : Equiv.Perm (Fin 4)) 0, ?_⟩
  rw [vertP5_apply]
  have := perm_at_abs σ (segnoZeroTesta_abs s) base5_nonneg 0
  rw [this]
  rfl

/--
@isnad1 id=ex.0h2v.s7.d38a260bd8d3 from=translated src=- shape=c4726c37 vocab=18bda3df
-/
theorem vertP5_testimone_uno (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : ∃ j, |vertP5 σ s j| = 1 := by
  refine ⟨(σ : Equiv.Perm (Fin 4)) 2, ?_⟩
  rw [vertP5_apply]
  have := perm_at_abs σ (segnoZeroTesta_abs s) base5_nonneg 2
  rw [this]
  rfl

/--
@isnad1 id=or.0h3v.s8.dbb88f04fad8 from=translated src=- shape=783cdecd vocab=0dca29df
-/
theorem vertP6_range (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool)
    (j : Fin 4) :
    |vertP6 σ s j| = 0 ∨ |vertP6 σ s j| = aureo - 1 ∨
      |vertP6 σ s j| = aureo ∨ |vertP6 σ s j| = Real.sqrt 5 := by
  rw [vertP6_apply, abs_mul, segnoZeroTesta_abs, one_mul,
    abs_of_nonneg (base6_nonneg _)]
  have hk : ∀ k : Fin 4, base6 k = 0 ∨ base6 k = aureo - 1 ∨
      base6 k = aureo ∨ base6 k = Real.sqrt 5 := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  exact hk _

/--
@isnad1 id=ex.0h2v.s7.cf1e622b0a73 from=translated src=- shape=0f56fcb0 vocab=2c5b076a
-/
theorem vertP6_testimone (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : ∃ j, |vertP6 σ s j| = Real.sqrt 5 := by
  refine ⟨(σ : Equiv.Perm (Fin 4)) 3, ?_⟩
  rw [vertP6_apply]
  have := perm_at_abs σ (segnoZeroTesta_abs s) base6_nonneg 3
  rw [this]
  rfl

/--
@isnad1 id=or.0h3v.s8.1832957ddb8e from=translated src=- shape=16ad7afd vocab=c0b15068
-/
theorem vertP7_range (σ : alternatingGroup (Fin 4)) (s : Fin 4 → Bool)
    (j : Fin 4) :
    |vertP7 σ s j| = aureo - 1 ∨ |vertP7 σ s j| = 1 ∨
      |vertP7 σ s j| = aureo ∨ |vertP7 σ s j| = 2 := by
  rw [vertP7_apply, abs_mul, segnoPieno_abs, one_mul,
    abs_of_nonneg (base7_nonneg _)]
  have hk : ∀ k : Fin 4, base7 k = aureo - 1 ∨ base7 k = 1 ∨
      base7 k = aureo ∨ base7 k = 2 := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  exact hk _

/-! ## Le ventun disgiunzioni fra le famiglie -/

/--
@isnad1 id=ne.0h3v.s4.07e5d194ac9d from=translated src=- shape=00d1103e vocab=0aae445d
-/
theorem vertP1_ne_vertP2 (c : CodiceVentiquattro) (i : Fin 4)
    (s : Fin 4 → Bool) : vertP1 c ≠ vertP2 i s := by
  intro h
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP1_testimone c
  rw [h] at ht
  rcases vertP2_range i s (indicePrimoVentiquattro c) with hr | hr <;>
    rw [ht] at hr <;> linarith

/--
@isnad1 id=ne.0h3v.s4.9d1d557f7b89 from=translated src=- shape=00d1103e vocab=38957def
-/
theorem vertP1_ne_vertP3 (c : CodiceVentiquattro) (i : Fin 4)
    (s : Fin 4 → Bool) : vertP1 c ≠ vertP3 i s := by
  intro h
  have hb := aureo_bounds
  have ht := vertP1_testimone c
  rw [h] at ht
  rcases vertP3_range i s (indicePrimoVentiquattro c) with hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h3v.s4.290583badc3b from=translated src=- shape=00d1103e vocab=28ab9261
-/
theorem vertP1_ne_vertP4 (c : CodiceVentiquattro) (i : Fin 4)
    (s : Fin 4 → Bool) : vertP1 c ≠ vertP4 i s := by
  intro h
  have hb := aureo_bounds
  have ht := vertP1_testimone c
  rw [h] at ht
  rcases vertP4_range i s (indicePrimoVentiquattro c) with hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h3v.s6.5947f94ad625 from=translated src=- shape=04aa1b85 vocab=63d0c153
-/
theorem vertP1_ne_vertP5 (c : CodiceVentiquattro)
    (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) :
    vertP1 c ≠ vertP5 σ s := by
  intro h
  have hb := aureo_bounds
  have ht := vertP1_testimone c
  rw [h] at ht
  rcases vertP5_range σ s (indicePrimoVentiquattro c) with
    hr | hr | hr | hr <;> rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h3v.s6.006270f576bf from=translated src=- shape=04aa1b85 vocab=3ff596ff
-/
theorem vertP1_ne_vertP6 (c : CodiceVentiquattro)
    (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) :
    vertP1 c ≠ vertP6 σ s := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP1_testimone c
  rw [h] at ht
  rcases vertP6_range σ s (indicePrimoVentiquattro c) with
    hr | hr | hr | hr <;> rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h3v.s6.a0710a1ef29b from=translated src=- shape=04aa1b85 vocab=9c20c94a
-/
theorem vertP1_ne_vertP7 (c : CodiceVentiquattro)
    (σ : alternatingGroup (Fin 4)) (s : Fin 4 → Bool) :
    vertP1 c ≠ vertP7 σ s := by
  intro h
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := vertP1_testimone_zero c
  rw [h] at hj
  rcases vertP7_range σ s j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s5.670c00b7ac9c from=translated src=- shape=fadd8250 vocab=6267ac18
-/
theorem vertP2_ne_vertP3 (i : Fin 4) (s : Fin 4 → Bool) (i' : Fin 4)
    (s' : Fin 4 → Bool) : vertP2 i s ≠ vertP3 i' s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP2_testimone i s
  rw [h] at ht
  rcases vertP3_range i' s' i with hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s5.1689a8d593a3 from=translated src=- shape=fadd8250 vocab=ff3299f9
-/
theorem vertP2_ne_vertP4 (i : Fin 4) (s : Fin 4 → Bool) (i' : Fin 4)
    (s' : Fin 4 → Bool) : vertP2 i s ≠ vertP4 i' s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP2_testimone i s
  rw [h] at ht
  rcases vertP4_range i' s' i with hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.9b04eb82610c from=translated src=- shape=2f622fde vocab=288b3f24
-/
theorem vertP2_ne_vertP5 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP2 i s ≠ vertP5 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP2_testimone i s
  rw [h] at ht
  rcases vertP5_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.494ec93af337 from=translated src=- shape=2f622fde vocab=1a905e95
-/
theorem vertP2_ne_vertP6 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP2 i s ≠ vertP6 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  obtain ⟨j, hj⟩ := vertP2_testimone_uno i s
  rw [h] at hj
  rcases vertP6_range σ s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.589c570fa2f9 from=translated src=- shape=2f622fde vocab=a0c8e1bc
-/
theorem vertP2_ne_vertP7 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 4 → Bool) :
    vertP2 i s ≠ vertP7 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP2_testimone i s
  rw [h] at ht
  rcases vertP7_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s5.1ec4743b3c48 from=translated src=- shape=fadd8250 vocab=5eb2148a
-/
theorem vertP3_ne_vertP4 (i : Fin 4) (s : Fin 4 → Bool) (i' : Fin 4)
    (s' : Fin 4 → Bool) : vertP3 i s ≠ vertP4 i' s' := by
  intro h
  have hb := aureo_bounds
  have ht := vertP3_testimone i s
  rw [h] at ht
  rcases vertP4_range i' s' i with hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.1c9b5de78f44 from=translated src=- shape=2f622fde vocab=3b138b2f
-/
theorem vertP3_ne_vertP5 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP3 i s ≠ vertP5 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := vertP3_testimone_aureo i s
  rw [h] at hj
  rcases vertP5_range σ s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.26d3e81618cb from=translated src=- shape=2f622fde vocab=9d11a0ed
-/
theorem vertP3_ne_vertP6 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP3 i s ≠ vertP6 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP3_testimone i s
  rw [h] at ht
  rcases vertP6_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.762d5f9d3b54 from=translated src=- shape=2f622fde vocab=30d5b656
-/
theorem vertP3_ne_vertP7 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 4 → Bool) :
    vertP3 i s ≠ vertP7 σ s' := by
  intro h
  have hb := aureo_bounds
  have ht := vertP3_testimone i s
  rw [h] at ht
  rcases vertP7_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.9eeaf5649519 from=translated src=- shape=2f622fde vocab=e4d05509
-/
theorem vertP4_ne_vertP5 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP4 i s ≠ vertP5 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := vertP4_testimone_inv i s
  rw [h] at hj
  rcases vertP5_range σ s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.53e0a0556955 from=translated src=- shape=2f622fde vocab=4987a80f
-/
theorem vertP4_ne_vertP6 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 3 → Bool) :
    vertP4 i s ≠ vertP6 σ s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  have ht := vertP4_testimone i s
  rw [h] at ht
  rcases vertP6_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.05dfc5de2a69 from=translated src=- shape=2f622fde vocab=acd150d8
-/
theorem vertP4_ne_vertP7 (i : Fin 4) (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (s' : Fin 4 → Bool) :
    vertP4 i s ≠ vertP7 σ s' := by
  intro h
  have hb := aureo_bounds
  have ht := vertP4_testimone i s
  rw [h] at ht
  rcases vertP7_range σ s' i with hr | hr | hr | hr <;>
    rw [ht] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.10173bf64dbf from=translated src=- shape=7c472ecd vocab=87330604
-/
theorem vertP5_ne_vertP6 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (σ' : alternatingGroup (Fin 4))
    (s' : Fin 3 → Bool) : vertP5 σ s ≠ vertP6 σ' s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  obtain ⟨j, hj⟩ := vertP5_testimone_uno σ s
  rw [h] at hj
  rcases vertP6_range σ' s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.41541daed950 from=translated src=- shape=7c472ecd vocab=fe91269e
-/
theorem vertP5_ne_vertP7 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (σ' : alternatingGroup (Fin 4))
    (s' : Fin 4 → Bool) : vertP5 σ s ≠ vertP7 σ' s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨j, hj⟩ := vertP5_testimone_zero σ s
  rw [h] at hj
  rcases vertP7_range σ' s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/--
@isnad1 id=ne.0h4v.s7.1d175e422b8e from=translated src=- shape=7c472ecd vocab=dc32131c
-/
theorem vertP6_ne_vertP7 (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (σ' : alternatingGroup (Fin 4))
    (s' : Fin 4 → Bool) : vertP6 σ s ≠ vertP7 σ' s' := by
  intro h
  have hb := aureo_bounds
  obtain ⟨lo, hi⟩ := sqrt_five_bounds
  obtain ⟨j, hj⟩ := vertP6_testimone σ s
  rw [h] at hj
  rcases vertP7_range σ' s' j with hr | hr | hr | hr <;>
    rw [hj] at hr <;> linarith [hb.1, hb.2]

/-! ## Il Finset dei 600 vertici e il politopo -/

open Classical in
/-- I 600 vertici del 120-cell: l'unione delle sette famiglie.-/
noncomputable def centoventiVertici : Finset (E 4) :=
  ((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
    ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
      (fun p => vertP2 p.1 p.2)) ∪
    ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
      (fun p => vertP3 p.1 p.2)) ∪
    ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
      (fun p => vertP4 p.1 p.2)) ∪
    ((Finset.univ :
        Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
      (fun p => vertP5 p.1 p.2)) ∪
    ((Finset.univ :
        Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
      (fun p => vertP6 p.1 p.2)) ∪
    ((Finset.univ :
        Finset (alternatingGroup (Fin 4) × (Fin 4 → Bool))).image
      (fun p => vertP7 p.1 p.2))

open Classical in
/--
@isnad1 id=eq.1h1v.s6.da1f579606b6 from=translated src=- shape=79ed8e37 vocab=5f04d326
-/
theorem norm_sq_mem_centoventiVertici {v : E 4}
    (hv : v ∈ centoventiVertici) : ‖v‖ ^ 2 = 8 := by
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with ((((((⟨c, hc⟩ | ⟨p, hp⟩) | ⟨p, hp⟩) | ⟨p, hp⟩) |
    ⟨p, hp⟩) | ⟨p, hp⟩) | ⟨p, hp⟩)
  · rw [← hc]; exact norm_sq_vertP1 c
  · rw [← hp]; exact norm_sq_vertP2 p.1 p.2
  · rw [← hp]; exact norm_sq_vertP3 p.1 p.2
  · rw [← hp]; exact norm_sq_vertP4 p.1 p.2
  · rw [← hp]; exact norm_sq_vertP5 p.1 p.2
  · rw [← hp]; exact norm_sq_vertP6 p.1 p.2
  · rw [← hp]; exact norm_sq_vertP7 p.1 p.2

open Classical in
/--
@isnad1 id=nonempty.0h0v.s3.e5af7f458060 from=translated src=- shape=06f63001 vocab=44f8c257
-/
theorem centoventiVertici_nonempty : centoventiVertici.Nonempty := by
  refine ⟨vertP1 (codiceVentiquattro 0 1 (by norm_num) true true), ?_⟩
  simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    ⟨_, rfl⟩)))))

open Classical in
/-- **LA CARDINALITÀ**: `24+64+64+64+96+96+192 = 600`.
@isnad1 id=eq.0h0v.s3.f88e49b8f8f8 from=translated src=- shape=415057c6 vocab=ea065600
-/
theorem card_centoventiVertici : centoventiVertici.card = 600 := by
  rw [centoventiVertici]
  -- disgiunzioni progressive
  have d12 : Disjoint
      ((Finset.univ : Finset CodiceVentiquattro).image vertP1)
      ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
        (fun p => vertP2 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨c, _, rfl⟩ := hx
    obtain ⟨p, _, hp⟩ := hy
    exact vertP1_ne_vertP2 c p.1 p.2 hp.symm
  have d3 : Disjoint
      (((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP2 p.1 p.2)))
      ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
        (fun p => vertP3 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, _, hq⟩ := hy
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx <;> rw [Finset.mem_image] at hx
    · obtain ⟨c, _, rfl⟩ := hx
      exact vertP1_ne_vertP3 c q.1 q.2 hq.symm
    · obtain ⟨p, _, rfl⟩ := hx
      exact vertP2_ne_vertP3 p.1 p.2 q.1 q.2 hq.symm
  have d4 : Disjoint
      ((((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP2 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP3 p.1 p.2)))
      ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
        (fun p => vertP4 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, _, hq⟩ := hy
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_union] at hx
      rcases hx with hx | hx <;> rw [Finset.mem_image] at hx
      · obtain ⟨c, _, rfl⟩ := hx
        exact vertP1_ne_vertP4 c q.1 q.2 hq.symm
      · obtain ⟨p, _, rfl⟩ := hx
        exact vertP2_ne_vertP4 p.1 p.2 q.1 q.2 hq.symm
    · rw [Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact vertP3_ne_vertP4 p.1 p.2 q.1 q.2 hq.symm
  have d5 : Disjoint
      (((((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP2 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP3 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP4 p.1 p.2)))
      ((Finset.univ :
          Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
        (fun p => vertP5 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, _, hq⟩ := hy
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_union] at hx
        rcases hx with hx | hx <;> rw [Finset.mem_image] at hx
        · obtain ⟨c, _, rfl⟩ := hx
          exact vertP1_ne_vertP5 c q.1 q.2 hq.symm
        · obtain ⟨p, _, rfl⟩ := hx
          exact vertP2_ne_vertP5 p.1 p.2 q.1 q.2 hq.symm
      · rw [Finset.mem_image] at hx
        obtain ⟨p, _, rfl⟩ := hx
        exact vertP3_ne_vertP5 p.1 p.2 q.1 q.2 hq.symm
    · rw [Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact vertP4_ne_vertP5 p.1 p.2 q.1 q.2 hq.symm
  have d6 : Disjoint
      ((((((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP2 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP3 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP4 p.1 p.2))) ∪
        ((Finset.univ :
            Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
          (fun p => vertP5 p.1 p.2)))
      ((Finset.univ :
          Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
        (fun p => vertP6 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, _, hq⟩ := hy
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · rw [Finset.mem_union] at hx
          rcases hx with hx | hx <;> rw [Finset.mem_image] at hx
          · obtain ⟨c, _, rfl⟩ := hx
            exact vertP1_ne_vertP6 c q.1 q.2 hq.symm
          · obtain ⟨p, _, rfl⟩ := hx
            exact vertP2_ne_vertP6 p.1 p.2 q.1 q.2 hq.symm
        · rw [Finset.mem_image] at hx
          obtain ⟨p, _, rfl⟩ := hx
          exact vertP3_ne_vertP6 p.1 p.2 q.1 q.2 hq.symm
      · rw [Finset.mem_image] at hx
        obtain ⟨p, _, rfl⟩ := hx
        exact vertP4_ne_vertP6 p.1 p.2 q.1 q.2 hq.symm
    · rw [Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact vertP5_ne_vertP6 p.1 p.2 q.1 q.2 hq.symm
  have d7 : Disjoint
      (((((((Finset.univ : Finset CodiceVentiquattro).image vertP1) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP2 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP3 p.1 p.2))) ∪
        ((Finset.univ : Finset (Fin 4 × (Fin 4 → Bool))).image
          (fun p => vertP4 p.1 p.2))) ∪
        ((Finset.univ :
            Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
          (fun p => vertP5 p.1 p.2))) ∪
        ((Finset.univ :
            Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
          (fun p => vertP6 p.1 p.2)))
      ((Finset.univ :
          Finset (alternatingGroup (Fin 4) × (Fin 4 → Bool))).image
        (fun p => vertP7 p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    rw [Finset.mem_image] at hy
    obtain ⟨q, _, hq⟩ := hy
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · rw [Finset.mem_union] at hx
            rcases hx with hx | hx <;> rw [Finset.mem_image] at hx
            · obtain ⟨c, _, rfl⟩ := hx
              exact vertP1_ne_vertP7 c q.1 q.2 hq.symm
            · obtain ⟨p, _, rfl⟩ := hx
              exact vertP2_ne_vertP7 p.1 p.2 q.1 q.2 hq.symm
          · rw [Finset.mem_image] at hx
            obtain ⟨p, _, rfl⟩ := hx
            exact vertP3_ne_vertP7 p.1 p.2 q.1 q.2 hq.symm
        · rw [Finset.mem_image] at hx
          obtain ⟨p, _, rfl⟩ := hx
          exact vertP4_ne_vertP7 p.1 p.2 q.1 q.2 hq.symm
      · rw [Finset.mem_image] at hx
        obtain ⟨p, _, rfl⟩ := hx
        exact vertP5_ne_vertP7 p.1 p.2 q.1 q.2 hq.symm
    · rw [Finset.mem_image] at hx
      obtain ⟨p, _, rfl⟩ := hx
      exact vertP6_ne_vertP7 p.1 p.2 q.1 q.2 hq.symm
  rw [Finset.card_union_of_disjoint d7,
    Finset.card_union_of_disjoint d6,
    Finset.card_union_of_disjoint d5,
    Finset.card_union_of_disjoint d4,
    Finset.card_union_of_disjoint d3,
    Finset.card_union_of_disjoint d12,
    Finset.card_image_of_injective _ vertP1_injective,
    Finset.card_image_of_injective _ vertP2_injective,
    Finset.card_image_of_injective _ vertP3_injective,
    Finset.card_image_of_injective _ vertP4_injective,
    Finset.card_image_of_injective _ vertP5_injective,
    Finset.card_image_of_injective _ vertP6_injective,
    Finset.card_image_of_injective _ vertP7_injective]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, card_codiceVentiquattro,
    card_coppiaVentiquattro, card_alternatingGroup]
  norm_num [Nat.factorial]

open Classical in
/--
@isnad1 id=eq.0h0v.s8.79d8c5fe61e0 from=translated src=- shape=c466b020 vocab=ede16a48
-/
theorem centoventiVertici_eq_extremePoints :
    ((centoventiVertici : Finset (E 4)) : Set (E 4)) =
      Set.extremePoints ℝ
        (convexHull ℝ
          ((centoventiVertici : Finset (E 4)) : Set (E 4))) := by
  have hv0 := vertP1 (codiceVentiquattro 0 1 (by norm_num) true true)
  have hne : (0 : E 4) ≠
      vertP1 (codiceVentiquattro 0 1 (by norm_num) true true) := by
    intro h
    have hnorm := norm_sq_vertP1 (codiceVentiquattro 0 1
      (by norm_num) true true)
    rw [← h] at hnorm
    simp at hnorm
  haveI : Nontrivial (E 4) :=
    ⟨⟨0, vertP1 (codiceVentiquattro 0 1 (by norm_num) true true), hne⟩⟩
  symm
  apply cosferico_extremePoints 0 (Real.sqrt 8)
  intro v hv
  rw [mem_sphere_zero_iff_norm]
  have hv' : v ∈ centoventiVertici := by exact_mod_cast hv
  have hsq := norm_sq_mem_centoventiVertici hv'
  rw [← Real.sqrt_sq (norm_nonneg v), hsq]

open Classical in
/-- **IL 120-CELL** come politopo convesso di `E 4`.-/
noncomputable def centoventi : ConvexPolytope 4 :=
  ⟨centoventiVertici, centoventiVertici_nonempty,
    centoventiVertici_eq_extremePoints⟩

/-- La cardinalità dei vertici del 120-cell.
@isnad1 id=eq.0h0v.s4.2e0a3b302d05 from=translated src=- shape=1538b06e vocab=d00001c4
-/
theorem card_centoventi_vertices : centoventi.vertices.card = 600 :=
  card_centoventiVertici

open Classical in
/--
@isnad1 id=mem.0h2v.s5.3e23a7cd9775 from=translated src=- shape=90a5d296 vocab=ba2a649e
-/
theorem vertP2_mem_centoventi_toSet (i : Fin 4) (s : Fin 4 → Bool) :
    vertP2 i s ∈ centoventi.toSet := by
  apply subset_convexHull ℝ _
  have hmem : vertP2 i s ∈ centoventiVertici := by
    simp only [centoventiVertici, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
      ⟨(i, s), rfl⟩)))))
  exact_mod_cast hmem

/-- **PIENA DIMENSIONALITÀ**: i flip di segno del blocco P2 danno i
generatori.
@isnad1 id=isfulldi.0h0v.s2.e8272ff95148 from=translated src=- shape=cef8a6bf vocab=3809cce0
-/
theorem centoventi_isFullDim : centoventi.IsFullDim := by
  classical
  let W : Submodule ℝ (E 4) := vectorSpan ℝ centoventi.toSet
  have hbasis : ∀ k : Fin 4,
      (EuclideanSpace.basisFun (Fin 4) ℝ) k ∈ W := by
    intro k
    obtain ⟨i, hik⟩ := exists_ne k
    have hdiff : vertP2 i (fun _ => true) -
        vertP2 i (fun j => if j = k then false else true) ∈ W :=
      vsub_mem_vectorSpan ℝ
        (vertP2_mem_centoventi_toSet i (fun _ => true))
        (vertP2_mem_centoventi_toSet i (fun j => if j = k then false
          else true))
    have hcalc : vertP2 i (fun _ => true) -
        vertP2 i (fun j => if j = k then false else true)
        = (2 : ℝ) • (EuclideanSpace.basisFun (Fin 4) ℝ) k := by
      ext j
      rw [PiLp.sub_apply, PiLp.smul_apply, vertP2_apply, vertP2_apply,
        EuclideanSpace.basisFun_apply, PiLp.single_apply,
        smul_eq_mul]
      by_cases hjk : j = k
      · rw [ite_eq_left hjk]
        have hjik : ¬ j = i := by
          rw [hjk]
          exact fun h => hik h.symm
        rw [ite_eq_right hjik]
        simp [hjk, hjik]
        norm_num
      · rw [ite_eq_right hjk]
        by_cases hji : j = i
        · rw [ite_eq_left hji]
          simp [hjk, hji]
          exact hik
        · rw [ite_eq_right hji]
          simp [hjk, hji]
    rw [hcalc] at hdiff
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp hdiff
  have hW : W = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro x
    rw [← (EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x]
    exact Submodule.sum_mem W fun i _ => W.smul_mem _ (hbasis i)
  rw [ConvexPolytope.IsFullDim, ConvexPolytope.dim]
  change Module.finrank ℝ W = 4
  rw [hW, finrank_top, finrank_euclideanSpace]
  simp

end LeanEval.Geometry.PlatonicClassification
-- Tengoku: root names of this library moved to Tengoku.LeanEvalPlatonicClassification so they do not collide with other libraries (generated)
