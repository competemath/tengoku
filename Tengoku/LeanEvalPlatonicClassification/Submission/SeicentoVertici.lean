import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.AureoBase
import Tengoku.LeanEvalPlatonicClassification.ChallengeDeps
import Tengoku.LeanEvalPlatonicClassification.Submission.Ortoplesse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
I VERTICI DEL 600-CELL (21 lug 2026) — combinatoria degli indici prima
delle coordinate (direttiva del revisore): tre blocchi parametrizzati

* **A** (8): `±eᵢ`, indice `Fin 4 × Bool`;
* **B** (16): `(±1/2, ±1/2, ±1/2, ±1/2)`, indice `Fin 4 → Bool`;
* **C** (96): le permutazioni PARI di `(φ/2, 1/2, (φ−1)/2, 0)` coi segni
  sulle tre coordinate non nulle, indice
  `alternatingGroup (Fin 4) × (Fin 3 → Bool)`.

Tutti su sfera unitaria (`aureo_norm_sq`).  L'iniettività del blocco C si
recupera dai QUATTRO valori assoluti distinti `0 < (φ−1)/2 < 1/2 < φ/2`:
la permutazione si legge dalle posizioni dei valori, i segni dai valori
non nulli.
-/
namespace Tengoku.LeanEvalPlatonicClassification end Tengoku.LeanEvalPlatonicClassification open Tengoku.LeanEvalPlatonicClassification
open Real

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Blocco A: i vertici `±eᵢ`.-/
noncomputable def vertA (i : Fin 4) (b : Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => if j = i then (if b then 1 else -1) else 0)

/--
@isnad1 id=eq.0h3v.s6.ec159d13deca from=translated src=- shape=80ba5af4 vocab=faf8bc50
-/
@[simp] theorem vertA_apply (i : Fin 4) (b : Bool) (j : Fin 4) :
    vertA i b j = if j = i then (if b then (1 : ℝ) else -1) else 0 := by
  simp [vertA]

/-- Blocco B: i vertici `(±1/2)⁴`.-/
noncomputable def vertB (s : Fin 4 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => if s j then 1 / 2 else -(1 / 2))

/--
@isnad1 id=eq.0h2v.s6.fd1d77557617 from=translated src=- shape=3f4cc58c vocab=79a00a06
-/
@[simp] theorem vertB_apply (s : Fin 4 → Bool) (j : Fin 4) :
    vertB s j = if s j then (1 / 2 : ℝ) else -(1 / 2) := by
  simp [vertB]

/-- I quattro valori del blocco aureo, in posizione canonica.-/
noncomputable def baseC : Fin 4 → ℝ :=
  ![aureo / 2, 1 / 2, (aureo - 1) / 2, 0]

/-- I segni del blocco aureo (la quarta coordinata è nulla).-/
noncomputable def segnoC (s : Fin 3 → Bool) : Fin 4 → ℝ :=
  ![if s 0 then 1 else -1, if s 1 then 1 else -1,
    if s 2 then 1 else -1, 1]

/--
@isnad1 id=eq.0h2v.s4.bc347c031227 from=translated src=- shape=8ac8adb9 vocab=d10e01b7
-/
theorem segnoC_abs (s : Fin 3 → Bool) (k : Fin 4) :
    |segnoC s k| = 1 := by
  fin_cases k <;> simp [segnoC] <;> split_ifs <;> norm_num

/--
@isnad1 id=eq.0h2v.s5.fbd92a94b4b8 from=translated src=- shape=b4164dab vocab=31074a61
-/
theorem segnoC_sq (s : Fin 3 → Bool) (k : Fin 4) :
    segnoC s k ^ 2 = 1 := by
  fin_cases k <;> simp [segnoC] <;> split_ifs <;> norm_num

/--
@isnad1 id=le.0h1v.s4.7e1d67d0c361 from=translated src=- shape=de9abb23 vocab=c5941728
-/
theorem baseC_nonneg (k : Fin 4) : 0 ≤ baseC k := by
  have hv := aureo_valori_ordinati
  fin_cases k
  · show (0 : ℝ) ≤ aureo / 2
    linarith [hv.1, hv.2.1, hv.2.2.1]
  · show (0 : ℝ) ≤ 1 / 2
    norm_num
  · show (0 : ℝ) ≤ (aureo - 1) / 2
    linarith [hv.1]
  · show (0 : ℝ) ≤ 0
    exact le_rfl

/-- I quattro valori assoluti del blocco aureo sono distinti.
@isnad1 id=injectiv.0h0v.s3.47c7be7b61ec from=translated src=- shape=bfe16b09 vocab=8ff90e49
-/
theorem baseC_injective : Function.Injective baseC := by
  have hv := aureo_valori_ordinati
  intro k k' h
  fin_cases k <;> fin_cases k' <;> first
    | rfl
    | (exfalso; simp [baseC] at h; done)
    | (exfalso; simp [baseC] at h; nlinarith [hv.1, hv.2.1, hv.2.2.1])

/-- Blocco C: la permutazione pari `σ` colloca i valori, i segni `s`
orientano le tre coordinate non nulle.-/
noncomputable def vertC (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) : E 4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (fun j => segnoC s ((σ : Equiv.Perm (Fin 4)).symm j) *
      baseC ((σ : Equiv.Perm (Fin 4)).symm j))

/--
@isnad1 id=eq.0h3v.s9.bd33a59508a8 from=translated src=- shape=0de02669 vocab=18d7dd90
-/
@[simp] theorem vertC_apply (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (j : Fin 4) :
    vertC σ s j = segnoC s ((σ : Equiv.Perm (Fin 4)).symm j) *
      baseC ((σ : Equiv.Perm (Fin 4)).symm j) := by
  simp [vertC]

/-- Il valore del blocco C nella posizione `σ k` è `±(valore k)`.
@isnad1 id=eq.0h3v.s8.0dfd86a53147 from=translated src=- shape=34d73f37 vocab=e4e00b95
-/
theorem vertC_at (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool)
    (k : Fin 4) :
    vertC σ s ((σ : Equiv.Perm (Fin 4)) k) = segnoC s k * baseC k := by
  rw [vertC_apply, Equiv.symm_apply_apply]

/-! ## Le norme: tutti sulla sfera unitaria -/

/--
@isnad1 id=eq.0h2v.s6.8f36573c1f3b from=translated src=- shape=082d759b vocab=df841b9d
-/
theorem norm_vertA (i : Fin 4) (b : Bool) : ‖vertA i b‖ = 1 := by
  have hsq : ‖vertA i b‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vertA_apply]
    rw [Finset.sum_eq_single i]
    · cases b <;> norm_num
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hnn : 0 ≤ ‖vertA i b‖ := norm_nonneg _
  nlinarith [hsq]

/--
@isnad1 id=eq.0h1v.s6.1f6ae900840f from=translated src=- shape=3a464964 vocab=4cab28d4
-/
theorem norm_vertB (s : Fin 4 → Bool) : ‖vertB s‖ = 1 := by
  have hsq : ‖vertB s‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vertB_apply]
    have hterm : ∀ j : Fin 4,
        ‖if s j then (1 / 2 : ℝ) else -(1 / 2)‖ ^ 2 = 1 / 4 := by
      intro j
      cases hs : s j <;> simp <;> norm_num
    simp_rw [hterm]
    norm_num
  have hnn : 0 ≤ ‖vertB s‖ := norm_nonneg _
  nlinarith [hsq]

/--
@isnad1 id=eq.0h2v.s7.4829a9fac871 from=translated src=- shape=52dfff24 vocab=6f902a41
-/
theorem norm_vertC (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) :
    ‖vertC σ s‖ = 1 := by
  have hsq : ‖vertC σ s‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vertC_apply]
    have hre : ∑ j : Fin 4,
        ‖segnoC s ((σ : Equiv.Perm (Fin 4)).symm j) *
          baseC ((σ : Equiv.Perm (Fin 4)).symm j)‖ ^ 2
        = ∑ k : Fin 4, ‖segnoC s k * baseC k‖ ^ 2 :=
      Fintype.sum_equiv (σ : Equiv.Perm (Fin 4)).symm _ _ (fun j => rfl)
    rw [hre]
    have hterm : ∀ k : Fin 4,
        ‖segnoC s k * baseC k‖ ^ 2 = baseC k ^ 2 := by
      intro k
      rw [norm_mul, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs, segnoC_sq, one_mul]
    simp_rw [hterm]
    rw [Fin.sum_univ_four]
    have h0 : baseC 0 = aureo / 2 := rfl
    have h1 : baseC 1 = 1 / 2 := rfl
    have h2 : baseC 2 = (aureo - 1) / 2 := rfl
    have h3 : baseC 3 = 0 := rfl
    rw [h0, h1, h2, h3]
    nlinarith [aureo_norm_sq]
  have hnn : 0 ≤ ‖vertC σ s‖ := norm_nonneg _
  nlinarith [hsq]

/-! ## Iniettività dei tre blocchi -/

/--
@isnad1 id=lt.0h1v.s4.13adc365468f from=translated src=- shape=9a4b31c0 vocab=cabe6a00
-/
theorem baseC_lt_one (k : Fin 4) : baseC k < 1 := by
  have hv := aureo_valori_ordinati
  fin_cases k
  · show aureo / 2 < 1
    linarith [hv.2.2.2]
  · show (1 / 2 : ℝ) < 1
    norm_num
  · show (aureo - 1) / 2 < 1
    linarith [hv.2.1, hv.2.2.1, hv.2.2.2]
  · show (0 : ℝ) < 1
    norm_num

/--
@isnad1 id=lt.0h1v.s4.ee5328ff9a49 from=translated src=- shape=0252f147 vocab=24053cd5
-/
theorem baseC_pos_tre (m : Fin 3) : 0 < baseC ⟨(m : ℕ), by omega⟩ := by
  have hv := aureo_valori_ordinati
  fin_cases m
  · show (0 : ℝ) < aureo / 2
    linarith [hv.1, hv.2.1, hv.2.2.1]
  · show (0 : ℝ) < 1 / 2
    norm_num
  · show (0 : ℝ) < (aureo - 1) / 2
    linarith [hv.1]

/--
@isnad1 id=injectiv.0h0v.s5.4abda040f252 from=translated src=- shape=b4e34b09 vocab=de8c6e67
-/
theorem vertA_injective :
    Function.Injective (fun p : Fin 4 × Bool => vertA p.1 p.2) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  simp only at h
  have hii : i = i' := by
    by_contra hne
    have h1 := congrArg (fun v : E 4 => v i) h
    simp only [vertA_apply, ite_eq_left rfl, ite_eq_right hne] at h1
    cases b <;> norm_num at h1
  subst hii
  have h2 := congrArg (fun v : E 4 => v i) h
  simp only [vertA_apply, ite_eq_left rfl] at h2
  cases b <;> cases b' <;> first
    | rfl
    | (exfalso; norm_num at h2)

/--
@isnad1 id=injectiv.0h0v.s4.7fba5a2a03b7 from=translated src=- shape=6e6692b1 vocab=cdc08741
-/
theorem vertB_injective : Function.Injective vertB := by
  intro s s' h
  funext j
  have h1 := congrArg (fun v : E 4 => v j) h
  simp only [vertB_apply] at h1
  cases hs : s j <;> cases hs' : s' j <;>
    rw [hs, hs'] at h1 <;> first
      | rfl
      | (exfalso; norm_num at h1)

/-- L'iniettività del blocco aureo: la permutazione si legge dai valori
assoluti, i segni dai valori non nulli.
@isnad1 id=injectiv.0h0v.s8.688434ea6723 from=translated src=- shape=3e84d5f1 vocab=d8cab68f
-/
theorem vertC_injective :
    Function.Injective (fun p :
      alternatingGroup (Fin 4) × (Fin 3 → Bool) => vertC p.1 p.2) := by
  rintro ⟨σ, s⟩ ⟨σ', s'⟩ h
  simp only at h
  -- la permutazione coincide
  have hσσ : ∀ k : Fin 4, (σ : Equiv.Perm (Fin 4)) k =
      (σ' : Equiv.Perm (Fin 4)) k := by
    intro k
    have h1 := congrArg (fun v : E 4 => v ((σ : Equiv.Perm (Fin 4)) k)) h
    simp only [vertC_at, vertC_apply] at h1
    -- |base k| = |base (σ'⁻¹ (σ k))|
    have habs := congrArg abs h1
    rw [abs_mul, abs_mul, segnoC_abs, segnoC_abs, one_mul, one_mul,
      abs_of_nonneg (baseC_nonneg _), abs_of_nonneg (baseC_nonneg _)]
      at habs
    have hk := baseC_injective habs
    rw [Equiv.symm_apply_apply] at hk
    have h2 := congrArg (σ' : Equiv.Perm (Fin 4)) hk
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm
  have hσ : σ = σ' := by
    apply Subtype.ext
    exact Equiv.ext hσσ
  subst hσ
  -- i segni coincidono
  have hs : s = s' := by
    funext m
    have hk := congrArg (fun v : E 4 =>
      v ((σ : Equiv.Perm (Fin 4)) ⟨(m : ℕ), by omega⟩)) h
    simp only [vertC_at] at hk
    have hbne : baseC ⟨(m : ℕ), by omega⟩ ≠ 0 :=
      ne_of_gt (baseC_pos_tre m)
    have hsg : segnoC s ⟨(m : ℕ), by omega⟩ =
        segnoC s' ⟨(m : ℕ), by omega⟩ :=
      mul_right_cancel₀ hbne hk
    fin_cases m
    · show s 0 = s' 0
      have h0 : (if s 0 then (1 : ℝ) else -1)
          = (if s' 0 then 1 else -1) := hsg
      cases hs1 : s 0 <;> cases hs2 : s' 0 <;>
        first
          | rfl
          | (exfalso; rw [hs1, hs2] at h0; norm_num at h0)
    · show s 1 = s' 1
      have h0 : (if s 1 then (1 : ℝ) else -1)
          = (if s' 1 then 1 else -1) := hsg
      cases hs1 : s 1 <;> cases hs2 : s' 1 <;>
        first
          | rfl
          | (exfalso; rw [hs1, hs2] at h0; norm_num at h0)
    · show s 2 = s' 2
      have h0 : (if s 2 then (1 : ℝ) else -1)
          = (if s' 2 then 1 else -1) := hsg
      cases hs1 : s 2 <;> cases hs2 : s' 2 <;>
        first
          | rfl
          | (exfalso; rw [hs1, hs2] at h0; norm_num at h0)
  rw [hs]

/-! ## Le disgiunzioni fra i blocchi -/

/--
@isnad1 id=ne.0h3v.s4.439d8790f0cf from=translated src=- shape=68af074f vocab=b969a4f7
-/
theorem vertA_ne_vertB (i : Fin 4) (b : Bool) (s : Fin 4 → Bool) :
    vertA i b ≠ vertB s := by
  intro h
  obtain ⟨j, hj⟩ := exists_ne i
  have h1 := congrArg (fun v : E 4 => v j) h
  simp only [vertA_apply, vertB_apply, ite_eq_right hj] at h1
  cases hs : s j <;> rw [hs] at h1 <;> norm_num at h1

/--
@isnad1 id=ne.0h4v.s7.ae43f5c6594b from=translated src=- shape=c951dcb8 vocab=15f72d99
-/
theorem vertA_ne_vertC (i : Fin 4) (b : Bool)
    (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) :
    vertA i b ≠ vertC σ s := by
  intro h
  have h1 := congrArg (fun v : E 4 => v i) h
  simp only [vertA_apply, vertC_apply, ite_eq_left rfl] at h1
  have habs := congrArg abs h1
  rw [abs_mul, segnoC_abs, one_mul,
    abs_of_nonneg (baseC_nonneg _)] at habs
  have hlt := baseC_lt_one ((σ : Equiv.Perm (Fin 4)).symm i)
  cases b <;> norm_num at habs <;> linarith [hlt]

/--
@isnad1 id=ne.0h3v.s7.265f2a2f0a10 from=translated src=- shape=5c265ee7 vocab=7b7fcbc2
-/
theorem vertB_ne_vertC (s : Fin 4 → Bool)
    (σ : alternatingGroup (Fin 4)) (t : Fin 3 → Bool) :
    vertB s ≠ vertC σ t := by
  intro h
  have h1 := congrArg (fun v : E 4 =>
    v ((σ : Equiv.Perm (Fin 4)) 3)) h
  rw [vertC_at] at h1
  have hb3 : baseC 3 = 0 := rfl
  rw [hb3, mul_zero] at h1
  simp only [vertB_apply] at h1
  cases hs : s ((σ : Equiv.Perm (Fin 4)) 3) <;> rw [hs] at h1 <;>
    norm_num at h1

/-! ## Il Finset dei 120 vertici e il politopo -/

open Classical in
/-- I 120 vertici del 600-cell: l'unione dei tre blocchi.-/
noncomputable def seicentoVertici : Finset (E 4) :=
  ((Finset.univ : Finset (Fin 4 × Bool)).image
      (fun p => vertA p.1 p.2)) ∪
    ((Finset.univ : Finset (Fin 4 → Bool)).image vertB) ∪
    ((Finset.univ :
        Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
      (fun p => vertC p.1 p.2))

open Classical in
/--
@isnad1 id=eq.1h1v.s6.ebee9b28e8fe from=translated src=- shape=306de394 vocab=c4e72a1d
-/
theorem norm_mem_seicentoVertici {v : E 4}
    (hv : v ∈ seicentoVertici) : ‖v‖ = 1 := by
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with (⟨p, hp⟩ | ⟨s, hs⟩) | ⟨p, hp⟩
  · rw [← hp]
    exact norm_vertA p.1 p.2
  · rw [← hs]
    exact norm_vertB s
  · rw [← hp]
    exact norm_vertC p.1 p.2

open Classical in
/--
@isnad1 id=nonempty.0h0v.s3.a016118feffb from=translated src=- shape=06f63001 vocab=29929cd4
-/
theorem seicentoVertici_nonempty : seicentoVertici.Nonempty := by
  refine ⟨vertB (fun _ => true), ?_⟩
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨fun _ => true, rfl⟩)

open Classical in
/-- **LA CARDINALITÀ**: `8 + 16 + 96 = 120`.
@isnad1 id=eq.0h0v.s3.d714f0bd31a3 from=translated src=- shape=415057c6 vocab=be0fb6f7
-/
theorem card_seicentoVertici : seicentoVertici.card = 120 := by
  rw [seicentoVertici]
  have hdisjAB : Disjoint
      ((Finset.univ : Finset (Fin 4 × Bool)).image
        (fun p => vertA p.1 p.2))
      ((Finset.univ : Finset (Fin 4 → Bool)).image vertB) := by
    rw [Finset.disjoint_left]
    rintro x hxA hxB
    rw [Finset.mem_image] at hxA hxB
    obtain ⟨p, _, rfl⟩ := hxA
    obtain ⟨s, _, hs⟩ := hxB
    exact vertA_ne_vertB p.1 p.2 s hs.symm
  have hdisjABC : Disjoint
      (((Finset.univ : Finset (Fin 4 × Bool)).image
          (fun p => vertA p.1 p.2)) ∪
        ((Finset.univ : Finset (Fin 4 → Bool)).image vertB))
      ((Finset.univ :
          Finset (alternatingGroup (Fin 4) × (Fin 3 → Bool))).image
        (fun p => vertC p.1 p.2)) := by
    rw [Finset.disjoint_left]
    rintro x hxAB hxC
    rw [Finset.mem_image] at hxC
    obtain ⟨q, _, hq⟩ := hxC
    rw [Finset.mem_union] at hxAB
    rcases hxAB with hxA | hxB
    · rw [Finset.mem_image] at hxA
      obtain ⟨p, _, rfl⟩ := hxA
      exact vertA_ne_vertC p.1 p.2 q.1 q.2 hq.symm
    · rw [Finset.mem_image] at hxB
      obtain ⟨s, _, rfl⟩ := hxB
      exact vertB_ne_vertC s q.1 q.2 hq.symm
  rw [Finset.card_union_of_disjoint hdisjABC,
    Finset.card_union_of_disjoint hdisjAB,
    Finset.card_image_of_injective _ vertA_injective,
    Finset.card_image_of_injective _ vertB_injective,
    Finset.card_image_of_injective _ vertC_injective]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool, card_alternatingGroup]
  norm_num [Nat.factorial]

open Classical in
/--
@isnad1 id=eq.0h0v.s8.13bc4714e28e from=translated src=- shape=c466b020 vocab=f3b79eaa
-/
theorem seicentoVertici_eq_extremePoints :
    ((seicentoVertici : Finset (E 4)) : Set (E 4)) =
      Set.extremePoints ℝ
        (convexHull ℝ ((seicentoVertici : Finset (E 4)) : Set (E 4))) := by
  have hne : (0 : E 4) ≠ vertB (fun _ => true) := by
    intro h
    have h0 := congrArg (fun x : E 4 => x (0 : Fin 4)) h
    simp only [vertB_apply] at h0
    norm_num at h0
  haveI : Nontrivial (E 4) := ⟨⟨0, vertB (fun _ => true), hne⟩⟩
  symm
  apply cosferico_extremePoints 0 1
  intro v hv
  rw [mem_sphere_zero_iff_norm]
  have hv' : v ∈ seicentoVertici := by exact_mod_cast hv
  exact norm_mem_seicentoVertici hv'

open Classical in
/-- **IL 600-CELL** come politopo convesso di `E 4`.-/
noncomputable def seicento : ConvexPolytope 4 :=
  ⟨seicentoVertici, seicentoVertici_nonempty,
    seicentoVertici_eq_extremePoints⟩

/-- La cardinalità dei vertici del 600-cell.
@isnad1 id=eq.0h0v.s4.2cd93e35dd47 from=translated src=- shape=1538b06e vocab=3b428414
-/
theorem card_seicento_vertices : seicento.vertices.card = 120 :=
  card_seicentoVertici

open Classical in
/--
@isnad1 id=mem.0h2v.s5.f0db9baf3014 from=translated src=- shape=220a9e72 vocab=c049d8ba
-/
theorem vertA_mem_seicento_toSet (i : Fin 4) (b : Bool) :
    vertA i b ∈ seicento.toSet := by
  apply subset_convexHull ℝ _
  have hmem : vertA i b ∈ seicentoVertici := by
    simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact Or.inl (Or.inl ⟨(i, b), rfl⟩)
  exact_mod_cast hmem

/-- **PIENA DIMENSIONALITÀ**: le differenze `±eᵢ` del blocco A generano
tutto `E 4`.
@isnad1 id=isfulldi.0h0v.s2.578ab9bd9e3e from=translated src=- shape=cef8a6bf vocab=cca79e8b
-/
theorem seicento_isFullDim : seicento.IsFullDim := by
  let W : Submodule ℝ (E 4) := vectorSpan ℝ seicento.toSet
  have hbasis : ∀ i : Fin 4,
      (EuclideanSpace.basisFun (Fin 4) ℝ) i ∈ W := by
    intro i
    have hdiff : vertA i true - vertA i false ∈ W :=
      vsub_mem_vectorSpan ℝ (vertA_mem_seicento_toSet i true)
        (vertA_mem_seicento_toSet i false)
    have hcalc : vertA i true - vertA i false
        = (2 : ℝ) • (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
      ext j
      rw [PiLp.sub_apply, PiLp.smul_apply, vertA_apply, vertA_apply,
        EuclideanSpace.basisFun_apply, PiLp.single_apply,
        smul_eq_mul]
      by_cases hji : j = i
      · rw [ite_eq_left hji, ite_eq_left hji, ite_eq_left hji]
        show (1 : ℝ) - (-1) = 2 * 1
        norm_num
      · rw [ite_eq_right hji, ite_eq_right hji, ite_eq_right hji]
        show (0 : ℝ) - 0 = 2 * 0
        norm_num
    rw [EuclideanSpace.basisFun_apply] at *
    exact (W.smul_mem_iff (by norm_num : (2 : ℝ) ≠ 0)).mp (hcalc ▸ hdiff)
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
