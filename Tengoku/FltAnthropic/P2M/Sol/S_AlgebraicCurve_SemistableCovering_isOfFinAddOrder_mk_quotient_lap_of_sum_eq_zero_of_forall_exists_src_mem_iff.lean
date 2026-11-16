import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_SemistableCovering_isOfFinAddOrder_mk_quotient_lap_of_sum_eq_zero_of_forall_exists_src_mem_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_SemistableCovering_isOfFinAddOrder_mk_quotient_lap_of_sum_eq_zero_of_forall_exists_src_mem_iff

set_option autoImplicit false

namespace TropCnt

variable {V Seg : Type} [Fintype V] [DecidableEq V] [Fintype Seg] (ends : Seg → V × V)

def bd : (Seg → ℤ) →+ (V → ℤ) where
  toFun y := ∑ ε, y ε • ((Pi.single (ends ε).1 1 : V → ℤ) - Pi.single (ends ε).2 1)
  map_zero' := by simp
  map_add' y y' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

def cobd : (V → ℤ) →+ (Seg → ℤ) where
  toFun x ε := x (ends ε).1 - x (ends ε).2
  map_zero' := by ext; simp
  map_add' x x' := by ext; simp only [Pi.add_apply]; ring

def lapRow (v : V) : V → ℤ := ∑ ε,
  ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
   (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))

/--
@isnad1 id=eq.0h4v.s7.dd1285eed77c from=translated src=- shape=399c3e1a vocab=7eec416f
-/
theorem lapRow_eq (v : V) : lapRow ends v = bd ends (cobd ends (Pi.single v 1)) := by
  classical
  unfold lapRow bd cobd
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  apply Finset.sum_congr rfl
  intro ε _
  by_cases h1 : (ends ε).1 = v <;> by_cases h2 : (ends ε).2 = v
  · subst h1; simp [h2]
  · subst h1; simp [h2]
  · subst h2; simp [h1]
  · simp [h1, h2]

/--
@isnad1 id=eq.0h3v.s7.6c6b8bc76695 from=translated src=- shape=aa00ede3 vocab=f593f795
-/
theorem closure_range_lapRow :
    AddSubgroup.closure (Set.range (lapRow ends)) = ((bd ends).comp (cobd ends)).range := by
  classical
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    exact AddMonoidHom.mem_range.mpr ⟨Pi.single v 1, (lapRow_eq ends v).symm⟩
  · rintro _ ⟨x, rfl⟩

    have hx : x = ∑ v, x v • (Pi.single v 1 : V → ℤ) := by
      ext u; simp [Finset.sum_apply, Pi.single_apply]
    rw [hx, map_sum]
    refine AddSubgroup.sum_mem _ fun v _ => ?_
    rw [map_zsmul]
    have hv : bd ends (cobd ends (Pi.single v 1)) ∈ AddSubgroup.closure (Set.range (lapRow ends)) :=
      AddSubgroup.subset_closure ⟨v, lapRow_eq ends v⟩
    exact AddSubgroup.zsmul_mem _ hv _

def deg : (V → ℤ) →+ ℤ where
  toFun x := ∑ v, x v
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

section L4

def cobdQ : (V → ℚ) →ₗ[ℚ] (Seg → ℚ) where
  toFun x ε := x (ends ε).1 - x (ends ε).2
  map_add' x y := by ext; simp only [Pi.add_apply]; ring
  map_smul' c x := by ext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def bdQ : (Seg → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun y := ∑ ε, y ε • ((Pi.single (ends ε).1 1 : V → ℚ) - Pi.single (ends ε).2 1)
  map_add' y y' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

def degQ : (V → ℚ) →ₗ[ℚ] ℚ where
  toFun x := ∑ v, x v
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/--
@isnad1 id=eq.0h5v.s7.c63dbf333957 from=translated src=- shape=d2d6c9ea vocab=a9712247
-/
theorem cobdQ_apply (x : V → ℚ) (ε : Seg) : cobdQ ends x ε = x (ends ε).1 - x (ends ε).2 := rfl

/--
@isnad1 id=eq.0h5v.s7.eb3da2cb81aa from=translated src=- shape=9478bcfd vocab=97677e4f
-/
theorem bdQ_apply (y : Seg → ℚ) (v : V) :
    bdQ ends y v = ∑ ε, y ε * ((if v = (ends ε).1 then 1 else 0) - (if v = (ends ε).2 then 1 else 0)) := by
  unfold bdQ
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
    smul_eq_mul]

/--
@isnad1 id=eq.0h2v.s6.3fe84fa10a46 from=translated src=- shape=7571dfb9 vocab=9388d88e
-/
theorem degQ_apply (x : V → ℚ) : degQ (V := V) x = ∑ v, x v := rfl

/--
@isnad1 id=eq.0h5v.s8.8375fb98a783 from=translated src=- shape=9d91a63d vocab=de2d7ba6
-/
theorem sum_mul_bdQ (x : V → ℚ) (y : Seg → ℚ) :
    ∑ v, x v * bdQ ends y v = ∑ ε, cobdQ ends x ε * y ε := by
  simp only [bdQ_apply, cobdQ_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ε _
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/--
@isnad1 id=eq.0h4v.s7.275da4ed8df0 from=translated src=- shape=d4bacdd4 vocab=37bef385
-/
theorem degQ_bdQ (y : Seg → ℚ) : degQ (bdQ ends y) = 0 := by
  have := sum_mul_bdQ ends (fun _ => (1 : ℚ)) y
  simp only [one_mul, cobdQ_apply, sub_self, zero_mul, Finset.sum_const_zero] at this
  rw [degQ_apply]
  exact this

/--
@isnad1 id=eq.0h4v.s7.2fe388f8afd3 from=translated src=- shape=d6fbe0e1 vocab=85979b41
-/
theorem cast_cobd (z : V → ℤ) : (fun ε => ((cobd ends z ε : ℤ) : ℚ)) = cobdQ ends (fun v => (z v : ℚ)) := by
  ext ε
  unfold cobd
  simp only [cobdQ_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_sub]

/--
@isnad1 id=eq.0h4v.s7.216f02db5505 from=translated src=- shape=af13e15b vocab=d124082d
-/
theorem cast_bd (y : Seg → ℤ) : (fun v => ((bd ends y v : ℤ) : ℚ)) = bdQ ends (fun ε => (y ε : ℚ)) := by
  ext v
  unfold bd
  rw [bdQ_apply]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
    smul_eq_mul]
  push_cast
  rfl

/--
@isnad1 id=le.1h4v.s8.06399225aed3 from=translated src=- shape=676b73f1 vocab=a6a03ff7
-/
theorem ker_lapQ_le (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (v₀ : V) : LinearMap.ker ((bdQ ends).comp (cobdQ ends)) ≤ Submodule.span ℚ {fun _ : V => (1 : ℚ)} := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx

  have hsq : ∑ ε, cobdQ ends x ε * cobdQ ends x ε = 0 := by
    rw [← sum_mul_bdQ ends x (cobdQ ends x), hx]
    simp
  have hzero : ∀ ε, cobdQ ends x ε = 0 := by
    intro ε
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun ε _ => mul_self_nonneg (cobdQ ends x ε))).1 hsq ε
      (Finset.mem_univ ε)
    exact mul_self_eq_zero.1 h

  have hconst : ∀ u v, x u = x v := by
    intro u v
    obtain ⟨y, hy⟩ := hconn u v
    have h1 : ∑ w, x w * bdQ ends (fun ε => (y ε : ℚ)) w = 0 := by
      rw [sum_mul_bdQ]; simp [hzero]
    rw [← cast_bd ends y, hy] at h1
    simp only [Pi.sub_apply, Pi.single_apply, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_sub,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
    exact sub_eq_zero.1 h1
  rw [Submodule.mem_span_singleton]
  exact ⟨x v₀, funext fun v => by simp [hconst v v₀]⟩

/--
@isnad1 id=eq.1h4v.s8.c97516fd095a from=translated src=- shape=7d51ebc3 vocab=f278fc94
-/
theorem range_lapQ_eq (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (v₀ : V) : LinearMap.range ((bdQ ends).comp (cobdQ ends)) = LinearMap.ker (degQ (V := V)) := by
  classical
  have hle : LinearMap.range ((bdQ ends).comp (cobdQ ends)) ≤ LinearMap.ker (degQ (V := V)) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact degQ_bdQ ends _
  have hV : Module.finrank ℚ (V → ℚ) = Fintype.card V := Module.finrank_fintype_fun_eq_card ℚ

  have hdeg_surj : LinearMap.range (degQ (V := V)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single v₀ c, ?_⟩
    rw [degQ_apply]
    simp [Pi.single_apply]
  have hker_deg : Module.finrank ℚ (LinearMap.ker (degQ (V := V))) + 1 = Fintype.card V := by
    have := LinearMap.finrank_range_add_finrank_ker (degQ (V := V))
    rw [hdeg_surj, finrank_top, Module.finrank_self, hV] at this
    omega

  have hkerL : Module.finrank ℚ (LinearMap.ker ((bdQ ends).comp (cobdQ ends))) ≤ 1 := by
    calc Module.finrank ℚ (LinearMap.ker ((bdQ ends).comp (cobdQ ends)))
        ≤ Module.finrank ℚ (Submodule.span ℚ {fun _ : V => (1 : ℚ)}) :=
          Submodule.finrank_mono (ker_lapQ_le ends hconn v₀)
      _ = 1 := finrank_span_singleton (by
          intro h
          have := congrFun h v₀
          simp at this)
  have hrange : Module.finrank ℚ (LinearMap.range ((bdQ ends).comp (cobdQ ends))) + 1 ≥ Fintype.card V := by
    have := LinearMap.finrank_range_add_finrank_ker ((bdQ ends).comp (cobdQ ends))
    rw [hV] at this
    omega
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

/--
@isnad1 id=ex.2h4v.s8.bd1a21d337b5 from=translated src=- shape=712e7bb6 vocab=10ea0756
-/
theorem exists_nsmul_mem_range_lap_of_deg_eq_zero
    (hconn : ∀ u v : V, (Pi.single u 1 : V → ℤ) - Pi.single v 1 ∈ (bd ends).range)
    (h : V → ℤ) (hh : deg (V := V) h = 0) :
    ∃ d : ℕ, 0 < d ∧ (d : ℤ) • h ∈ ((bd ends).comp (cobd ends)).range := by
  classical
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · refine ⟨1, one_pos, ⟨0, ?_⟩⟩
    ext v; exact (IsEmpty.false v).elim

  have hmem : (fun v => (h v : ℚ)) ∈ LinearMap.ker (degQ (V := V)) := by
    rw [LinearMap.mem_ker, degQ_apply]
    have : ((∑ v, h v : ℤ) : ℚ) = 0 := by
      have hh' : ∑ v, h v = 0 := hh
      rw [hh']; simp
    push_cast at this
    exact this
  rw [← range_lapQ_eq ends hconn v₀] at hmem
  obtain ⟨q, hq⟩ := hmem
  rw [LinearMap.comp_apply] at hq

  set d : ℕ := ∏ v, (q v).den with hd
  have hdpos : 0 < d := Finset.prod_pos fun v _ => (q v).den_pos
  have hdvd : ∀ v, (q v).den ∣ d := fun v => Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
  set z : V → ℤ := fun v => (q v).num * ((d / (q v).den : ℕ) : ℤ) with hz
  have hzq : (fun v => (z v : ℚ)) = (d : ℚ) • q := by
    ext v
    simp only [hz, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hdvd v) (by exact_mod_cast (q v).den_pos.ne'), ← Rat.mul_den_eq_num (q v)]
    field_simp
  refine ⟨d, hdpos, z, ?_⟩

  have hcast : (fun v => (((bd ends).comp (cobd ends) z) v : ℚ)) = fun v => ((((d : ℕ) : ℤ) • h) v : ℚ) := by
    rw [AddMonoidHom.comp_apply]
    rw [show (fun v => ((bd ends (cobd ends z) v : ℤ) : ℚ)) = bdQ ends (fun ε => (cobd ends z ε : ℚ)) from cast_bd ends _,
      cast_cobd ends z, hzq, LinearMap.map_smul, LinearMap.map_smul, hq]
    ext v
    simp [Pi.smul_apply]
  ext v
  have := congrFun hcast v
  exact_mod_cast this

end L4

end TropCnt

namespace TropCnt

variable {V Seg : Type} [Fintype V] [DecidableEq V] [Fintype Seg] (ends : Seg → V × V)

/--
@isnad1 id=mem.0h4v.s7.857df3a6ebfb from=translated src=- shape=a74e252f vocab=ce8c81dc
-/
theorem single_sub_single_ends_mem (ε : Seg) :
    (Pi.single (ends ε).1 1 : V → ℤ) - Pi.single (ends ε).2 1 ∈ (bd ends).range := by
  classical
  refine ⟨Pi.single ε 1, ?_⟩
  show ∑ ε', (Pi.single ε (1 : ℤ) : Seg → ℤ) ε' • ((Pi.single (ends ε').1 1 : V → ℤ) - Pi.single (ends ε').2 1) = _
  rw [Finset.sum_eq_single_of_mem ε (Finset.mem_univ _)
    (fun ε' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])]
  rw [Pi.single_eq_same, one_smul]

/--
@isnad1 id=mem.3h9v.s9.8c4861f45ec7 from=translated src=- shape=c2e1144e vocab=6676663f
-/
theorem single_sub_single_mem_of_cut {n m : ℕ} (src tgt : Fin m → Fin n) {I : Type} [Fintype I] [DecidableEq I]
    (en : Seg → (Fin n ⊕ I) × (Fin n ⊕ I))
    (hcut : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S))
    (horig : ∀ e, (Pi.single (Sum.inl (src e)) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (tgt e)) 1 ∈ (bd en).range)
    (hint : ∀ i : I, ∃ j : Fin n,
      (Pi.single (Sum.inr i) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j) 1 ∈ (bd en).range) :
    ∀ u v : Fin n ⊕ I, (Pi.single u 1 : Fin n ⊕ I → ℤ) - Pi.single v 1 ∈ (bd en).range := by
  classical
  intro u v
  set B := (bd en).range with hB
  have hrefl : ∀ a : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single a 1 ∈ B := fun a => by
    rw [sub_self]; exact B.zero_mem
  have hsymm : ∀ a b : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single b 1 ∈ B →
      (Pi.single b 1 : Fin n ⊕ I → ℤ) - Pi.single a 1 ∈ B := fun a b h => by
    rw [← neg_sub]; exact B.neg_mem h
  have htrans : ∀ a b c : Fin n ⊕ I, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single b 1 ∈ B →
      (Pi.single b 1 : Fin n ⊕ I → ℤ) - Pi.single c 1 ∈ B → (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single c 1 ∈ B :=
    fun a b c h1 h2 => by
      have := B.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hbase : ∀ a : Fin n ⊕ I, ∃ j : Fin n, (Pi.single a 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j) 1 ∈ B := by
    rintro (j | i)
    · exact ⟨j, hrefl _⟩
    · exact hint i
  have horig' : ∀ j j' : Fin n, (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl j') 1 ∈ B := by
    intro j j'
    by_contra hjj
    let S : Finset (Fin n) :=
      Finset.univ.filter fun i => (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl i) 1 ∈ B
    have hmemS : ∀ i, i ∈ S ↔ (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl i) 1 ∈ B := by
      intro i; simp [S]
    have hjS : j ∈ S := (hmemS j).2 (hrefl _)
    have hj'S : j' ∈ Sᶜ := by rw [Finset.mem_compl, hmemS]; exact hjj
    obtain ⟨e, he⟩ := hcut S ⟨j, hjS⟩ ⟨j', hj'S⟩
    rw [hmemS, hmemS] at he
    have hiff : (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (src e)) 1 ∈ B ↔
        (Pi.single (Sum.inl j) 1 : Fin n ⊕ I → ℤ) - Pi.single (Sum.inl (tgt e)) 1 ∈ B :=
      ⟨fun h => htrans _ _ _ h (horig e), fun h => htrans _ _ _ h (hsymm _ _ (horig e))⟩
    rw [hiff] at he
    exact iff_not_self he
  obtain ⟨j, hj⟩ := hbase u
  obtain ⟨j', hj'⟩ := hbase v
  exact htrans _ _ _ hj (htrans _ _ _ (horig' j j') (hsymm _ _ hj'))

end TropCnt

namespace TropCnt

section Subdiv

abbrev SV (n m : ℕ) (W : Fin m → ℕ) : Type := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))

abbrev SSeg (m : ℕ) (W : Fin m → ℕ) : Type := Σ e : Fin m, Fin (W e)

variable {n m : ℕ} (src tgt : Fin m → Fin n) (W : Fin m → ℕ)

def subdivEnds : SSeg m W → SV n m W × SV n m W := fun ε =>
  (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
   if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
    else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)

/--
@isnad1 id=eq.1h6v.s6.4bd00cc6f0a5 from=translated src=- shape=58755e07 vocab=f3b05c80
-/
theorem subdivEnds_fst_zero (e : Fin m) (h : 0 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨0, h⟩⟩).1 = Sum.inl (src e) := by
  simp [subdivEnds]

/--
@isnad1 id=eq.1h7v.s6.1559fa7e5bb1 from=translated src=- shape=522b1b62 vocab=6e706954
-/
theorem subdivEnds_fst_succ (e : Fin m) (j : ℕ) (h : j + 1 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨j + 1, h⟩⟩).1 =
      (subdivEnds src tgt W ⟨e, ⟨j, (Nat.lt_succ_self j).trans h⟩⟩).2 := by
  have h' : ¬ (j + 1 = W e) := h.ne
  simp [subdivEnds, h']

/--
@isnad1 id=eq.1h6v.s6.328410b2bffe from=translated src=- shape=72edef11 vocab=256858e8
-/
theorem subdivEnds_snd_last (e : Fin m) (h : 0 < W e) :
    (subdivEnds src tgt W ⟨e, ⟨W e - 1, Nat.sub_lt h one_pos⟩⟩).2 = Sum.inl (tgt e) := by
  have h' : W e - 1 + 1 = W e := Nat.sub_add_cancel h
  simp [subdivEnds, h']

/--
@isnad1 id=eq.0h7v.s7.73a312006b43 from=translated src=- shape=49dcdfa0 vocab=dca19048
-/
theorem subdivEnds_snd_int (e : Fin m) (i : Fin (W e - 1)) :
    (subdivEnds src tgt W ⟨e, ⟨i.1, by have := i.2; omega⟩⟩).2 = Sum.inr ⟨e, i⟩ := by
  have h' : ¬ (i.1 + 1 = W e) := by have := i.2; omega
  simp [subdivEnds, h']

/--
@isnad1 id=mem.1h7v.s9.e78e30978d3b from=translated src=- shape=b2b1d384 vocab=2f55c477
-/
theorem single_src_sub_single_snd_mem (e : Fin m) : ∀ (j : ℕ) (h : j < W e),
    (Pi.single (Sum.inl (src e)) 1 : SV n m W → ℤ) - Pi.single ((subdivEnds src tgt W ⟨e, ⟨j, h⟩⟩).2) 1 ∈
      (bd (subdivEnds src tgt W)).range := by
  intro j
  induction j with
  | zero =>
    intro h
    have := single_sub_single_ends_mem (subdivEnds src tgt W) ⟨e, ⟨0, h⟩⟩
    rwa [subdivEnds_fst_zero] at this
  | succ j ih =>
    intro h
    have h1 := ih ((Nat.lt_succ_self j).trans h)
    have h2 := single_sub_single_ends_mem (subdivEnds src tgt W) ⟨e, ⟨j + 1, h⟩⟩
    rw [subdivEnds_fst_succ] at h2
    have := AddSubgroup.add_mem _ h1 h2
    rwa [sub_add_sub_cancel] at this

/--
@isnad1 id=mem.2h7v.s9.db744532b163 from=translated src=- shape=f6804233 vocab=0e5a5bad
-/
theorem subdiv_conn (hW : ∀ e, 0 < W e)
    (hcut : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)) :
    ∀ u v : SV n m W, (Pi.single u 1 : SV n m W → ℤ) - Pi.single v 1 ∈ (bd (subdivEnds src tgt W)).range := by
  apply single_sub_single_mem_of_cut src tgt (subdivEnds src tgt W) hcut
  · intro e
    have := single_src_sub_single_snd_mem src tgt W e (W e - 1) (Nat.sub_lt (hW e) one_pos)
    rwa [subdivEnds_snd_last src tgt W e (hW e)] at this
  · rintro ⟨e, i⟩
    refine ⟨src e, ?_⟩
    have := single_src_sub_single_snd_mem src tgt W e i.1 (by have := i.2; omega)
    rw [subdivEnds_snd_int] at this
    rw [← neg_sub]; exact AddSubgroup.neg_mem _ this

end Subdiv

/--
@isnad1 id=isoffina.3h6v.s10.6f7711020ee6 from=translated src=- shape=3b328f12 vocab=7c7662c2
-/
theorem isOfFinAddOrder_mk_of_sum_eq_zero (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)) :
    ∀ x : SV n m W → ℤ, (∑ v, x v) = 0 →
      IsOfFinAddOrder (QuotientAddGroup.mk x :
        (SV n m W → ℤ) ⧸ AddSubgroup.closure (Set.range (lapRow (subdivEnds src tgt W)))) := by
  classical
  intro x hx
  rw [closure_range_lapRow]
  obtain ⟨d, hd, hmem⟩ :=
    exists_nsmul_mem_range_lap_of_deg_eq_zero (subdivEnds src tgt W) (subdiv_conn src tgt W hW hconn) x hx
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  refine ⟨d, hd, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  simpa [natCast_zsmul] using hmem

end TropCnt

/--
@isnad1 id=other.2h5v.s11.9895d0d14491 from=translated src=- shape=86e72539 vocab=6f2cfe2e
-/
theorem solution
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e)
    (hconn : ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S)) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ x : V → ℤ, (∑ v, x v) = 0 →
      IsOfFinAddOrder (QuotientAddGroup.mk x : (V → ℤ) ⧸ AddSubgroup.closure (Set.range lap)) := by
  intro V ends lap
  exact TropCnt.isOfFinAddOrder_mk_of_sum_eq_zero n m src tgt W hW hconn
