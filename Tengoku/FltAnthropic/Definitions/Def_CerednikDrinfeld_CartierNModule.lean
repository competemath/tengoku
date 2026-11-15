import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

namespace CartierN

variable {M : Type u} [AddCommGroup M]

def beta (V Pi : M →+ M) : M →+ M × M :=
  V.prod (-Pi)

/--
@isnad1 id=eq.0h4v.s8.298ee9d18026 from=translated src=- shape=cf5976fc vocab=358b9c55
-/
@[simp] theorem beta_apply (V Pi : M →+ M) (m : M) : beta V Pi m = (V m, -Pi m) := rfl

abbrev NMod (V Pi : M →+ M) : Type u :=
  (M × M) ⧸ (beta V Pi).range

def mk (V Pi : M →+ M) : M × M →+ NMod V Pi :=
  QuotientAddGroup.mk' (beta V Pi).range

abbrev cls (V Pi : M →+ M) (m m' : M) : NMod V Pi := mk V Pi (m, m')

/--
@isnad1 id=eq.0h4v.s8.c35df4bc15a2 from=translated src=- shape=aeb30b30 vocab=45ff884b
-/
theorem mk_apply (V Pi : M →+ M) (x : M × M) : mk V Pi x = (x : NMod V Pi) := rfl

/--
@isnad1 id=surjecti.0h3v.s8.0a0e520f9119 from=translated src=- shape=612c4b8c vocab=2cf2ba5a
-/
theorem mk_surjective (V Pi : M →+ M) : Function.Surjective (mk V Pi) :=
  QuotientAddGroup.mk'_surjective _

/--
@isnad1 id=ex.0h4v.s6.e2b9a0525514 from=translated src=- shape=04a3e67e vocab=49534018
-/
theorem cls_surjective (V Pi : M →+ M) (z : NMod V Pi) : ∃ m m' : M, cls V Pi m m' = z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := mk_surjective V Pi z
  exact ⟨m, m', rfl⟩

/--
@isnad1 id=iff.0h4v.s8.63f6e3bee68f from=translated src=- shape=4748ed9e vocab=0b058755
-/
theorem mk_eq_zero_iff (V Pi : M →+ M) (x : M × M) :
    mk V Pi x = 0 ↔ ∃ m : M, (V m, -Pi m) = x := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  rfl

/--
@isnad1 id=iff.0h5v.s9.055809d63539 from=translated src=- shape=c548f31d vocab=fe1ed7b3
-/
theorem mk_eq_mk_iff (V Pi : M →+ M) (x y : M × M) :
    mk V Pi x = mk V Pi y ↔ ∃ m : M, y = x + (V m, -Pi m) := by
  rw [mk, QuotientAddGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, ⟨m, rfl⟩, h⟩
    exact ⟨m, h.symm⟩
  · rintro ⟨m, h⟩
    exact ⟨_, ⟨m, rfl⟩, h.symm⟩

/--
@isnad1 id=eq.0h4v.s8.fe2359bfbe1f from=translated src=- shape=0a12b121 vocab=8620ebb3
-/
@[simp] theorem cls_beta (V Pi : M →+ M) (m : M) : cls V Pi (V m) (-Pi m) = 0 :=
  (mk_eq_zero_iff V Pi _).2 ⟨m, rfl⟩

/--
@isnad1 id=eq.0h4v.s7.3e38878b4930 from=translated src=- shape=6c7b318b vocab=19332261
-/
theorem cls_V_zero (V Pi : M →+ M) (m : M) : cls V Pi (V m) 0 = cls V Pi 0 (Pi m) := by
  have h : ((V m, 0) : M × M) = (0, Pi m) + (V m, -Pi m) := by ext <;> simp
  have h2 : cls V Pi (V m) 0 = cls V Pi 0 (Pi m) + cls V Pi (V m) (-Pi m) := by
    rw [cls, cls, cls, ← map_add, ← h]
  rw [h2, cls_beta, add_zero]

/--
@isnad1 id=eq.0h7v.s7.36fde6b67a48 from=translated src=- shape=c54a5c2f vocab=d65501b8
-/
theorem cls_add_cls (V Pi : M →+ M) (m m' n n' : M) :
    cls V Pi m m' + cls V Pi n n' = cls V Pi (m + n) (m' + n') := by
  rw [cls, cls, cls, ← map_add]; rfl

def inl (V Pi : M →+ M) : M →+ NMod V Pi := (mk V Pi).comp (AddMonoidHom.inl M M)

def iota (V Pi : M →+ M) : M →+ NMod V Pi := (mk V Pi).comp (AddMonoidHom.inr M M)

/--
@isnad1 id=eq.0h4v.s8.84991cb8d3cd from=translated src=- shape=9657e079 vocab=03113189
-/
@[simp] theorem inl_apply (V Pi : M →+ M) (m : M) : inl V Pi m = cls V Pi m 0 := rfl
/--
@isnad1 id=eq.0h4v.s8.0a2a7d6a2369 from=translated src=- shape=37813961 vocab=96ca5fa4
-/
@[simp] theorem iota_apply (V Pi : M →+ M) (m : M) : iota V Pi m = cls V Pi 0 m := rfl

/--
@isnad1 id=eq.0h5v.s8.676d9d6fa40e from=translated src=- shape=d5dc9f5c vocab=c30cf0d6
-/
theorem cls_eq_inl_add_iota (V Pi : M →+ M) (m m' : M) :
    cls V Pi m m' = inl V Pi m + iota V Pi m' := by
  rw [inl_apply, iota_apply, cls_add_cls, add_zero, zero_add]

/--
@isnad1 id=eq.0h3v.s8.79f83f97964a from=translated src=- shape=0c7bf0b6 vocab=972028f0
-/
theorem inl_comp_V (V Pi : M →+ M) : (inl V Pi).comp V = (iota V Pi).comp Pi := by
  ext m
  exact cls_V_zero V Pi m

/--
@isnad1 id=le.1h3v.s8.58d71c6660d4 from=translated src=- shape=f9ac6078 vocab=a44cc015
-/
theorem beta_range_le_ker_coprod (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (beta V Pi).range ≤ (Pi.coprod V).ker := by
  rintro _ ⟨m, rfl⟩
  have hm : Pi (V m) = V (Pi m) := DFunLike.congr_fun h m
  rw [AddMonoidHom.mem_ker, beta_apply, AddMonoidHom.coprod_apply, map_neg, hm, add_neg_cancel]

def lambda (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) : NMod V Pi →+ M :=
  QuotientAddGroup.lift (beta V Pi).range (Pi.coprod V) (beta_range_le_ker_coprod V Pi h)

/--
@isnad1 id=eq.1h5v.s8.a93c2144ac0b from=translated src=- shape=2324d062 vocab=b7f0c56c
-/
@[simp] theorem lambda_cls (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) (m m' : M) :
    lambda V Pi h (cls V Pi m m') = Pi m + V m' := rfl

/--
@isnad1 id=eq.1h4v.s9.da301fbe0258 from=translated src=- shape=678eabb7 vocab=984f3fc5
-/
theorem lambda_mk (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) (x : M × M) :
    lambda V Pi h (mk V Pi x) = Pi x.1 + V x.2 := rfl

/--
@isnad1 id=eq.1h3v.s8.636d6a2fe2da from=translated src=- shape=8700a625 vocab=ea3c4560
-/
theorem lambda_comp_iota (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (lambda V Pi h).comp (iota V Pi) = V := by
  ext m
  show Pi 0 + V m = V m
  rw [map_zero, zero_add]

/--
@isnad1 id=eq.1h3v.s8.448f0ebce52b from=translated src=- shape=47974855 vocab=86bb2b34
-/
theorem lambda_comp_inl (V Pi : M →+ M) (h : Pi.comp V = V.comp Pi) :
    (lambda V Pi h).comp (inl V Pi) = Pi := by
  ext m
  show Pi m + V 0 = Pi m
  rw [map_zero, add_zero]

/--
@isnad1 id=le.0h3v.s8.5f1d612786c9 from=translated src=- shape=6d9027d4 vocab=348d2dda
-/
theorem beta_range_le_ker_toLie (V Pi : M →+ M) :
    (beta V Pi).range ≤ ((QuotientAddGroup.mk' V.range).comp (AddMonoidHom.fst M M)).ker := by
  rintro _ ⟨m, rfl⟩
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, beta_apply, AddMonoidHom.coe_fst,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨m, rfl⟩

def toLie (V Pi : M →+ M) : NMod V Pi →+ M ⧸ V.range :=
  QuotientAddGroup.lift (beta V Pi).range ((QuotientAddGroup.mk' V.range).comp (AddMonoidHom.fst M M))
    (beta_range_le_ker_toLie V Pi)

/--
@isnad1 id=eq.0h5v.s9.eb2f6251c766 from=translated src=- shape=791fa96f vocab=53fe8a00
-/
@[simp] theorem toLie_cls (V Pi : M →+ M) (m m' : M) :
    toLie V Pi (cls V Pi m m') = (m : M ⧸ V.range) := rfl

/--
@isnad1 id=surjecti.0h3v.s9.a02f507f7683 from=translated src=- shape=3ef58d82 vocab=46048a2e
-/
theorem toLie_surjective (V Pi : M →+ M) : Function.Surjective (toLie V Pi) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientAddGroup.mk_surjective q
  exact ⟨cls V Pi m 0, rfl⟩

/--
@isnad1 id=eq.0h3v.s9.685f415a7220 from=translated src=- shape=9a0bbfd5 vocab=509f5972
-/
theorem toLie_comp_iota (V Pi : M →+ M) : (toLie V Pi).comp (iota V Pi) = 0 := by
  ext m
  rfl

section map

variable {M' : Type v} [AddCommGroup M']

/--
@isnad1 id=le.2h9v.s9.a98350bdd354 from=translated src=- shape=381202e8 vocab=616a580d
-/
theorem beta_range_le_ker_map₂ (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) :
    (beta V Pi).range ≤ ((mk V' Pi').comp (T₁.prodMap T₂)).ker := by
  rintro _ ⟨m, rfl⟩
  have h₁ : T₁ (V m) = V' (S m) := DFunLike.congr_fun hV m
  have h₂ : T₂ (Pi m) = Pi' (S m) := DFunLike.congr_fun hPi m
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, beta_apply]
  show cls V' Pi' (T₁ (V m)) (T₂ (-Pi m)) = 0
  rw [map_neg, h₁, h₂]
  exact cls_beta V' Pi' (S m)

def map₂ (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) : NMod V Pi →+ NMod V' Pi' :=
  QuotientAddGroup.lift (beta V Pi).range ((mk V' Pi').comp (T₁.prodMap T₂))
    (beta_range_le_ker_map₂ V Pi V' Pi' T₁ T₂ S hV hPi)

/--
@isnad1 id=eq.2h11v.s9.98bc863994db from=translated src=- shape=e01c1181 vocab=311985ad
-/
@[simp] theorem map₂_cls (V Pi : M →+ M) (V' Pi' : M' →+ M') (T₁ T₂ S : M →+ M')
    (hV : T₁.comp V = V'.comp S) (hPi : T₂.comp Pi = Pi'.comp S) (m m' : M) :
    map₂ V Pi V' Pi' T₁ T₂ S hV hPi (cls V Pi m m') = cls V' Pi' (T₁ m) (T₂ m') := rfl

def map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) : NMod V Pi →+ NMod V' Pi' :=
  map₂ V Pi V' Pi' T T T hV hPi

/--
@isnad1 id=eq.2h9v.s9.e0fc72fa148c from=translated src=- shape=fab3cc63 vocab=caa67ac3
-/
@[simp] theorem map_cls (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) (m m' : M) :
    map V Pi V' Pi' T hV hPi (cls V Pi m m') = cls V' Pi' (T m) (T m') := rfl

/--
@isnad1 id=eq.4h7v.s9.1e9c481526e0 from=translated src=- shape=dffd4cce vocab=e39bdb98
-/
theorem lambda_comp_map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T)
    (h : Pi.comp V = V.comp Pi) (h' : Pi'.comp V' = V'.comp Pi') :
    (lambda V' Pi' h').comp (map V Pi V' Pi' T hV hPi) = T.comp (lambda V Pi h) := by
  ext ⟨m, m'⟩
  show Pi' (T m) + V' (T m') = T (Pi m + V m')
  rw [map_add, ← AddMonoidHom.comp_apply, ← hPi, ← AddMonoidHom.comp_apply V', ← hV]
  rfl

/--
@isnad1 id=eq.2h7v.s10.860cbcc2df2d from=translated src=- shape=9e0d209c vocab=8bb708cc
-/
theorem toLie_comp_map (V Pi : M →+ M) (V' Pi' : M' →+ M') (T : M →+ M')
    (hV : T.comp V = V'.comp T) (hPi : T.comp Pi = Pi'.comp T) :
    (toLie V' Pi').comp (map V Pi V' Pi' T hV hPi) =
      (QuotientAddGroup.map V.range V'.range T (by
        rintro _ ⟨m, rfl⟩
        exact ⟨T m, (DFunLike.congr_fun hV m).symm⟩)).comp (toLie V Pi) := by
  ext ⟨m, m'⟩
  rfl

end map

def piece (V Pi : M →+ M) (A A' : AddSubgroup M) : AddSubgroup (NMod V Pi) :=
  (A.prod A').map (mk V Pi)

/--
@isnad1 id=mem.2h7v.s8.6cc126f9cb1d from=translated src=- shape=f6dbe954 vocab=576710b3
-/
theorem cls_mem_piece (V Pi : M →+ M) {A A' : AddSubgroup M} {m m' : M} (hm : m ∈ A)
    (hm' : m' ∈ A') : cls V Pi m m' ∈ piece V Pi A A' :=
  ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

/--
@isnad1 id=iff.0h6v.s8.0213d6b105b8 from=translated src=- shape=e232fc3c vocab=576710b3
-/
theorem mem_piece_iff (V Pi : M →+ M) (A A' : AddSubgroup M) (z : NMod V Pi) :
    z ∈ piece V Pi A A' ↔ ∃ m ∈ A, ∃ m' ∈ A', cls V Pi m m' = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, ⟨hm, hm'⟩, rfl⟩
    exact ⟨m, hm, m', hm', rfl⟩
  · rintro ⟨m, hm, m', hm', rfl⟩
    exact cls_mem_piece V Pi hm hm'

/--
@isnad1 id=le.1h4v.s9.ad4d409b6fbd from=translated src=- shape=4836f742 vocab=5072c94d
-/
theorem beta_range_le_ker_phi (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) :
    (beta V Pi).range ≤ (L.coprod (inl V Pi)).ker := by
  rintro _ ⟨m, rfl⟩
  have hm : L (V m) = inl V Pi (Pi m) := DFunLike.congr_fun hL m
  rw [AddMonoidHom.mem_ker, beta_apply, AddMonoidHom.coprod_apply, hm, map_neg, add_neg_cancel]

def phi (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    NMod V Pi →+ NMod V Pi :=
  QuotientAddGroup.lift (beta V Pi).range (L.coprod (inl V Pi)) (beta_range_le_ker_phi V Pi L hL)

/--
@isnad1 id=eq.1h6v.s9.78dea1bc82e7 from=translated src=- shape=81170dbc vocab=9222b1c6
-/
@[simp] theorem phi_cls (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m m' : M) :
    phi V Pi L hL (cls V Pi m m') = L m + cls V Pi m' 0 := rfl

/--
@isnad1 id=eq.1h5v.s10.d60d8af783e0 from=translated src=- shape=29f0e1e5 vocab=eaca8e8f
-/
theorem phi_iota (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m : M) : phi V Pi L hL (iota V Pi m) = inl V Pi m := by
  rw [iota_apply, phi_cls, map_zero, zero_add, inl_apply]

/--
@isnad1 id=eq.0h3v.s7.4893362a5374 from=translated src=- shape=e756a23e vocab=d950dc49
-/
theorem cls_zero_zero (V Pi : M →+ M) : cls V Pi 0 0 = 0 := map_zero (mk V Pi)

/--
@isnad1 id=eq.1h5v.s10.7b7e6311e79f from=translated src=- shape=8f7d21c7 vocab=28c44d8e
-/
theorem phi_inl (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (m : M) : phi V Pi L hL (inl V Pi m) = L m := by
  rw [inl_apply, phi_cls, cls_zero_zero, add_zero]

def eta (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    AddSubgroup (NMod V Pi) :=
  (phi V Pi L hL - AddMonoidHom.id (NMod V Pi)).ker

/--
@isnad1 id=iff.1h5v.s9.f748e7c4ff41 from=translated src=- shape=87ed7c70 vocab=e4e114db
-/
theorem mem_eta_iff (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (z : NMod V Pi) :
    z ∈ eta V Pi L hL ↔ phi V Pi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

def u (V Pi : M →+ M) (L : M →+ NMod V Pi) (hL : L.comp V = (inl V Pi).comp Pi) :
    eta V Pi L hL →+ M ⧸ V.range :=
  (toLie V Pi).comp (eta V Pi L hL).subtype

/--
@isnad1 id=eq.1h5v.s11.d15a76b26e5f from=translated src=- shape=eb0d115b vocab=68ab7598
-/
@[simp] theorem u_apply (V Pi : M →+ M) (L : M →+ NMod V Pi)
    (hL : L.comp V = (inl V Pi).comp Pi) (z : eta V Pi L hL) :
    u V Pi L hL z = toLie V Pi (z : NMod V Pi) := rfl

end CartierN

end CerednikDrinfeld

end
