-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._001: verified translations of equational_theories/Generated/MagmaEgg/small/_001.lean (58 theorems)
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.EquationalTheories.Deps.Equations

set_option linter.all false

namespace EquationalTheories

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

theorem Equation2558_implies_Equation31 (G: Type _) [Magma G] (h: Equation2558 G) : Equation31 G
:= fun x y =>
  let v0 := M x (M (M x x) x)
  T (h x v0 y) (C (T (C (R v0) (C (S (h y x x)) (R y))) (S (h (M y y) x x))) (R x))

theorem Equation2673_implies_Equation2064 (G: Type _) [Magma G] (h: Equation2673 G) : Equation2064 G
:= fun x y =>
  let v0 := M y y
  let v1 := M x y
  T (T (h x y) (C (C (h v1 y) (R v0)) (R y))) (S (h (M (M v1 y) v0) y))

theorem Equation2737_implies_Equation1722 (G: Type _) [Magma G] (h: Equation2737 G) : Equation1722 G
:= fun x y =>
  let v0 := M x y
  let v1 := M y y
  T (T (h x y) (C (C (R v1) (h v0 y)) (R y))) (S (h (M v1 (M v0 y)) y))

theorem Equation3124_implies_Equation2 (G: Type _) [Magma G] (h: Equation3124 G) : Equation2 G
:= fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (T (h x v0 y) (C (S (h y x x)) h1)) (C (h y x y) h1)) (S (h y v0 y))

theorem Equation3751_implies_Equation3724 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3724 G
:= fun x y =>
  let v0 := M y x
  have h1 := h x y
  T h1 (C (T (T (T (h y x) (C h1 h1)) (S (h v0 v0))) (S h1)) (R v0))

theorem Equation3751_implies_Equation3749 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3749 G
:= fun x y =>
  have h0 := h x y
  let v1 := M y x
  T h0 (C (R v1) (T (T (T (h y x) (C h0 h0)) (S (h v1 v1))) (S h0)))

theorem Equation3932_implies_Equation3729 (G: Type _) [Magma G] (h: Equation3932 G) : Equation3729 G
:= fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (T (T (h x (M y v0) z) (C (C (R x) (S (h y z z))) (R z))) (S (h x y z))) (R v0))

theorem Equation4229_implies_Equation3537 (G: Type _) [Magma G] (h: Equation4229 G) : Equation3537 G
:= fun x y z =>
  let v0 := M z z
  let v1 := M v0 y
  T (T (h x y z) (C (T (h v0 y z) (h v1 v0 z)) (R x))) (S (h x v1 v0))

theorem Equation542_implies_Equation2 (G: Type _) [Magma G] (h: Equation542 G) : Equation2 G
:= fun x y =>
  let v0 := M y y
  have h1 := R v0
  T (T (T (h x v0 y) (C h1 (S (h v0 y x)))) (C h1 (h v0 y y))) (S (h y v0 y))

theorem Equation1256_implies_Equation11 (G: Type _) [Magma G] (h: Equation1256 G) : Equation11 G
:= fun x y =>
  have h0 := S (h (M y y) x x)
  let v1 := M (M (M x x) x) x
  T (h x y v1) (C (R x) (T (C h0 (R v1)) h0))

theorem Equation2310_implies_Equation208 (G: Type _) [Magma G] (h: Equation2310 G) : Equation208 G
:= fun x y =>
  let v0 := M x (M y x)
  T (h x (M x (M v0 (M x v0))) y) (C (S (h v0 x x)) (R x))

theorem Equation2314_implies_Equation221 (G: Type _) [Magma G] (h: Equation2314 G) : Equation221 G
:= fun x y =>
  have h0 := R x
  T (h x y (M y (M y (M x y)))) (C (C (R y) (C h0 (S (h y y x)))) h0)

theorem Equation2795_implies_Equation31 (G: Type _) [Magma G] (h: Equation2795 G) : Equation31 G
:= fun x y =>
  let v0 := M y y
  have h1 := S (h y v0 y)
  let v2 := M v0 y
  T (h x (M v2 v2) y) (C (C h1 h1) (R x))

theorem Equation2882_implies_Equation260 (G: Type _) [Magma G] (h: Equation2882 G) : Equation260 G
:= fun x y =>
  have h0 := R x
  T (h x (M (M y (M x x)) y) y) (C (C (C h0 (S (h y x x))) h0) h0)

theorem Equation2913_implies_Equation2507 (G: Type _) [Magma G] (h: Equation2913 G) : Equation2507 G
:= fun x y =>
  let v0 := M x y
  have h1 := R y
  T (T (h x y) (C (C (C h1 (h v0 y)) h1) h1)) (S (h (M (M y (M v0 y)) y) y))

theorem Equation3397_implies_Equation4374 (G: Type _) [Magma G] (h: Equation3397 G) : Equation4374 G
:= fun x y z w =>
  let v0 := M y z
  have h1 := h y z v0
  T (T (T (C (R x) h1) (S (h z v0 x))) (h z v0 w)) (C (R w) (S h1))

theorem Equation714_implies_Equation1120 (G: Type _) [Magma G] (h: Equation714 G) : Equation1120 G
:= fun x y =>
  let v0 := M y x
  have h1 := R y
  T (T (h x y) (C h1 (C h1 (C (h v0 y) h1)))) (S (h (M y (M (M y v0) y)) y))

theorem Equation823_implies_Equation8 (G: Type _) [Magma G] (h: Equation823 G) : Equation8 G
:= fun x =>
  have h0 := S (h x x)
  let v1 := M x x
  T (h x (M v1 v1)) (C (R x) (C h0 h0))

theorem Equation858_implies_Equation11 (G: Type _) [Magma G] (h: Equation858 G) : Equation11 G
:= fun x y =>
  let v0 := M y y
  have h1 := S (h y v0 y)
  let v2 := M v0 y
  T (h x y (M v2 v2)) (C (R x) (C h1 h1))

theorem Equation1259_implies_Equation105 (G: Type _) [Magma G] (h: Equation1259 G) : Equation105 G
:= fun x y =>
  have h0 := R x
  T (h x y (M (M (M y x) y) y)) (C h0 (C (C (S (h y y x)) h0) (R y)))

theorem Equation1459_implies_Equation2282 (G: Type _) [Magma G] (h: Equation1459 G) : Equation2282 G
:= fun x y z =>
  let v0 := M z z
  let v1 := M y v0
  T (h x v1 v0) (C (R (M x v1)) (S (h y v0 z)))

theorem Equation2239_implies_Equation27 (G: Type _) [Magma G] (h: Equation2239 G) : Equation27 G
:= fun x y z =>
  let v0 := M x (M x (M x x))
  T (h x z) (C (T (h v0 y) (C (S (h x (M v0 (M v0 v0)))) (R y))) (R z))

theorem Equation3146_implies_Equation2 (G: Type _) [Magma G] (h: Equation3146 G) : Equation2 G
:= fun x y =>
  let v0 := M y y
  have h1 := R v0
  T (T (T (h x v0 y) (C (S (h v0 y x)) h1)) (C (h v0 y y) h1)) (S (h y v0 y))

theorem Equation3617_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3617 G) : Equation3820 G
:= fun x y z =>
  let v0 := M z z
  T (h x y v0) (C (R v0) (T (T (h (M v0 x) y z) (C (R z) (C (S (h z x z)) (R y)))) (S (h x y z))))

theorem Equation828_implies_Equation49 (G: Type _) [Magma G] (h: Equation828 G) : Equation49 G
:= fun x y =>
  let v0 := M x x
  T (h x (M v0 v0) y) (C (R x) (C (S (h x x x)) (R (M y x))))

theorem Equation1122_implies_Equation1934 (G: Type _) [Magma G] (h: Equation1122 G) : Equation1934 G
:= fun x y =>
  let v0 := M y (M y y)
  have h1 := h x v0
  T h1 (C (R v0) (T (h (M (M v0 (M v0 v0)) x) y) (C (R y) (S h1))))

theorem Equation1577_implies_Equation968 (G: Type _) [Magma G] (h: Equation1577 G) : Equation968 G
:= fun x y z =>
  let v0 := M z y
  let v1 := M v0 (M z x)
  T (T (h x v0 z) (C (R (M v0 z)) (h v1 z y))) (S (h (M y v1) v0 z))

theorem Equation1590_implies_Equation934 (G: Type _) [Magma G] (h: Equation1590 G) : Equation934 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M v0 (M z x)
  T (T (h x z v0) (C (R (M z v0)) (h v1 y z))) (S (h (M y v1) z v0))

theorem Equation2348_implies_Equation2 (G: Type _) [Magma G] (h: Equation2348 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C (C h1 (C h1 (h v0 y y))) h1)) (S (h y x (M y (M y (M y v0)))))

theorem Equation2364_implies_Equation218 (G: Type _) [Magma G] (h: Equation2364 G) : Equation218 G
:= fun x y =>
  let v0 := M x x
  T (h x y (M x (M x (M v0 v0)))) (C (C (R y) (S (h v0 x x))) (R x))

theorem Equation2964_implies_Equation31 (G: Type _) [Magma G] (h: Equation2964 G) : Equation31 G
:= fun x y =>
  have h0 := S (h y x x)
  let v1 := M (M x (M x x)) x
  T (h x v1 y) (C (C (T (C (R v1) h0) h0) (R y)) (R x))

theorem Equation647_implies_Equation11 (G: Type _) [Magma G] (h: Equation647 G) : Equation11 G
:= fun x y =>
  have h0 := S (h y x x)
  let v1 := M x (M (M x x) x)
  T (h x y v1) (C (R x) (C (R y) (T (C h0 (R v1)) h0)))

theorem Equation710_implies_Equation2 (G: Type _) [Magma G] (h: Equation710 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C h1 (C h1 (C (h v0 y x) h1)))) (S (h y x (M y (M (M v0 x) y))))

theorem Equation1455_implies_Equation2267 (G: Type _) [Magma G] (h: Equation1455 G) : Equation2267 G
:= fun x y =>
  let v0 := M y (M y y)
  let v1 := M x v0
  T (T (h x v0) (C (h v1 y) (R (M v0 (M v0 v0))))) (S (h (M v1 y) v0))

theorem Equation1658_implies_Equation2470 (G: Type _) [Magma G] (h: Equation1658 G) : Equation2470 G
:= fun x y =>
  let v0 := M (M y y) y
  let v1 := M x v0
  T (T (h x v0) (C (h v1 y) (R (M (M v0 v0) v0)))) (S (h (M v1 y) v0))

theorem Equation1934_implies_Equation1122 (G: Type _) [Magma G] (h: Equation1934 G) : Equation1122 G
:= fun x y =>
  let v0 := M y (M y y)
  let v1 := M v0 x
  T (T (h x v0) (C (R (M v0 (M v0 v0))) (h v1 y))) (S (h (M y v1) v0))

theorem Equation2199_implies_Equation1340 (G: Type _) [Magma G] (h: Equation2199 G) : Equation1340 G
:= fun x y z =>
  let v0 := M (M y z) z
  let v1 := M v0 x
  T (T (h x v0 x) (C (R (M v1 x)) (h v1 y z))) (S (h (M y v1) v0 x))

theorem Equation2470_implies_Equation1658 (G: Type _) [Magma G] (h: Equation2470 G) : Equation1658 G
:= fun x y =>
  let v0 := M (M y y) y
  have h1 := h x v0
  T h1 (C (T (h (M x (M (M v0 v0) v0)) y) (C (S h1) (R y))) (R v0))

theorem Equation3756_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3756 G) : Equation3820 G
:= fun x y z =>
  let v0 := M x y
  let v1 := M z z
  let v2 := M v1 v0
  T (T (h x y v2) (C (h y x z) (R (M v2 v2)))) (S (h v1 v0 v2))

theorem Equation910_implies_Equation504 (G: Type _) [Magma G] (h: Equation910 G) : Equation504 G
:= fun x y =>
  let v0 := M y y
  have h1 := h x y
  have h2 := R y
  T h1 (C h2 (T (h (M (M y x) v0) y) (C h2 (C (S h1) (R v0)))))

theorem Equation1072_implies_Equation19 (G: Type _) [Magma G] (h: Equation1072 G) : Equation19 G
:= fun x y z =>
  let v0 := M (M x (M x x)) x
  T (h x y) (C (R y) (T (h v0 z) (C (R z) (S (h x (M v0 (M v0 v0)))))))

theorem Equation1300_implies_Equation2 (G: Type _) [Magma G] (h: Equation1300 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C h1 (C (C (h v0 y y) h1) h1))) (S (h y x (M (M (M v0 y) y) y)))

theorem Equation1325_implies_Equation2137 (G: Type _) [Magma G] (h: Equation1325 G) : Equation2137 G
:= fun x y =>
  let v0 := M (M y y) y
  have h1 := h x v0
  T h1 (C (R v0) (T (h (M (M (M v0 v0) v0) x) y) (C (R y) (S h1))))

theorem Equation1368_implies_Equation1587 (G: Type _) [Magma G] (h: Equation1368 G) : Equation1587 G
:= fun x y z =>
  let v0 := M y z
  have h1 := h x v0 z
  T h1 (C (R v0) (T (h (M (M (M z v0) x) z) z y) (C (R z) (C (S h1) (R y)))))

theorem Equation1374_implies_Equation2186 (G: Type _) [Magma G] (h: Equation1374 G) : Equation2186 G
:= fun x y z =>
  let v0 := M (M y z) y
  have h1 := h x v0 y
  T h1 (C (R v0) (T (h (M (M (M y v0) y) x) z y) (C (R z) (S h1))))

theorem Equation1458_implies_Equation161 (G: Type _) [Magma G] (h: Equation1458 G) : Equation161 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  T (h x y v1) (C (R (M x y)) (C (R y) (T (C (R v1) (h y z y)) (S (h z v0 z)))))

theorem Equation1470_implies_Equation2271 (G: Type _) [Magma G] (h: Equation1470 G) : Equation2271 G
:= fun x y z =>
  let v0 := M y (M y z)
  let v1 := M x v0
  T (T (h x v0 x) (C (h v1 z y) (R (M x v1)))) (S (h (M v1 z) v0 x))

theorem Equation1898_implies_Equation1086 (G: Type _) [Magma G] (h: Equation1898 G) : Equation1086 G
:= fun x y =>
  let v0 := M y y
  let v1 := M x v0
  T (T (h x v0) (C (C (R v0) (h v1 y)) (R (M v0 v0)))) (S (h (M y (M v1 y)) v0))

theorem Equation2079_implies_Equation2891 (G: Type _) [Magma G] (h: Equation2079 G) : Equation2891 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  T (T (h x v0 x) (C (C (h v1 z y) (R x)) (R v1))) (S (h (M (M v1 z) y) v0 x))

theorem Equation2137_implies_Equation1325 (G: Type _) [Magma G] (h: Equation2137 G) : Equation1325 G
:= fun x y =>
  let v0 := M (M y y) y
  let v1 := M v0 x
  T (T (h x v0) (C (R (M (M v0 v0) v0)) (h v1 y))) (S (h (M y v1) v0))

theorem Equation2167_implies_Equation14 (G: Type _) [Magma G] (h: Equation2167 G) : Equation14 G
:= fun x y =>
  let v0 := M x x
  have h1 := h x x x
  T (h x x y) (C (T (C (C h1 (R y)) h1) (S (h y (M v0 x) v0))) (R (M x y)))

theorem Equation2263_implies_Equation23 (G: Type _) [Magma G] (h: Equation2263 G) : Equation23 G
:= fun x =>
  have h0 := R x
  have h1 := S (h x x)
  let v2 := M x (M x (M x x))
  T (h x v2) (C (C h0 (T (C (R v2) h1) h1)) h0)

theorem Equation2267_implies_Equation1455 (G: Type _) [Magma G] (h: Equation2267 G) : Equation1455 G
:= fun x y =>
  let v0 := M y (M y y)
  have h1 := h x v0
  T h1 (C (T (h (M x (M v0 (M v0 v0))) y) (C (S h1) (R y))) (R v0))

theorem Equation2337_implies_Equation3 (G: Type _) [Magma G] (h: Equation2337 G) : Equation3 G
:= fun x =>
  have h0 := S (h x x)
  let v1 := M x (M x (M x x))
  have h2 := R v1
  T (h x v1) (C (T (C h2 (T (C h2 h0) h0)) h0) (R x))

theorem Equation2936_implies_Equation23 (G: Type _) [Magma G] (h: Equation2936 G) : Equation23 G
:= fun x =>
  have h0 := R x
  have h1 := S (h x x)
  let v2 := M (M x (M x x)) x
  T (h x v2) (C (C (T (C (R v2) h1) h1) h0) h0)

theorem Equation2978_implies_Equation2 (G: Type _) [Magma G] (h: Equation2978 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  have h1 := R x
  T (T (h x x x) (C (C (C h1 (h v0 y x)) h1) h1)) (S (h y x (M (M y (M x v0)) y)))

theorem Equation3180_implies_Equation2712 (G: Type _) [Magma G] (h: Equation3180 G) : Equation2712 G
:= fun x y z =>
  have h0 := R x
  let v1 := M y z
  T (h x v1 y) (C (C (C (T (C (h v1 y z) (R y)) (S (h y v1 v1))) h0) (R v1)) h0)

theorem Equation3609_implies_Equation41 (G: Type _) [Magma G] (h: Equation3609 G) : Equation41 G
:= fun x y z =>
  let v0 := M x x
  T (T (h x x v0) (C (R v0) (T (h (M x v0) v0 x) (S (h (M z v0) v0 x))))) (S (h y z v0))

end EquationalTheories
