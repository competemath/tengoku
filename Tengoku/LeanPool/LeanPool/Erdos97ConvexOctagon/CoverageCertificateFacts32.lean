/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 32).
@isnad1 id=eq.0h0v.s5.a82997af2628 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_32 :
    branchClaimRootValidB 0 32 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 22).
@isnad1 id=eq.0h0v.s5.ef53c0aa502f from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_22 :
    branchClaimRootValidB 6 22 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 10).
@isnad1 id=eq.0h0v.s5.b4dde444d76a from=translated src=- shape=e9e0773c vocab=ec985d2f
-/
theorem coverageBranchRoot_3_10 :
    branchClaimRootValidB 3 10 (.search branchClaims3Row10) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 6), starting at 64.
@isnad1 id=eq.0h0v.s3.9e3ecd340ee2 from=translated src=- shape=6f582f20 vocab=0fbd34af
-/
theorem coverageBranchNodes_3_06_00064 :
    nodeClaimChunkValidB branchClaims3Row6 64 33 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 10), starting at 0.
@isnad1 id=eq.0h0v.s3.fee20e04aef3 from=translated src=- shape=6f582f20 vocab=ac2dbcb6
-/
theorem coverageBranchNodes_3_10_00000 :
    nodeClaimChunkValidB branchClaims3Row10 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 10), starting at 64.
@isnad1 id=eq.0h0v.s3.4571db323e38 from=translated src=- shape=6f582f20 vocab=ac2dbcb6
-/
theorem coverageBranchNodes_3_10_00064 :
    nodeClaimChunkValidB branchClaims3Row10 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 10), starting at 128.
@isnad1 id=eq.0h0v.s3.982e65424f7e from=translated src=- shape=6f582f20 vocab=ac2dbcb6
-/
theorem coverageBranchNodes_3_10_00128 :
    nodeClaimChunkValidB branchClaims3Row10 128 17 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
