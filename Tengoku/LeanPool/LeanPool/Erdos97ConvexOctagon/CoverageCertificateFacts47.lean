/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 22).
@isnad1 id=eq.0h0v.s5.c3a41bc83a22 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_22 :
    branchClaimRootValidB 1 22 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 6).
@isnad1 id=eq.0h0v.s5.8b36f5fc2e8c from=translated src=- shape=e9e0773c vocab=a6026712
-/
theorem coverageBranchRoot_5_06 :
    branchClaimRootValidB 5 6 (.search branchClaims5Row6) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 7).
@isnad1 id=eq.0h0v.s5.d2711e635e69 from=translated src=- shape=e9e0773c vocab=443d6a4a
-/
theorem coverageBranchRoot_5_07 :
    branchClaimRootValidB 5 7 (.search branchClaims5Row7) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 5), starting at 64.
@isnad1 id=eq.0h0v.s3.b54a0f2277c9 from=translated src=- shape=6f582f20 vocab=b557c68f
-/
theorem coverageBranchNodes_5_05_00064 :
    nodeClaimChunkValidB branchClaims5Row5 64 30 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 6), starting at 0.
@isnad1 id=eq.0h0v.s3.0809545a5886 from=translated src=- shape=6f582f20 vocab=5e7aae5f
-/
theorem coverageBranchNodes_5_06_00000 :
    nodeClaimChunkValidB branchClaims5Row6 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 6), starting at 64.
@isnad1 id=eq.0h0v.s3.cb7b5a64bb2a from=translated src=- shape=6f582f20 vocab=5e7aae5f
-/
theorem coverageBranchNodes_5_06_00064 :
    nodeClaimChunkValidB branchClaims5Row6 64 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 7), starting at 0.
@isnad1 id=eq.0h0v.s3.65935e15198c from=translated src=- shape=6f582f20 vocab=85116444
-/
theorem coverageBranchNodes_5_07_00000 :
    nodeClaimChunkValidB branchClaims5Row7 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
