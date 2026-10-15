/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 33).
@isnad1 id=eq.0h0v.s5.ddfe2a6e4d2b from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_33 :
    branchClaimRootValidB 3 33 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 2).
@isnad1 id=eq.0h0v.s5.7f6c904b44ab from=translated src=- shape=e9e0773c vocab=590f043a
-/
theorem coverageBranchRoot_6_02 :
    branchClaimRootValidB 6 2 (.search branchClaims6Row2) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 3).
@isnad1 id=eq.0h0v.s5.81c355fcbc18 from=translated src=- shape=e9e0773c vocab=e24c45a3
-/
theorem coverageBranchRoot_6_03 :
    branchClaimRootValidB 6 3 (.search branchClaims6Row3) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 4).
@isnad1 id=eq.0h0v.s5.5c205fdbd95d from=translated src=- shape=e9e0773c vocab=096bf85d
-/
theorem coverageBranchRoot_6_04 :
    branchClaimRootValidB 6 4 (.search branchClaims6Row4) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 1), starting at 64.
@isnad1 id=eq.0h0v.s3.fda8dfb6febe from=translated src=- shape=6f582f20 vocab=13534537
-/
theorem coverageBranchNodes_6_01_00064 :
    nodeClaimChunkValidB branchClaims6Row1 64 1 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 2), starting at 0.
@isnad1 id=eq.0h0v.s3.afe84552a6a9 from=translated src=- shape=6f582f20 vocab=f3ba7148
-/
theorem coverageBranchNodes_6_02_00000 :
    nodeClaimChunkValidB branchClaims6Row2 0 52 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 3), starting at 0.
@isnad1 id=eq.0h0v.s3.9adbafb19d9e from=translated src=- shape=6f582f20 vocab=09e0b44e
-/
theorem coverageBranchNodes_6_03_00000 :
    nodeClaimChunkValidB branchClaims6Row3 0 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 4), starting at 0.
@isnad1 id=eq.0h0v.s3.93ec7547e342 from=translated src=- shape=6f582f20 vocab=1ee9c179
-/
theorem coverageBranchNodes_6_04_00000 :
    nodeClaimChunkValidB branchClaims6Row4 0 51 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
