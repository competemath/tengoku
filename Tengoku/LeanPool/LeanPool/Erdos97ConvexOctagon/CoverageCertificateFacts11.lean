/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 11).
@isnad1 id=eq.0h0v.s5.3eb819ade9be from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_11 :
    branchClaimRootValidB 0 11 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 29).
@isnad1 id=eq.0h0v.s5.b0800477dbc4 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_29 :
    branchClaimRootValidB 4 29 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 33).
@isnad1 id=eq.0h0v.s5.087da1d304b8 from=translated src=- shape=e9e0773c vocab=7e46c718
-/
theorem coverageBranchRoot_1_33 :
    branchClaimRootValidB 1 33 (.search branchClaims1Row33) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 32), starting at 64.
@isnad1 id=eq.0h0v.s3.a6e3a51a93b1 from=translated src=- shape=6f582f20 vocab=60ebc641
-/
theorem coverageBranchNodes_1_32_00064 :
    nodeClaimChunkValidB branchClaims1Row32 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 32), starting at 128.
@isnad1 id=eq.0h0v.s3.0f69b24e6eb6 from=translated src=- shape=6f582f20 vocab=60ebc641
-/
theorem coverageBranchNodes_1_32_00128 :
    nodeClaimChunkValidB branchClaims1Row32 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 32), starting at 192.
@isnad1 id=eq.0h0v.s3.53043a1949a9 from=translated src=- shape=6f582f20 vocab=60ebc641
-/
theorem coverageBranchNodes_1_32_00192 :
    nodeClaimChunkValidB branchClaims1Row32 192 54 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 33), starting at 0.
@isnad1 id=eq.0h0v.s3.9e461ffd7c98 from=translated src=- shape=6f582f20 vocab=54a98a78
-/
theorem coverageBranchNodes_1_33_00000 :
    nodeClaimChunkValidB branchClaims1Row33 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
