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

/-- Root audit for fixed branch (4, 1).
@isnad1 id=eq.0h0v.s5.67347d14620b from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_01 :
    branchClaimRootValidB 4 1 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 10).
@isnad1 id=eq.0h0v.s5.3e7e8da80a45 from=translated src=- shape=e9e0773c vocab=5d245b69
-/
theorem coverageBranchRoot_6_10 :
    branchClaimRootValidB 6 10 (.search branchClaims6Row10) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 9), starting at 64.
@isnad1 id=eq.0h0v.s3.aeacf4112796 from=translated src=- shape=6f582f20 vocab=ee60d6c2
-/
theorem coverageBranchNodes_6_09_00064 :
    nodeClaimChunkValidB branchClaims6Row9 64 51 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 0.
@isnad1 id=eq.0h0v.s3.0b0239d31fd0 from=translated src=- shape=6f582f20 vocab=fe48f456
-/
theorem coverageBranchNodes_6_10_00000 :
    nodeClaimChunkValidB branchClaims6Row10 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 64.
@isnad1 id=eq.0h0v.s3.0b9c4ce4b0d0 from=translated src=- shape=6f582f20 vocab=fe48f456
-/
theorem coverageBranchNodes_6_10_00064 :
    nodeClaimChunkValidB branchClaims6Row10 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 10), starting at 128.
@isnad1 id=eq.0h0v.s3.706f7e5623cf from=translated src=- shape=6f582f20 vocab=fe48f456
-/
theorem coverageBranchNodes_6_10_00128 :
    nodeClaimChunkValidB branchClaims6Row10 128 30 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
