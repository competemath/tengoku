/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 11).
@isnad1 id=eq.0h0v.s5.33011f1c73b5 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_11 :
    branchClaimRootValidB 1 11 (.patternThree 178) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 64.
@isnad1 id=eq.0h0v.s3.7dd581f7c052 from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00064 :
    nodeClaimChunkValidB branchClaims3Row27 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 128.
@isnad1 id=eq.0h0v.s3.19fc6599c621 from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00128 :
    nodeClaimChunkValidB branchClaims3Row27 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 192.
@isnad1 id=eq.0h0v.s3.758ad7e669d8 from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00192 :
    nodeClaimChunkValidB branchClaims3Row27 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 256.
@isnad1 id=eq.0h0v.s3.4cdc27afafc4 from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00256 :
    nodeClaimChunkValidB branchClaims3Row27 256 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
