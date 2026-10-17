/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingAsyncService
import Vegas.Examples.CommitSeedSignallingHalfSuccess
import Vegas.Examples.CommitSeedSignallingBobJoint
import Vegas.Examples.CommitSeedSignallingAcceptanceBoundary
import Vegas.Examples.CommitSeedSignallingAlicePrePoll
import Vegas.Examples.CommitSeedSignallingBobIncentives
import Vegas.Examples.CommitSeedSignallingCountedContinuation
import Vegas.Examples.CommitSeedSignallingUnopenedContinuation
import Vegas.Examples.CommitSeedSignallingCountedSeedTrace
import Vegas.Examples.CommitSeedSignallingTailRecall
import Vegas.Examples.CommitSeedSignallingInitializedPayoff

/-! # Native service and conditional timing bounds for private-seed signalling

These results establish the actual raw asynchronous contract, the conditional
late-acceptance bound and exact physical payoff identities. They do not assert
private calendar or success laws, or exclude every preserving equilibrium.
-/
