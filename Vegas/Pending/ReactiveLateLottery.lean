/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLateBlind
import Interaction.PendingErasureSelection

/-! # Public identifier lotteries satisfy late-packet erasure independence

This instantiates the runtime's named erasure-independence hypothesis with an
ordinary public lottery over all pending identifiers. The lottery inspects no
private value and permits rejection of any selected packet by the application.
No asynchronous service contract or equilibrium preservation is asserted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
    {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Equal-weight public identifier selection is erasure-independent for every
pending packet, hence for every packet sent after its protected window. -/
theorem blindToLatePackets_pendingLottery (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bound : graph.EventId → Nat) (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.BlindToLatePackets leaks bound
      ((runtime.reactiveApplication leaks).pendingLotteryScheduler weight nonnegative) := by
  intro recall view message pending _
  exact (runtime.reactiveApplication leaks).pendingLotteryScheduler_include_or_erased
    weight nonnegative recall view message pending

end Vegas.EventGraphRuntime
