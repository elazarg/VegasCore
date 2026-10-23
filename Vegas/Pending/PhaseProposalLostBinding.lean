/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback

/-! # Omitted bindings at genuine finished attempts

An absent accepted handle is a physical omission. Accepted unusable private
preparations remain distinct. No clear-attempt restriction is used.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace RecoveryState

omit [DecidableEq Player] in
/-- A finished omitted binding has permanently excluded its owner, independent
of the private typed meaning of any unaccepted prepared candidate. -/
theorem excluded_of_finished_unaccepted_binding
    (state : RecoveryState graph) (phase : RuntimePhase graph)
    (finished : phase.Finished state) (coverage : state.FailureCoverage)
    (event : graph.EventId) (inside : event ∈ phase.events)
    (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (unaccepted : state.native.accepted (.inr event) = none) : owner ∈ state.excluded := by
  have failed := (state.native.publicFailure_iff_accepted_none event owner payload binding
    (finished inside)).mpr unaccepted
  exact coverage.covered event owner (actor?_of_outputLayout_binding graph binding) failed

end RecoveryState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

end Vegas.EventGraphRuntime
