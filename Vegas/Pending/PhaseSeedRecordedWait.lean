/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCurrentTokens
import Interaction.ReactiveRecordedRounds
import Vegas.Pending.PhaseSeedClosedBound

/-! # Earlier tick closures of a surviving coordinate were actual wait queries -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem retained_bound_runRounds (scheduler : (app).Scheduler)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered) (tick entered : Nat)
    (coordinate : CommitAttemptEvent graph)
    (closed : ClosedCoordinateBound runtime tick entered coordinate execution.application)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    ClosedCoordinateBound runtime tick entered coordinate next.application := by
  let invariant : (app).ServiceInvariant scheduler (fun current =>
      current.application.Invariant inputs ∧ current.application.Ordered ∧
        ClosedCoordinateBound runtime tick entered coordinate current.application) := {
    respond := fun before who action safe =>
      ⟨(phaseApplication_invariant runtime leaks inputs).respond before who action safe.1,
        (phaseApplication_seedOrder runtime leaks).respond before who action safe.2.1,
        ClosedCoordinateBound.respond runtime leaks before who action safe.1 safe.2.1 safe.2.2⟩
    environment := fun before after command safe _ moved =>
      ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep before after command
          safe.1 moved,
        (phaseApplication_seedOrder runtime leaks).environmentStep before after command safe.2.1
          moved,
        ClosedCoordinateBound.environmentStep runtime leaks before after command safe.1 safe.2.1
          moved safe.2.2⟩ }
  exact (invariant.runRounds players count execution next ⟨valid, ordered, closed⟩ reached).2.2

end Vegas.EventGraphRuntime.PhaseSeedCalendar
