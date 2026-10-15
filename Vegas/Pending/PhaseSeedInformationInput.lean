/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedRecall
import Vegas.Pending.PhaseSeedOperationalInput

/-! # Actual pre-activation local queries are recovered from owner information -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The current callback has not yet appended its own action. Its actual query
uses the complete earlier own word, including choices in retired attempts. -/
def informationInput (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) : PhaseSeedInput graph :=
  { elapsed := view.application.2.native.clock -
      (view.application.2.native.activatedAt coordinate.event).getD view.application.2.native.clock
    activationClocks := (ownerWord runtime leaks coordinate owner past).map Prod.fst
    emissions := (ownerWord runtime leaks coordinate owner past).flatMap fun entry =>
      entry.2.map (Prod.mk entry.1) }

/-- This equality concerns the query BEFORE the genuine activation command.
The new activation is already in environment recall but not yet in own recall. -/
theorem activation_informationInput (execution next : (app).Execution) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (valid : WordRecall runtime leaks execution)
    (reached : next ∈ (execution.environmentStep app (.activate owner)).support) :
    localInput runtime leaks coordinate owner execution.environmentRecall
      (execution.observeEnvironment app) =
        informationInput runtime leaks coordinate owner (next.recall owner)
          (next.observe app owner) := by
  obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
  rw [localInput_word, valid owner coordinate]
  rfl

/-- Equal genuine owner information gives the same erased operational query,
without fixing foreign history, hidden initialization or remainder seeds. -/
theorem activation_operational_eq_of_information_eq
    (first second firstNext secondNext : (app).Execution) (owner : Player)
    (coordinate : CommitAttemptEvent graph)
    (firstValid : WordRecall runtime leaks first) (secondValid : WordRecall runtime leaks second)
    (firstReached : firstNext ∈ (first.environmentStep app (.activate owner)).support)
    (secondReached : secondNext ∈ (second.environmentStep app (.activate owner)).support)
    (same : (firstNext.recall owner, firstNext.observe app owner) =
      (secondNext.recall owner, secondNext.observe app owner)) :
    PhaseSeedInput.operational coordinate.attempt
      (localInput runtime leaks coordinate owner first.environmentRecall
        (first.observeEnvironment app)) =
      PhaseSeedInput.operational coordinate.attempt
        (localInput runtime leaks coordinate owner second.environmentRecall
          (second.observeEnvironment app)) := by
  rw [activation_informationInput runtime leaks first firstNext owner coordinate firstValid
    firstReached, activation_informationInput runtime leaks second secondNext owner coordinate
      secondValid secondReached]
  exact congrArg (fun information => PhaseSeedInput.operational coordinate.attempt
    (informationInput runtime leaks coordinate owner information.1 information.2)) same

end Vegas.EventGraphRuntime.PhaseSeedScheduler
