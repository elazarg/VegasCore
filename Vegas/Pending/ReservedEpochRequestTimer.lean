/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochRequestProgress

/-! # An unchanged work interval retains the original request timer -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def RequestWatch (inputs : graph.Inputs) (bound : Nat) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (entered : Nat) (execution : (app).Execution) : Prop :=
  WorkValid inputs execution.application ∧ workRemaining execution.application ≤ bound ∧
    (workRemaining execution.application = bound →
      execution.application.SeedRequest owner coordinate ∧
        execution.application.current.native.activatedAt coordinate.event = some entered)

theorem request_watch_invariant (scheduler : (app).Scheduler)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (bound : Nat)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (entered : Nat) :
    (app).ServiceInvariant scheduler
      (RequestWatch runtime leaks inputs bound owner coordinate entered) where
  respond execution actor action watched := by
    obtain ⟨valid, bounded, witness⟩ := watched
    have nextValid := (work_valid_invariant runtime leaks inputs).respond
      execution actor action valid
    have decreases := (work_step_relation runtime leaks).respond
      execution actor action inputs valid
    refine ⟨nextValid, decreases.trans bounded, ?_⟩
    intro flat
    have beforeFlat : workRemaining execution.application = bound := by omega
    obtain ⟨request, activated⟩ := witness beforeFlat
    have nextRequest := respond_request runtime leaks execution actor action owner coordinate
      request
    have same := request.1.symm.trans nextRequest.1
    obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).respond
      execution actor action inputs valid.1 valid.2.1 same
    exact ⟨nextRequest, progress.activated coordinate.event entered activated nextRequest.2.2.1.1⟩
  environment execution next command watched _ moved := by
    obtain ⟨valid, bounded, witness⟩ := watched
    have nextValid := (work_valid_invariant runtime leaks inputs).environmentStep
      execution next command valid moved
    have decreases := (work_step_relation runtime leaks).environmentStep
      execution next command moved inputs valid
    refine ⟨nextValid, decreases.trans bounded, ?_⟩
    intro flat
    have beforeFlat : workRemaining execution.application = bound := by omega
    have equalWork : workRemaining next.application = workRemaining execution.application := by
      omega
    obtain ⟨request, activated⟩ := witness beforeFlat
    have nextRequest := (flat_request_relation runtime leaks ordered).environmentStep
      execution next command moved inputs valid owner coordinate request equalWork
    have same := request.1.symm.trans nextRequest.1
    obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).environmentStep
      execution next command moved inputs valid.1 valid.2.1 same
    exact ⟨nextRequest, progress.activated coordinate.event entered activated nextRequest.2.2.1.1⟩

theorem runRounds_flat_request (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (ordered : graph.RevealRelaxedOrdered) (count : Nat) (inputs : graph.Inputs)
    (before after : (app).Execution) (valid : WorkValid inputs before.application)
    (owner : Player) (coordinate : CommitAttemptEvent graph) (entered : Nat)
    (request : before.application.SeedRequest owner coordinate)
    (activated : before.application.current.native.activatedAt coordinate.event = some entered)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (flat : workRemaining after.application = workRemaining before.application) :
    after.application.SeedRequest owner coordinate ∧
      after.application.current.native.activatedAt coordinate.event = some entered := by
  have watched := (request_watch_invariant runtime leaks scheduler ordered inputs
    (workRemaining before.application) owner coordinate entered).runRounds players count before
      after ⟨valid, le_rfl, fun _ => ⟨request, activated⟩⟩ reached
  exact watched.2.2 flat

end Vegas.EventGraphRuntime.ReservedEpoch
