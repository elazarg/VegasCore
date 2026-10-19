/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalLostBindingSuffix
import Vegas.Pending.PhaseProposalUnusedPreparation
import Vegas.Pending.PhaseBindingIdleMenu
import Interaction.ReactiveInvariantPrefix

/-! # Actual lost-preparation replay after the original exclusion

Permanent exclusion supplies all later silent callback and rejected include
facts. The saved and current nonassociation invariant survives arbitrary
further retries, samples, processing and phase installation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A genuine suffix beginning just after the original lost sender's exclusion
has a genuine image under the original initial law and scheduler. Its complete
physical and non-sender recall projection is preserved through all later phases. -/
theorem phase_lost_binding_replay_after_close
    (scheduler : (app).Scheduler) (owner : Player) (slot : CandidateSlot graph)
    (first second : Raw L) (start finish : (app).Control)
    (startTrace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (trace : ((menu).protocol initial horizon scheduler).Trace (some finish))
    (retained : TracePrefix startTrace trace)
    (excluded : owner ∈ start.execution.application.current.excluded)
    (saved : start.execution.application.entry.native.HandleUnused (owner, slot))
    (active : start.execution.application.current.native.HandleUnused (owner, slot))
    (image : (app).Execution)
    (imagePrefix : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨start.remaining, start.actor, image⟩))
    (paired : image.eraseRecall app owner =
      ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution
        start.execution).eraseRecall app owner) :
    ∃ (target : (app).Execution)
      (imageTrace : ((menu).protocol initial horizon scheduler).Trace
        (some ⟨finish.remaining, finish.actor, target⟩)),
      TracePrefix imagePrefix imageTrace ∧
      target.eraseRecall app owner =
        ((HiddenSwap.preparationOnly (owner, slot) first second).phaseExecution
          finish.execution).eraseRecall app owner ∧
        imageTrace.transitionMass * startTrace.transitionMass =
          trace.transitionMass * imagePrefix.transitionMass ∧
      (∀ policy : ((menu).information initial horizon scheduler).BehavioralPolicy owner,
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner imageTrace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner imagePrefix)) ∧
      ∀ policy : ((menu).information initial horizon scheduler).BehavioralPolicy owner,
        ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner trace) =
          ((menu).information initial horizon scheduler).ownPlayReachProbability policy
            (((menu).information initial horizon scheduler).ownPlay owner startTrace) := by
  have persists (control : (app).Control)
      (prior : ((menu).protocol initial horizon scheduler).Trace (some control))
      (fromStart : TracePrefix startTrace prior) :
      owner ∈ control.execution.application.current.excluded ∧
        control.execution.application.entry.native.HandleUnused (owner, slot) ∧
          control.execution.application.current.native.HandleUnused (owner, slot) :=
    (phaseApplication_excluded_unused_preparation runtime leaks (owner, slot)).tracePrefix
      menu initial horizon scheduler start control startTrace prior fromStart
        ⟨excluded, saved, active⟩
  apply phase_lost_binding_suffix_replay runtime leaks bounds initial horizon scheduler owner slot
    first second start finish startTrace trace retained image imagePrefix paired
  · intro remaining execution prior fromStart _kept
    have original := persists ⟨remaining, some owner, execution⟩ prior fromStart
    apply PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan inputs
      horizon scheduler remaining owner execution prior
    intro coordinate request
    exact request.2.2.2.2 original.1
  · intro remaining execution prior fromStart _kept image imageTrace paired
    have excluded := (persists ⟨remaining, some owner, execution⟩ prior fromStart).1
    have imageExcluded : owner ∈ image.application.current.excluded := by
      have application := congrArg
        (fun value : (app).Execution => value.application.current.excluded) paired
      change image.application.current.excluded = execution.application.current.excluded
        at application
      rw [application]
      exact excluded
    apply PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan inputs
      horizon scheduler remaining owner image imageTrace
    intro coordinate request
    exact request.2.2.2.2 imageExcluded
  · intro control prior fromStart _kept
    exact (persists control prior fromStart).2.2
  · intro remaining execution prior fromStart _command _next _selected _moved _nextTrace
      _extended _kept _id message event _chosen _found call
    exact PhaseRuntimeState.handle_commitment_none_of_handle_owner_excluded runtime
      execution.application message event (owner, slot) call
        (persists ⟨remaining + 1, none, execution⟩ prior fromStart).1

end Vegas.EventGraphRuntime
