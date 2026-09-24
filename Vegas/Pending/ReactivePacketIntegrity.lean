/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts

/-! # Prescribed event packets cannot be replaced by replay or competing traffic

Only the focal player must follow its compiled graph policy. Every envelope
has a submission origin in its author's recall, and that player's recall has
at most one emitted packet per event. Arbitrary opponents and schedulers may
copy that envelope but cannot supply a different one under the same author
and event. Application acceptance and retention until inclusion are separate
obligations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def ReactivePacketIntegrity (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.Provenance (runtime.reactiveApplication leaks) ∧
    (runtime.reactiveSubmittedEvents leaks (execution.recall who)).Nodup

theorem reactiveSubmittedEvents_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (once : (runtime.reactiveSubmittedEvents leaks (execution.recall who)).Nodup)
    (supported : action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks)
        who)).support) :
    (runtime.reactiveSubmittedEvents leaks
      ((execution.respond (runtime.reactiveApplication leaks) who action).recall who)).Nodup := by
  rcases runtime.prescribedReactivePolicy_transmission leaks who policy _ _ action supported with
    silent | ⟨event, material, sent, addressed, absent⟩
  · simpa only [ReactiveApplication.Execution.respond, silent, ↓reduceIte,
      reactiveSubmittedEvents, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Option.bind_none, List.append_nil] using once
  · have fresh : event ∉ runtime.reactiveSubmittedEvents leaks (execution.recall who) := by
      intro member
      have present := (runtime.reactiveAlreadySubmitted_iff leaks _ event).mpr member
      rw [absent] at present
      contradiction
    have appended : (runtime.reactiveSubmittedEvents leaks (execution.recall who) ++
      [event]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨once, by simp, ?_⟩
      intro prior member last singleton eq
      cases List.mem_singleton.mp singleton
      exact fresh (eq ▸ member)
    simpa only [ReactiveApplication.Execution.respond, sent, ↓reduceIte,
      reactiveSubmittedEvents, MessageNetwork.submit, reactiveApplication,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Option.bind_some,
      WitnessedSubmission.emit_call, addressed] using appended

/-- The playerwise hypothesis leaves every other player's policy unrestricted. -/
theorem reactivePacketIntegrity_policy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players who = runtime.prescribedReactivePolicy leaks who policy) :
    (runtime.reactiveApplication leaks).PolicyInvariant players
      (runtime.ReactivePacketIntegrity leaks who) where
  respond execution actor action valid supported := by
    refine ⟨(runtime.reactiveApplication leaks).respond_provenance execution actor action
      valid.1, ?_⟩
    by_cases same : who = actor
    · subst actor
      rw [prescribed] at supported
      exact runtime.reactiveSubmittedEvents_respond leaks who policy execution action
        valid.2 supported
    · rw [(runtime.reactiveApplication leaks).respond_recall_other execution actor who
      same action]
      exact valid.2
  environment execution next command valid reached := by
    refine ⟨(runtime.reactiveApplication leaks).environment_provenance
      execution next command valid.1 reached, ?_⟩
    rw [(runtime.reactiveApplication leaks).environmentStep_recall execution next command reached]
    exact valid.2

theorem reactivePacketIntegrity_initial (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (state : State graph) : runtime.ReactivePacketIntegrity leaks who
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state) :=
  ⟨MessageNetwork.Satisfies.empty, List.nodup_nil⟩

/-- All retained envelopes from the prescribed owner at this event equal its
remembered output. This covers pending, included, received, and replayed copies. -/
theorem ReactivePacketIntegrity.retained (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : runtime.ReactivePacketIntegrity leaks who execution)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (emitted : message ∈ (runtime.reactiveApplication leaks).outputs (execution.recall who))
    (addressed : message.payload.call.event? graph = some event) :
    execution.network.Satisfies (fun retained =>
      retained.sender = who → retained.payload.call.event? graph = some event →
        retained = message) := by
  apply valid.1.mono
  intro retained origin author atEvent
  obtain ⟨entry, member, material, _, output, _⟩ := origin
  rw [author] at member
  exact runtime.reactiveSubmittedEvents_unique leaks (execution.recall who) valid.2
    retained message event (List.mem_filterMap.mpr ⟨entry, member, output⟩)
      emitted atEvent addressed

/-- Packet integrity holds at every prefix of canonical behavioral play, for
every scheduler and arbitrary opponent policies. -/
theorem canonical_reactivePacketIntegrity (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players who = runtime.compileReactivePolicy leaks who policy)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (fuel : Nat)
    (result : (runtime.reactiveApplication leaks).ProtocolState)
    (supported : result ∈ ((((runtime.reactiveApplication leaks).information
      initial horizon scheduler).runSingleMoverBehavioralFrom
        ((runtime.reactiveApplication leaks).singleMover initial horizon scheduler)
        (fun player => (runtime.reactiveApplication leaks).encodePolicy (players player)) fuel
        ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).initHistory).map
          ExecutionProtocol.History.state).support) :
    ReactiveApplication.executionInvariant (runtime.ReactivePacketIntegrity leaks who) result :=
  by
    have updateEq : Function.update players who
        (runtime.compileReactivePolicy leaks who policy) = players := by
      rw [← prescribed, Function.update_eq_self]
    rw [← updateEq, runtime.compileReactivePolicy_canonical_run leaks who policy players
      initial horizon scheduler fuel] at supported
    exact (runtime.reactivePacketIntegrity_policy leaks who policy _
      (Function.update_self ..)).canonical_run initial horizon scheduler
        (fun state _ => runtime.reactivePacketIntegrity_initial leaks who state)
        fuel result supported

end Vegas.EventGraphRuntime
