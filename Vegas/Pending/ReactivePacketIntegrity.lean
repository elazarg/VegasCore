/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveProvenance
import Vegas.Pending.ReactivePolicyFacts

/-! # Prescribed event packets cannot be replaced by replay or competing traffic

Only the focal player must follow its compiled graph policy. Every envelope
has a submission origin in its author's recall, and that player's recall has
at most one emitted packet per event. Arbitrary opponents and schedulers may
copy that envelope but cannot supply a different one under the same author
and event. This establishes identity, not delivery or application acceptance.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def ReactivePacketIntegrity (runtime : EventGraphRuntime graph) (who : Player)
    (execution : runtime.reactiveApplication.Execution) : Prop :=
  execution.Provenance runtime.reactiveApplication ∧
    (runtime.reactiveSubmittedEvents (execution.recall who)).Nodup

theorem reactiveSubmittedEvents_respond (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who) (execution : runtime.reactiveApplication.Execution)
    (action : runtime.reactiveApplication.Action)
    (once : (runtime.reactiveSubmittedEvents (execution.recall who)).Nodup)
    (supported : action ∈ (runtime.compileReactivePolicy who policy
      (execution.recall who) (execution.observe runtime.reactiveApplication who)).support) :
    (runtime.reactiveSubmittedEvents
      ((execution.respond runtime.reactiveApplication who action).recall who)).Nodup := by
  rcases runtime.compileReactivePolicy_transmission who policy _ _ action supported with
    silent | ⟨event, material, sent, addressed, absent⟩
  · simpa only [ReactiveApplication.Execution.respond, silent, ↓reduceIte,
      reactiveSubmittedEvents, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      Option.bind_none, List.append_nil] using once
  · have fresh : event ∉ runtime.reactiveSubmittedEvents (execution.recall who) := by
      intro member
      have present := (runtime.reactiveAlreadySubmitted_iff _ event).mpr member
      rw [absent] at present
      contradiction
    have appended : (runtime.reactiveSubmittedEvents (execution.recall who) ++ [event]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨once, by simp, ?_⟩
      intro prior member last singleton eq
      cases List.mem_singleton.mp singleton
      exact fresh (eq ▸ member)
    simpa only [ReactiveApplication.Execution.respond, sent, ↓reduceIte,
      reactiveSubmittedEvents, MessageNetwork.submit, reactiveApplication,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Option.bind_some,
      addressed] using appended

/-- The playerwise hypothesis leaves every other player's policy unrestricted. -/
theorem reactivePacketIntegrity_policy (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who) (players : Player → runtime.reactiveApplication.Policy)
    (prescribed : players who = runtime.compileReactivePolicy who policy) :
    runtime.reactiveApplication.PolicyInvariant players (runtime.ReactivePacketIntegrity who) where
  respond execution actor action valid supported := by
    refine ⟨runtime.reactiveApplication.respond_provenance execution actor action valid.1, ?_⟩
    by_cases same : who = actor
    · subst actor
      rw [prescribed] at supported
      exact runtime.reactiveSubmittedEvents_respond who policy execution action valid.2 supported
    · rw [runtime.reactiveApplication.respond_recall_other execution actor who same action]
      exact valid.2
  environment execution next command valid reached := by
    refine ⟨runtime.reactiveApplication.environment_provenance
      execution next command valid.1 reached, ?_⟩
    rw [runtime.reactiveApplication.environmentStep_recall execution next command reached]
    exact valid.2

theorem reactivePacketIntegrity_initial (runtime : EventGraphRuntime graph) (who : Player)
    (state : State graph) : runtime.ReactivePacketIntegrity who
      (ReactiveApplication.Execution.initial runtime.reactiveApplication state) :=
  ⟨MessageNetwork.Satisfies.empty, List.nodup_nil⟩

/-- All retained envelopes from the prescribed owner at this event equal its
remembered output. This covers pending, included, received, and replayed copies. -/
theorem ReactivePacketIntegrity.retained (runtime : EventGraphRuntime graph) (who : Player)
    (execution : runtime.reactiveApplication.Execution)
    (valid : runtime.ReactivePacketIntegrity who execution)
    (message : Message Player (Payload graph)) (event : graph.EventId)
    (emitted : message ∈ runtime.reactiveApplication.outputs (execution.recall who))
    (addressed : message.payload.event? graph = some event) :
    execution.network.Satisfies (fun retained =>
      retained.sender = who → retained.payload.event? graph = some event →
        retained = message) := by
  apply valid.1.mono
  intro retained origin author atEvent
  obtain ⟨entry, member, material, _, output, _⟩ := origin
  rw [author] at member
  exact runtime.reactiveSubmittedEvents_unique (execution.recall who) valid.2
    retained message event (List.mem_filterMap.mpr ⟨entry, member, output⟩)
      emitted atEvent addressed

/-- Packet integrity holds at every prefix of canonical behavioral play, for
every scheduler and arbitrary opponent policies. -/
theorem canonical_reactivePacketIntegrity (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who) (players : Player → runtime.reactiveApplication.Policy)
    (prescribed : players who = runtime.compileReactivePolicy who policy)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : runtime.reactiveApplication.Scheduler) (fuel : Nat)
    (result : runtime.reactiveApplication.ProtocolState)
    (supported : result ∈ (((runtime.reactiveApplication.information
      initial horizon scheduler).runSingleMoverBehavioralFrom
        (runtime.reactiveApplication.singleMover initial horizon scheduler)
        (fun player => runtime.reactiveApplication.encodePolicy (players player)) fuel
        (runtime.reactiveApplication.protocol initial horizon scheduler).initHistory).map
          ExecutionProtocol.History.state).support) :
    ReactiveApplication.executionInvariant (runtime.ReactivePacketIntegrity who) result :=
  (runtime.reactivePacketIntegrity_policy who policy players prescribed).canonical_run
    initial horizon scheduler (fun state _ => runtime.reactivePacketIntegrity_initial who state)
      fuel result supported

end Vegas.EventGraphRuntime
