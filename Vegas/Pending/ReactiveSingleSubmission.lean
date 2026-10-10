/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveAsyncContract
import Interaction.ReactivePolicyInvariant

/-! # Unique prescribed event submissions on actual runs -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Faithful positive prescribed recall contains at most one emitted packet
for each event, irrespective of repeated activations. -/
theorem prescribedReactiveSubmittedEvents_nodup (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (faithful : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet) :
    (runtime.reactiveSubmittedEvents leaks history).Nodup := by
  induction consistent with
  | nil => exact List.nodup_nil
  | @snoc history entry consistent positive ih =>
      have prior := ih (fun earlier member => quiet earlier (List.mem_append_left _ member))
        (fun earlier member => faithful earlier (List.mem_append_left _ member))
      have emitted := runtime.prescribedReactivePolicy_transmission leaks who policy
        history entry.beforeView entry.action positive
      have last : entry ∈ history ++ [entry] :=
        List.mem_append_right _ (List.mem_singleton.mpr rfl)
      rcases emitted with silent | ⟨event, material, sent, addressed, absent⟩
      · have output := quiet entry last silent
        simpa only [reactiveSubmittedEvents, List.filterMap_append,
          List.filterMap_cons, List.filterMap_nil, output, Option.bind_none,
          List.append_nil] using prior
      · obtain ⟨message, output, callEq⟩ := faithful entry last material sent
        have eventEq : message.payload.call.event? graph = some event := by
          rw [callEq]
          exact addressed
        have missing : event ∉ runtime.reactiveSubmittedEvents leaks history := by
          intro member
          have yes := (runtime.reactiveAlreadySubmitted_iff leaks history event).mpr member
          rw [absent] at yes
          cases yes
        simpa only [reactiveSubmittedEvents, List.filterMap_append,
          List.filterMap_cons, List.filterMap_nil, output, Option.bind_some, eventEq]
          using (List.nodup_append.mpr ⟨prior, List.nodup_singleton event,
            by
              intro a member b selected same
              have equal : b = event := List.mem_singleton.mp selected
              exact missing (equal ▸ same ▸ member)⟩)

/-- An actual unique prescribed event emission discharges the scheduler's
sole-identifier protection condition on all the other recalled responses. -/
theorem prescribedReactiveEmission_sole (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (earlier later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (once : (runtime.reactiveSubmittedEvents leaks (earlier ++ entry :: later)).Nodup)
    (emitted : entry.emitted = some message)
    (addressed : message.payload.call.event? graph = some event) :
    ∀ other ∈ earlier ++ later, ¬ runtime.EmitsOtherFor leaks other event message.id := by
  intro other member conflicting
  obtain ⟨second, output, _, secondEvent, different⟩ := conflicting
  have firstMem : message ∈ (runtime.reactiveApplication leaks).outputs
      (earlier ++ entry :: later) :=
    List.mem_filterMap.mpr ⟨entry,
      List.mem_append_right _ List.mem_cons_self, emitted⟩
  have secondMember : other ∈ earlier ++ entry :: later := by
    rcases List.mem_append.mp member with before | after
    · exact List.mem_append_left _ before
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)
  have secondMem : second ∈ (runtime.reactiveApplication leaks).outputs
      (earlier ++ entry :: later) :=
    List.mem_filterMap.mpr ⟨other, secondMember, output⟩
  exact different (congrArg Message.id
    (runtime.reactiveSubmittedEvents_unique leaks _ once second message event secondMem firstMem
      secondEvent addressed))


/-- The actual prescribed focal policy emits at most one packet per event
through all supported runtime steps, with arbitrary opponent policies. -/
theorem prescribedReactiveSubmittedEvents_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players who = runtime.prescribedReactivePolicy leaks who policy) :
    (runtime.reactiveApplication leaks).PolicyInvariant players (fun execution =>
      (runtime.reactiveSubmittedEvents leaks (execution.recall who)).Nodup) where
  respond execution actor action valid supported := by
    let app := runtime.reactiveApplication leaks
    by_cases same : who = actor
    · subst actor
      rw [focal] at supported
      rcases runtime.prescribedReactivePolicy_transmission leaks who policy
        (execution.recall who) (execution.observe app who) action supported with
        silent | ⟨event, material, sent, addressed, absent⟩
      · cases action with
        | mk transmission =>
            cases silent
            simpa only [ReactiveApplication.Execution.respond, ↓reduceIte,
              reactiveSubmittedEvents, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, Option.bind_none, List.append_nil] using valid
      · have missing : event ∉ runtime.reactiveSubmittedEvents leaks (execution.recall who) := by
          intro member
          have yes := (runtime.reactiveAlreadySubmitted_iff leaks _ event).mpr member
          rw [absent] at yes
          cases yes
        have extended :
            (runtime.reactiveSubmittedEvents leaks (execution.recall who) ++ [event]).Nodup :=
          List.nodup_append.mpr ⟨valid, List.nodup_singleton event, by
            intro a member b selected equal
            have chosen : b = event := List.mem_singleton.mp selected
            exact missing (chosen ▸ equal ▸ member)⟩
        cases action with
        | mk transmission =>
            cases sent
            simpa only [ReactiveApplication.Execution.respond, ↓reduceIte,
              reactiveSubmittedEvents, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, Option.bind_some, reactiveApplication,
              MessageNetwork.submit, WitnessedSubmission.emit, addressed] using extended
    · rw [app.respond_recall_other execution actor who same action]
      exact valid
  environment execution next command valid supported := by
    rw [(runtime.reactiveApplication leaks).environmentStep_recall
      execution next command supported]
    exact valid

/-- Sole event emission holds on the actual supported run with arbitrary
opponents and scheduler, starting from empty focal response recall. -/
theorem prescribedReactiveSubmittedEvents_runRounds (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players who = runtime.prescribedReactivePolicy leaks who policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (empty : execution.recall who = [])
    (supported : next ∈
      ((runtime.reactiveApplication leaks).runRounds scheduler players count execution).support) :
    (runtime.reactiveSubmittedEvents leaks (next.recall who)).Nodup := by
  have invariant := runtime.prescribedReactiveSubmittedEvents_invariant
    leaks who policy players focal
  apply invariant.runRounds scheduler count execution next _ supported
  simp only [empty, reactiveSubmittedEvents, List.filterMap_nil, List.nodup_nil]

end Vegas.EventGraphRuntime
