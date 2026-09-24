/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import GameTheoryExtensions.Core.PendingChoice

/-! # Prescribed submissions, recovery choices, and initialized law equality -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveResolutionPacket_event {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph) :
    (reactiveResolutionPacket who event payload binding outputEq action
      view).event? graph =
      some event := by
  dsimp only [reactiveResolutionPacket]
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
    · rfl
  · rfl

theorem reactiveDecision_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (event : graph.EventId) (action : graph.Action event) (view : ReactivePlayerView graph) :
    (runtime.reactiveDecision leaks who event action view).transmission = none ∨
      ∃ material, (runtime.reactiveDecision leaks who event action view).transmission =
        some (.submit material) ∧ material.call.packet.event? graph = some event := by
  unfold reactiveDecision
  split
  · exact Or.inl rfl
  · cases selected : reactiveFreshSlot view with
    | none => exact Or.inl rfl
    | some serial => exact Or.inr ⟨_, rfl, rfl⟩
  · rename_i owner payload binding checks outputEq codeEq nodeEq
    exact Or.inr ⟨_, rfl,
      reactiveResolutionPacket_event who event payload binding outputEq action view⟩

/-- No replay and no second submission for an event, regardless of how often
the scheduler activates the player or which public grant it offers. -/
theorem prescribedReactivePolicy_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.prescribedReactivePolicy leaks who policy history view).support) :
    action.transmission = none ∨ ∃ event material,
      action.transmission = some (.submit material) ∧ material.call.packet.event? graph = some
        event ∧
        runtime.reactiveAlreadySubmitted leaks history event = false := by
  rw [prescribedReactivePolicy_apply] at supported
  obtain ⟨intentions, _, produced⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨⟨response, intention⟩, issued, rfl⟩ := FinDist.support_map .. ▸ produced
  unfold prescribedReactiveResponse at issued
  split at issued
  · cases FinDist.mem_support_pure.mp issued; exact Or.inl rfl
  · rename_i event grant
    split at issued
    · cases FinDist.mem_support_pure.mp issued; exact Or.inl rfl
    · rename_i unsent
      have absent : runtime.reactiveAlreadySubmitted leaks history event = false :=
        Bool.eq_false_iff.mpr unsent
      split at issued
      · split at issued
        · split at issued
          · obtain ⟨choice, _, image⟩ := FinDist.support_map .. ▸ issued
            have responseEq := congrArg Prod.fst image
            dsimp only at responseEq
            subst response
            rcases runtime.reactiveDecision_transmission leaks who event choice
              view.application with
              silent | ⟨material, sent, addressed⟩
            · exact Or.inl silent
            · exact Or.inr ⟨event, material, sent, addressed, absent⟩
          · cases FinDist.mem_support_pure.mp issued; exact Or.inl rfl
        · cases FinDist.mem_support_pure.mp issued; exact Or.inl rfl
      · cases FinDist.mem_support_pure.mp issued; exact Or.inl rfl

def reactiveSubmittedEvents (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) : List graph.EventId :=
  history.filterMap fun entry => entry.emitted.bind (fun message => message.payload.call.event?
    graph)

theorem reactiveAlreadySubmitted_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId) :
    runtime.reactiveAlreadySubmitted leaks history event = true ↔
      event ∈ runtime.reactiveSubmittedEvents leaks history := by
  simp only [reactiveAlreadySubmitted, reactiveSubmittedEvents, List.any_eq_true,
    List.mem_filterMap, Option.any_eq_true, Option.bind_eq_some_iff, decide_eq_true_eq]

theorem reactiveSubmittedEvents_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (member : message ∈ (runtime.reactiveApplication leaks).outputs history)
    (addressed : message.payload.call.event? graph = some event) :
    event ∈ runtime.reactiveSubmittedEvents leaks history := by
  obtain ⟨entry, retained, emitted⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr
    ⟨entry, retained, by simp only [emitted, Option.bind_some, addressed]⟩

theorem reactiveSubmittedEvents_unique (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (once : (runtime.reactiveSubmittedEvents leaks history).Nodup)
    (first second : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (firstMem : first ∈ (runtime.reactiveApplication leaks).outputs history)
    (secondMem : second ∈ (runtime.reactiveApplication leaks).outputs history)
    (firstEvent : first.payload.call.event? graph = some event)
    (secondEvent : second.payload.call.event? graph = some event) : first = second := by
  obtain ⟨left, leftMem, leftOutput⟩ := List.mem_filterMap.mp firstMem
  obtain ⟨right, rightMem, rightOutput⟩ := List.mem_filterMap.mp secondMem
  let address (entry : (runtime.reactiveApplication leaks).PlayerEntry) :=
    entry.emitted.bind (fun message => message.payload.call.event? graph)
  have separated : history.Pairwise (fun a b =>
      ∀ e, address a = some e → ∀ f, address b = some f → e ≠ f) :=
    List.pairwise_filterMap.mp once
  have identity : history.Pairwise (fun a b =>
      address a = some event → address b = some event → a = b) :=
    separated.imp fun apart ha hb => (apart event ha event hb rfl).elim
  have same : left = right := List.Pairwise.forall_of_forall_of_flip
    (fun _ _ _ _ => rfl) identity
    (identity.imp fun eq ha hb => (eq hb ha).symm) leftMem rightMem
    (by simp only [address, leftOutput, Option.bind_some, firstEvent])
    (by simp only [address, rightOutput, Option.bind_some, secondEvent])
  subst right
  exact Option.some.inj (leftOutput.symm.trans rightOutput)

omit [DecidableEq Player] in
/-- Every recovery choice is supported by the current source decision law,
including choices taken from private memory. -/
theorem reactiveRecoveryLaw_support (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : FinDist (graph.Action event)) (action : graph.Action event)
    (supported : action ∈ (reactiveRecoveryLaw intentions event law).support) :
    action ∈ law.support := by
  classical
  dsimp only [reactiveRecoveryLaw] at supported
  split at supported
  · rename_i remembered selected found
    cases FinDist.mem_support_pure.mp supported
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
  · exact supported

omit [DecidableEq Player] in
theorem reactiveRecoveryLaw_pure (intentions : List (Option graph.Completion))
    (event : graph.EventId) (action : graph.Action event) :
    reactiveRecoveryLaw intentions event (FinDist.pure action) =
      FinDist.pure action := by
  classical
  dsimp only [reactiveRecoveryLaw]
  split
  · rename_i remembered selected found
    have same : selected = action := FinDist.mem_support_pure.mp
      (of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1)
    rw [same]
  · rfl

omit [DecidableEq Player] in
/-- Once a recovery response records a supported choice, another activation
reuses that choice as long as it is still supported. -/
theorem reactiveRecoveryLaw_remembered (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : FinDist (graph.Action event)) (action : graph.Action event)
    (supported : action ∈ law.support) :
    reactiveRecoveryLaw (intentions ++ [some ⟨event, action⟩]) event law =
      FinDist.pure action := by
  classical
  simp [reactiveRecoveryLaw, supported]

omit [DecidableEq Player] in
/-- The actual recovery lottery satisfies the local inclusion incentive law.
The fixed downstream kernel premise still has to be proved for a service;
this result alone does not assert native SPE. -/
theorem reactiveRecoveryLaw_optimal_response (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law retained : FinDist (graph.Action event))
    {Outcome : Type} (continuation : graph.Action event → FinDist Outcome)
    (utility : Outcome → ℝ) (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (law.bind continuation).expect utility)
    (alternative : FinDist (Option (graph.Action event))) :
    ((GameTheory.PendingChoice.responseLaw weight nonnegative atMostOne retained alternative).bind
      continuation).expect utility ≤
    ((GameTheory.PendingChoice.responseLaw weight nonnegative atMostOne retained
      ((reactiveRecoveryLaw intentions event law).map some)).bind continuation).expect
        utility :=
  GameTheory.PendingChoice.optimal_response_of_support weight nonnegative atMostOne retained law
    _ continuation utility optimal
    (fun _ supported => reactiveRecoveryLaw_support intentions event law _ supported)
    alternative

/-- Policy completion preserves initialized canonical state laws playerwise.
The opponents and the observation-local scheduler remain arbitrary. -/
theorem compileReactivePolicy_canonical_run (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (fuel : Nat) :
    let app := runtime.reactiveApplication leaks
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy
        (Function.update players who (runtime.compileReactivePolicy leaks who policy) actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        GameTheory.Protocol.ExecutionProtocol.History.state) =
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy
        (Function.update players who (runtime.prescribedReactivePolicy leaks who policy) actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        GameTheory.Protocol.ExecutionProtocol.History.state) := by
  simpa only [Function.update_self, Function.update_idem, compileReactivePolicy] using
    ReactiveApplication.Policy.recover_canonical_run
      (Function.update players who (runtime.prescribedReactivePolicy leaks who policy)) who
      (runtime.recoverReactivePolicy leaks who policy) initial horizon scheduler fuel

/-- The actual compiler realizes the prescribed private implementation against
arbitrary opponents and scheduling. Its intention list is absent from the game
execution, while all application state, packets, observations and recall agree. -/
theorem compileReactivePolicy_realizes (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (count : Nat) (state : State graph) :
    let app := runtime.reactiveApplication leaks
    let implementation := runtime.prescribedReactiveImplementation leaks who policy
    implementation.initial.bind (implementation.run who players scheduler count
        (ReactiveApplication.Execution.initial app state)) =
      app.runRounds scheduler
        (Function.update players who (runtime.compileReactivePolicy leaks who policy))
        count (ReactiveApplication.Execution.initial app state) := by
  dsimp only
  rw [ReactiveApplication.Implementation.realize_initial]
  have recovery := ReactiveApplication.Policy.recover_runRounds
    (Function.update players who (runtime.prescribedReactivePolicy leaks who policy)) who
    (runtime.recoverReactivePolicy leaks who policy) scheduler count
    (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state) .nil
  simpa only [Function.update_self, Function.update_idem, compileReactivePolicy,
    prescribedReactivePolicy] using recovery.symm

end Vegas.EventGraphRuntime
