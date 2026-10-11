/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResponseSampling

/-! # First source opportunities in supported private memory -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every fresh private intention names the actual source turn of its callback. -/
theorem prescribedReactiveResponse_intention_turn (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    view.application.publicView.ownTurn? who = some remembered.event := by
  unfold prescribedReactiveResponse at supported
  split at supported
  · simp at supported
  · rename_i event turn
    split at supported
    · simp at supported
    · split at supported
      · split at supported
        · split at supported
          · obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ supported
            have named : event = remembered.event := congrArg Completion.event
              (Option.some.inj (congrArg Prod.snd image))
            exact turn.trans (congrArg some named)
          · simp at supported
        · simp at supported
      · simp at supported

/-- Before the first callback for an event, every supported private posterior
has no retained intention for it. Other players and scheduling are unrestricted. -/
theorem prescribedReactivePosterior_no_intention_before_turn
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (event : graph.EventId)
    (earlierTurns : ∀ entry ∈ history,
      entry.beforeView.application.publicView.ownTurn? who ≠ some event)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ remembered, some remembered ∈ intentions → remembered.event ≠ event := by
  induction consistent generalizing intentions with
  | nil =>
      have lengths := runtime.prescribedReactivePosterior_length leaks who policy
        .nil intentions supported
      have empty : intentions = [] := List.eq_nil_of_length_eq_zero lengths
      simp [empty]
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      intro remembered member named
      rw [memoryEq] at member
      rcases List.mem_append.mp member with previousMember | currentMember
      · exact ih (fun entry member => earlierTurns entry (List.mem_append_left _ member))
          previous prior remembered previousMember named
      · have savedEq : saved = some remembered := (List.mem_singleton.mp currentMember).symm
        rw [savedEq] at produced
        have turn := runtime.prescribedReactiveResponse_intention_turn leaks who policy
          history previous latest.beforeView latest.action remembered produced
        exact earlierTurns latest (List.mem_append_right _ (by simp)) (by simpa [named] using turn)

/-- At the first source callback, both compiler freshness flags are false in
every supported memory. These flags follow from recorded turns and emissions. -/
theorem prescribedReactivePosterior_fresh_before_turn (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (event : graph.EventId)
    (earlierTurns : ∀ entry ∈ history,
      entry.beforeView.application.publicView.ownTurn? who ≠ some event)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    runtime.reactiveAlreadySubmitted leaks history event = false ∧
      runtime.reactiveAlreadyDecided leaks who history intentions event = false := by
  have absent := runtime.prescribedReactivePosterior_no_intention_before_turn
    leaks who policy consistent event earlierTurns intentions supported
  constructor
  · cases submitted : runtime.reactiveAlreadySubmitted leaks history event with
    | false => rfl
    | true =>
        obtain ⟨remembered, member, named⟩ :=
          runtime.prescribedReactivePosterior_submitted_coverage leaks who policy consistent
            quiet sent intentions supported event submitted
        exact False.elim (absent remembered member named)
  · cases decided : runtime.reactiveAlreadyDecided leaks who history intentions event with
    | false => rfl
    | true =>
        obtain ⟨remembered, member, named⟩ :=
          runtime.reactiveAlreadyDecided_memory leaks who history intentions event decided
        exact False.elim (absent remembered member named)

/-- First-opportunity freshness is operational for initialized runs with the
actual prescribed focal policy and arbitrary raw policies of everyone else. -/
theorem prescribedReactivePosterior_fresh_before_turn_of_initialized_support
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (focal : players who = runtime.prescribedReactivePolicy leaks who policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (event : graph.EventId)
    (earlierTurns : ∀ entry ∈ execution.recall who,
      entry.beforeView.application.publicView.ownTurn? who ≠ some event)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).support) :
    runtime.reactiveAlreadySubmitted leaks (execution.recall who) event = false ∧
      runtime.reactiveAlreadyDecided leaks who (execution.recall who) intentions event = false := by
  have consistent :=
    ((runtime.reactiveApplication leaks).consistentRecall_policyInvariant players).runRounds
      scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (fun owner => .nil) reached
  have ownConsistent := consistent who
  rw [focal] at ownConsistent
  have quiet :=
    ((runtime.reactiveApplication leaks).silentEmission_invariant players who).runRounds
      scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  have sent :=
    (runtime.reactiveEmission_call_invariant leaks players who).runRounds scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  exact runtime.prescribedReactivePosterior_fresh_before_turn leaks who policy ownConsistent
    quiet sent event earlierTurns intentions supported

/-- Once a recorded ready source callback sampled or reused its event, every
later callback for that event is silent under the actual behavioral compiler. -/
theorem prescribedReactivePolicy_silent_after_recorded_turn
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (quiet : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ history, ∀ material, entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (event : graph.EventId) (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (retained : entry ∈ history)
    (earlierTurn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (identity : entry.beforeView.application.who = who)
    (owned : graph.actor? event = some who)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (turn : view.application.publicView.ownTurn? who = some event) :
    runtime.prescribedReactivePolicy leaks who policy history view = PMF.pure ⟨none⟩ := by
  have ready := (entry.beforeView.application.publicView.ownTurn?_spec who event earlierTurn).1
  rw [prescribedReactivePolicy, ReactiveApplication.Implementation.policy_eq]
  simp only [prescribedReactiveImplementation, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply pmf_eq_pure_of_support_subset_singleton
  intro action supported
  obtain ⟨intentions, memorySupported, actionSupported⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨remembered, member, named⟩ :=
    runtime.prescribedReactivePosterior_recorded_ready_coverage leaks who policy history consistent
      quiet sent entry retained event earlierTurn identity ready owned intentions memorySupported
  have recorded := runtime.prescribedReactivePosterior_recorded leaks who policy consistent
    quiet sent intentions memorySupported remembered member
  rw [named] at recorded
  have blocked : runtime.prescribedReactiveResponse leaks who policy history intentions view =
      PMF.pure (⟨none⟩, none) := by
    rcases recorded with submitted | decided
    · simp only [prescribedReactiveResponse, turn, submitted, Bool.true_or, ↓reduceIte]
    · simp only [prescribedReactiveResponse, turn, decided, Bool.or_true, ↓reduceIte]
  rw [blocked, PMF.pure_map] at actionSupported
  exact (PMF.mem_support_pure_iff _ _).mp actionSupported

end Vegas.EventGraphRuntime
