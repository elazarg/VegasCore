/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePosteriorAlignment

/-! # Recorded decisions in supported initialized private memory -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every retained sampled intention is already recorded by either its emitted
event call or its authenticated silent decision. -/
theorem prescribedReactivePosterior_recorded (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (silentFaithful : ∀ entry ∈ history,
      entry.action.transmission = none → entry.emitted = none)
    (sentFaithful : ∀ entry ∈ history, ∀ material,
      entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧
        message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ remembered, some remembered ∈ intentions →
      runtime.reactiveAlreadySubmitted leaks history remembered.event = true ∨
        runtime.reactiveAlreadyDecided leaks who history intentions remembered.event = true := by
  induction consistent generalizing intentions with
  | nil =>
      have empty : intentions = [] := (PMF.mem_support_pure_iff _ _).mp supported
      simp [empty]
  | @snoc history entry consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history entry
          positive intentions supported
      have aligned : history.length = previous.length :=
        (runtime.prescribedReactivePosterior_length leaks who policy consistent previous prior).symm
      intro remembered member
      rw [memoryEq] at member ⊢
      rcases List.mem_append.mp member with earlier | current
      · rcases ih (fun old mem => silentFaithful old (List.mem_append_left _ mem))
          (fun old mem => sentFaithful old (List.mem_append_left _ mem)) previous prior
          remembered earlier with submitted | decided
        · left
          simp only [reactiveAlreadySubmitted, List.any_append] at submitted ⊢
          simp only [submitted, Bool.true_or]
        · right
          exact runtime.reactiveAlreadyDecided_append leaks who history [entry] previous [saved]
            remembered.event aligned decided
      · have savedEq : some remembered = saved := List.mem_singleton.mp current
        subst saved
        cases transmitted : entry.action.transmission with
        | none =>
            right
            have emitted := silentFaithful entry (List.mem_append_right _ (by simp)) transmitted
            have authentic := runtime.reactiveSilentDecision_of_prescribed_support leaks who policy
              history previous entry.beforeView entry.action remembered produced transmitted
              entry (by cases entry; simp_all)
            apply runtime.reactiveAlreadyDecided_of_mem leaks who _ _ entry remembered
            · rw [List.zip_append aligned]
              exact List.mem_append_right _ (by simp)
            · exact authentic
        | some material =>
            left
            obtain ⟨message, emitted, packet⟩ :=
              sentFaithful entry (List.mem_append_right _ (by simp)) material transmitted
            have fresh := runtime.prescribedReactiveResponse_some_fresh leaks who policy
              history previous entry.beforeView entry.action remembered produced
            have addressed : material.call.packet.event? graph = some remembered.event := by
              rcases runtime.reactiveDecision_transmission leaks who remembered.event
                remembered.action entry.beforeView.application with quiet | ⟨sent, issued, target⟩
              · rw [← fresh.2.2, transmitted] at quiet
                cases quiet
              · rw [← fresh.2.2, transmitted] at issued
                cases Option.some.inj issued
                exact target
            simp only [reactiveAlreadySubmitted, List.any_append]
            simp only [List.any_cons, List.any_nil, emitted, Option.any_some, packet, addressed,
              decide_true, Bool.or_false, Bool.or_true]

/-- Initialization and truthful response recall prevent two sampled intentions
for one event in every supported posterior memory. -/
theorem prescribedReactivePosterior_events_nodup (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (silentFaithful : ∀ entry ∈ history,
      entry.action.transmission = none → entry.emitted = none)
    (sentFaithful : ∀ entry ∈ history, ∀ material,
      entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧
        message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    (intentions.filterMap (fun saved => saved.map Completion.event)).Nodup := by
  induction consistent generalizing intentions with
  | nil =>
      have empty : intentions = [] := (PMF.mem_support_pure_iff _ _).mp supported
      simp [empty]
  | @snoc history entry consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history entry
          positive intentions supported
      have quiet := fun old mem => silentFaithful old (List.mem_append_left _ mem)
      have sent := fun old mem => sentFaithful old (List.mem_append_left _ mem)
      have distinct := ih quiet sent previous prior
      rw [memoryEq, List.filterMap_append]
      cases saved with
      | none => simpa using distinct
      | some remembered =>
          have fresh := runtime.prescribedReactiveResponse_some_fresh leaks who policy
            history previous entry.beforeView entry.action remembered produced
          have absent : remembered.event ∉
              previous.filterMap (fun choice => choice.map Completion.event) := by
            intro member
            obtain ⟨choice, retained, image⟩ := List.mem_filterMap.mp member
            cases choice with
            | none => simp at image
            | some original =>
                have same : original.event = remembered.event := Option.some.inj image
                have blocked := runtime.prescribedReactivePosterior_recorded leaks who policy
                  consistent quiet sent previous prior original retained
                rw [same, fresh.1, fresh.2.1] at blocked
                simp at blocked
          simp only [List.filterMap_cons, Option.map_some, List.filterMap_nil]
          exact distinct.append (by simp) (by simpa using absent)

omit [DecidableEq Player] in
/-- Distinct intention slots cannot supply different actions for one event
when the retained sampled event identities are duplicate-free. -/
theorem completion_eq_of_intention_events_nodup
    (intentions : List (Option graph.Completion))
    (distinct : (intentions.filterMap (fun saved => saved.map Completion.event)).Nodup)
    (first second : graph.Completion)
    (firstMem : some first ∈ intentions) (secondMem : some second ∈ intentions)
    (sameEvent : first.event = second.event) : first = second := by
  let label (saved : Option graph.Completion) := saved.map Completion.event
  have separated : intentions.Pairwise (fun a b =>
      ∀ e, label a = some e → ∀ f, label b = some f → e ≠ f) :=
    List.pairwise_filterMap.mp distinct
  have identity : intentions.Pairwise (fun a b =>
      label a = some first.event → label b = some first.event → a = b) :=
    separated.imp fun apart ha hb => (apart first.event ha first.event hb rfl).elim
  have same : some first = some second := List.Pairwise.forall_of_forall_of_flip
    (fun _ _ _ _ => rfl) identity
    (identity.imp fun eq ha hb => (eq hb ha).symm) firstMem secondMem
    rfl (by simp only [label, Option.map_some, sameEvent])
  exact Option.some.inj same

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual response records retain exactly the transmitted event call, including
submissions that the application later rejects. -/
theorem reactiveEmission_call_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (who : Player) :
    (runtime.reactiveApplication leaks).PolicyInvariant players (fun execution =>
      ∀ entry ∈ execution.recall who, ∀ material,
        entry.action.transmission = some material →
        ∃ message, entry.emitted = some message ∧
          message.payload.call = material.call.packet) where
  respond execution actor action faithful _ := by
    by_cases same : who = actor
    · subst actor
      cases action with
      | mk transmission =>
          cases transmission with
          | none =>
              simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
              intro entry member material transmitted
              rcases List.mem_append.mp member with old | latest
              · exact faithful entry old material transmitted
              · have same := List.mem_singleton.mp latest
                subst entry
                cases transmitted
          | some sent =>
              simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
              intro entry member material transmitted
              rcases List.mem_append.mp member with old | latest
              · exact faithful entry old material transmitted
              · have same := List.mem_singleton.mp latest
                subst entry
                cases Option.some.inj transmitted
                exact ⟨_, rfl, rfl⟩
    · rw [(runtime.reactiveApplication leaks).respond_recall_other execution actor who same action]
      exact faithful
  environment execution next command faithful reached := by
    rw [(runtime.reactiveApplication leaks).environmentStep_recall execution next command reached]
    exact faithful

/-- Every supported initialized execution samples each owned event at most once
in every supported private posterior memory. Opponents and scheduler are arbitrary. -/
theorem prescribedReactivePosterior_events_nodup_run
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (recovery : (runtime.reactiveApplication leaks).Policy)
    (focal : players who =
      (runtime.prescribedReactivePolicy leaks who policy).recover recovery)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).support) :
    (intentions.filterMap (fun saved => saved.map Completion.event)).Nodup := by
  have consistent :=
    ((runtime.prescribedReactivePolicy leaks who policy).recover_invariant recovery who
      players focal).runRounds scheduler count
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
        execution (.nil) reached
  have quiet :=
    ((runtime.reactiveApplication leaks).silentEmission_invariant players who).runRounds
      scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  have sent :=
    (runtime.reactiveEmission_call_invariant leaks players who).runRounds scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  exact runtime.prescribedReactivePosterior_events_nodup leaks who policy consistent quiet sent
    intentions supported

/-- At an actual initialized execution, a retained silent sampled intention
restores the original completion from an expiry completion with the same event.
Both authentication and competing-intention exclusion follow from support. -/
theorem reactiveOriginal_silent_of_initialized_support
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (recovery : (runtime.reactiveApplication leaks).Policy)
    (focal : players who =
      (runtime.prescribedReactivePolicy leaks who policy).recover recovery)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (count : Nat)
    (state : State graph) (execution : (runtime.reactiveApplication leaks).Execution)
    (reached : execution ∈ ((runtime.reactiveApplication leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)).support)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).support)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion)
    (retained : (entry, some remembered) ∈ (execution.recall who).zip intentions)
    (silent : entry.action.transmission = none)
    (sameEvent : remembered.event = completion.event)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts
      completion = remembered := by
  have authentic := runtime.prescribedReactivePosterior_silent_alignment_run leaks who policy
    players recovery focal scheduler count state execution reached intentions supported
    entry remembered retained silent
  have distinct := runtime.prescribedReactivePosterior_events_nodup_run leaks who policy
    players recovery focal scheduler count state execution reached intentions supported
  apply runtime.reactiveOriginal_silent_of_unique_memory leaks who (execution.recall who)
    intentions execution.receipts entry remembered completion retained authentic sameEvent
    _ resolution
  intro other member saved equal event
  subst other
  exact completion_eq_of_intention_events_nodup intentions distinct saved remembered member
    (List.of_mem_zip retained).2 (event.trans sameEvent.symm)

end Vegas.EventGraphRuntime
