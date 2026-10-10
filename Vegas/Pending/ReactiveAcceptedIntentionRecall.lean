/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePosteriorUniqueness

/-! # Original accepted resolution intentions from actual supported memory -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem accepted_filterMap_head_of_unique {α β : Type} (select : α → Option β)
    (entries : List α) (value : β)
    (present : ∃ entry ∈ entries, select entry = some value)
    (unique : ∀ entry ∈ entries, ∀ selected, select entry = some selected → selected = value) :
    (entries.filterMap select).head? = some value := by
  induction entries with
  | nil => simp at present
  | cons entry rest ih =>
      cases selected : select entry with
      | some head =>
          have same := unique entry (by simp) head selected
          simp [selected, same]
      | none =>
          simp only [List.filterMap_cons, selected]
          apply ih
          · obtain ⟨witness, member, chosen⟩ := present
            rcases List.mem_cons.mp member with same | later
            · subst witness
              rw [selected] at chosen
              cases chosen
            · exact ⟨witness, later, chosen⟩
          · intro witness member head chosen
            exact unique witness (List.mem_cons_of_mem _ member) head chosen

theorem reactiveOriginal_accepted_of_unique_memory (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (receipts : List (MessageId Player × Bool))
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion)
    (retained : (entry, some remembered) ∈ history.zip intentions)
    (message : Message Player (WitnessedPacket graph))
    (emitted : entry.emitted = some message)
    (named : message.payload.call.event? graph = some completion.event)
    (accepted : (message.id, true) ∈ receipts)
    (matching : entry.action = runtime.reactiveDecision leaks who remembered.event
      remembered.action entry.beforeView.application)
    (sameEvent : remembered.event = completion.event)
    (unique : ∀ other ∈ intentions, ∀ saved, other = some saved →
      saved.event = completion.event → saved = remembered)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who history intentions receipts completion = remembered := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp [node] at resolution
  | bind => simp [node] at resolution
  | resolve =>
      let select := fun (pair : (runtime.reactiveApplication leaks).PlayerEntry ×
          Option graph.Completion) => do
        let saved ← pair.2
        if saved.event = completion.event ∧
            runtime.ReactiveSilentDecision leaks who pair.1 saved then some saved
        else do
          let message ← pair.1.emitted
          if saved.event = completion.event ∧
              message.payload.call.event? graph = some completion.event ∧
              (message.id, true) ∈ receipts ∧
              pair.1.action = runtime.reactiveDecision leaks who saved.event
                saved.action pair.1.beforeView.application then some saved
          else none
      have found : ((history.zip intentions).filterMap select).head? = some remembered := by
        apply accepted_filterMap_head_of_unique
        · exact ⟨(entry, some remembered), retained,
            by simp [select, sameEvent, emitted, named, accepted, matching]⟩
        · rintro ⟨record, saved⟩ member selected chosen
          have inMemory := (List.of_mem_zip member).2
          cases saved with
          | none => simp [select] at chosen
          | some intention =>
              simp only [select, Option.bind_eq_bind, Option.bind_some] at chosen
              split at chosen
              · rename_i validated
                have same := Option.some.inj chosen
                subst selected
                exact unique (some intention) inMemory intention rfl validated.1
              · cases emitted : record.emitted with
                | none => simp [emitted] at chosen
                | some message =>
                    simp only [emitted, Option.bind_some] at chosen
                    split at chosen
                    · rename_i accepted
                      have same := Option.some.inj chosen
                      subst selected
                      exact unique (some intention) inMemory intention rfl accepted.1
                    · cases chosen
      simp only [reactiveOriginal, node]
      change (((history.zip intentions).filterMap select).head?).getD completion = remembered
      rw [found]
      rfl

/-- Every saved intention in a supported initialized posterior is the decision
actually recorded beside it, including transmitting decisions. -/
theorem prescribedReactivePosterior_decision_alignment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ entry remembered, (entry, some remembered) ∈ history.zip intentions →
      entry.action = runtime.reactiveDecision leaks who remembered.event remembered.action
        entry.beforeView.application := by
  induction consistent generalizing intentions with
  | nil =>
      intro entry remembered retained
      simp at retained
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      have aligned : history.length = previous.length :=
        (runtime.prescribedReactivePosterior_length leaks who policy consistent previous prior).symm
      intro entry remembered retained
      rw [memoryEq, List.zip_append aligned] at retained
      rcases List.mem_append.mp retained with earlier | current
      · exact ih previous prior entry remembered earlier
      · have same : entry = latest ∧ some remembered = saved := by
          simpa only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton,
            Prod.mk.injEq] using current
        obtain ⟨rfl, rfl⟩ := same
        exact (runtime.prescribedReactiveResponse_some_fresh leaks who policy history previous
          entry.beforeView entry.action remembered produced).2.2

/-- Accepted original resolution intentions are restored at actual initialized
executions. Authentication and absence of competing intentions are derived
from the behavioral realization's supported posterior. -/
theorem reactiveOriginal_accepted_of_initialized_support
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
    (message : Message Player (WitnessedPacket graph))
    (emitted : entry.emitted = some message)
    (named : message.payload.call.event? graph = some completion.event)
    (accepted : (message.id, true) ∈ execution.receipts)
    (sameEvent : remembered.event = completion.event)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts
      completion = remembered := by
  have consistent :=
    ((runtime.prescribedReactivePolicy leaks who policy).recover_invariant recovery who
      players focal).runRounds scheduler count
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
        execution (.nil) reached
  have authentic := runtime.prescribedReactivePosterior_decision_alignment leaks who policy
    consistent intentions supported entry remembered retained
  have distinct := runtime.prescribedReactivePosterior_events_nodup_run leaks who policy
    players recovery focal scheduler count state execution reached intentions supported
  apply runtime.reactiveOriginal_accepted_of_unique_memory leaks who (execution.recall who)
    intentions execution.receipts entry remembered completion retained message emitted named
    accepted authentic sameEvent _ resolution
  intro other member saved equal event
  subst other
  exact completion_eq_of_intention_events_nodup intentions distinct saved remembered member
    (List.of_mem_zip retained).2 (event.trans sameEvent.symm)

end Vegas.EventGraphRuntime
