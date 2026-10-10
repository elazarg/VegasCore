/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveIntentionRecall

/-! # Authentication of retained intentions from initialized posterior support -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A sampled intention is issued only before either a transmitted or a
remembered silent decision has already recorded its event. -/
theorem prescribedReactiveResponse_some_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support) :
    runtime.reactiveAlreadySubmitted leaks history remembered.event = false ∧
      runtime.reactiveAlreadyDecided leaks who history intentions remembered.event = false ∧
      action = runtime.reactiveDecision leaks who remembered.event remembered.action
        view.application := by
  unfold prescribedReactiveResponse at supported
  split at supported
  · simp at supported
  · split at supported
    · simp at supported
    · rename_i fresh
      split at supported
      · split at supported
        · split at supported
          · obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ supported
            have responseEq := congrArg Prod.fst image
            have intentionEq := Option.some.inj (congrArg Prod.snd image)
            dsimp only at responseEq intentionEq
            subst remembered
            refine ⟨?_, ?_, responseEq.symm⟩
            · cases sent : runtime.reactiveAlreadySubmitted leaks history _ <;>
                simp_all only [Bool.true_or, not_true_eq_false]
            · cases decided : runtime.reactiveAlreadyDecided leaks who history intentions _ <;>
                simp_all only [Bool.or_true, not_true_eq_false]
          · simp at supported
        · simp at supported
      · simp at supported

/-- Every retained silent intention in an initialized supported posterior is
authenticated by the actual recorded response, provided silent responses have
their operationally correct empty emission. -/
theorem prescribedReactivePosterior_silent_alignment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (faithful : ∀ entry ∈ history, entry.action.transmission = none → entry.emitted = none)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ entry remembered, (entry, some remembered) ∈ history.zip intentions →
      entry.action.transmission = none →
      runtime.ReactiveSilentDecision leaks who entry remembered := by
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
      intro entry remembered retained silent
      rw [memoryEq, List.zip_append aligned] at retained
      rcases List.mem_append.mp retained with earlier | current
      · exact ih (fun old member => faithful old (List.mem_append_left _ member))
          previous prior entry remembered earlier silent
      · have same : entry = latest ∧ some remembered = saved := by
          simpa only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton,
            Prod.mk.injEq] using current
        obtain ⟨rfl, rfl⟩ := same
        apply runtime.reactiveSilentDecision_of_prescribed_support leaks who policy history
          previous entry.beforeView entry.action remembered produced silent entry
        cases entry
        simp only [ReactiveApplication.PlayerEntry.mk.injEq, true_and]
        exact faithful _ (List.mem_append_right _ (by simp)) silent

end Vegas.EventGraphRuntime

namespace Interaction.ReactiveApplication

variable {Player : Type} [DecidableEq Player] (app : ReactiveApplication Player)

/-- Empty emission for a silent response is an invariant of actual executions,
independently of the policy, scheduler, and environment commands. -/
theorem silentEmission_invariant (players : Player → app.Policy) (who : Player) :
    app.PolicyInvariant players (fun execution =>
      ∀ entry ∈ execution.recall who,
        entry.action.transmission = none → entry.emitted = none) where
  respond execution actor action faithful _ := by
    by_cases same : who = actor
    · subst actor
      cases action with
      | mk transmission =>
          cases transmission with
          | none =>
              simp only [Execution.respond, ↓reduceIte]
              intro entry member silent
              rcases List.mem_append.mp member with old | latest
              · exact faithful entry old silent
              · have same := List.mem_singleton.mp latest
                subst entry
                rfl
          | some material =>
              simp only [Execution.respond, ↓reduceIte]
              intro entry member silent
              rcases List.mem_append.mp member with old | latest
              · exact faithful entry old silent
              · have same := List.mem_singleton.mp latest
                subst entry
                cases silent
    · rw [app.respond_recall_other execution actor who same action]
      exact faithful
  environment execution next command faithful reached := by
    rw [app.environmentStep_recall execution next command reached]
    exact faithful

end Interaction.ReactiveApplication

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Silent intention authentication holds at every supported finite execution
from initialized private memory, while opponents and the scheduler are arbitrary. -/
theorem prescribedReactivePosterior_silent_alignment_run
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
    ∀ entry remembered, (entry, some remembered) ∈ (execution.recall who).zip intentions →
      entry.action.transmission = none →
      runtime.ReactiveSilentDecision leaks who entry remembered := by
  have consistent :=
    ((runtime.prescribedReactivePolicy leaks who policy).recover_invariant recovery who
      players focal).runRounds scheduler count
        (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
        execution (.nil) reached
  have faithful :=
    ((runtime.reactiveApplication leaks).silentEmission_invariant players who).runRounds
      scheduler count
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state)
      execution (by simp [ReactiveApplication.Execution.initial]) reached
  exact runtime.prescribedReactivePosterior_silent_alignment leaks who policy consistent
    faithful intentions supported

end Vegas.EventGraphRuntime
