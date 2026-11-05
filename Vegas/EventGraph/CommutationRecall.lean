/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Commutation
import Vegas.EventGraph.Information

/-! # Commutation of ready events with different actors

Completing an event can make only its own actor default. Two distinct ready
events whose actors differ therefore leave each other's effective action and
recorded decision unchanged, and fixed actions at them commute after projecting
a configuration to its typed store and the completion recorded for each event.
The order of the two completions, and of their defaults, remains observable and
is not part of the projection.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Two events whose actors differ; ownerless events differ from every event. -/
def ActorsDiffer (graph : Vegas.EventGraph Player L) (left right : graph.EventId) : Prop :=
  ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who

omit [DecidableEq Player] in
theorem ActorsDiffer.symm {left right : graph.EventId} (differ : graph.ActorsDiffer left right) :
    graph.ActorsDiffer right left :=
  fun who rightActor leftActor => differ who leftActor rightActor

/-- The default recorded by a completion, if any, belongs to the completed event's actor. -/
theorem completion_defaultEvent_actor (config : graph.Config) (event : graph.EventId)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) (who : Player)
    (recorded : (EventGraph.completion graph event (config.actualDecision event action)
      value).defaultEvent = some who) :
    graph.actor? event = some who := by
  simp only [EventGraph.completion, Option.bind_eq_some_iff] at recorded
  obtain ⟨_, _, recorded⟩ := recorded
  unfold EventCode.defaultEvent at recorded
  split at recorded
  · exact recorded
  · exact absurd recorded (by simp)

/-- Completing an event changes no default of a player other than its actor. -/
theorem mem_defaulted_complete_of_actor_ne (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) (who : Player)
    (notActor : graph.actor? event ≠ some who) :
    who ∈ (config.complete event ready action value).defaulted ↔ who ∈ config.defaulted := by
  change who ∈ (config.complete event ready action value).defaults.defaulted ↔
    who ∈ config.defaults.defaulted
  rw [Config.complete_defaults]
  cases recorded : (EventGraph.completion graph event (config.actualDecision event action)
      value).defaultEvent with
  | none => rw [DefaultHistory.defaulted_record_none]
  | some owner =>
      rw [DefaultHistory.defaulted_record_some, Finset.mem_insert]
      have owned := completion_defaultEvent_actor config event action value owner recorded
      constructor
      · rintro (same | previous)
        · subst who
          exact absurd owned notActor
        · exact previous
      · exact Or.inr

/-- The effective action of an event is unchanged when an event of another actor completes. -/
theorem effectiveAction_complete_of_actorsDiffer (config : graph.Config)
    {completed other : graph.EventId} (ready : config.cut.Ready completed)
    (differ : graph.ActorsDiffer completed other)
    (action : graph.Action completed) (value : (graph.outputLayout completed).Value)
    (requested : graph.Action other) :
    (config.complete completed ready action value).effectiveAction other requested =
      config.effectiveAction other requested := by
  unfold Config.effectiveAction EventCode.effectiveAction
  split
  · next owner owned =>
      have member := mem_defaulted_complete_of_actor_ne config completed ready action value
        owner (fun completedActor => differ owner completedActor owned)
      by_cases inactive : owner ∈ config.defaulted
      · rw [ite_eq_left (member.mpr inactive), ite_eq_left inactive]
      · rw [ite_eq_right (fun active => inactive (member.mp active)), ite_eq_right inactive]
  · rfl

/-- The recorded decision of an event is unchanged when an event of another actor completes. -/
theorem actualDecision_complete_of_actorsDiffer (config : graph.Config)
    {completed other : graph.EventId} (ready : config.cut.Ready completed)
    (differ : graph.ActorsDiffer completed other)
    (action : graph.Action completed) (value : (graph.outputLayout completed).Value)
    (requested : graph.Action other) :
    (config.complete completed ready action value).actualDecision other requested =
      config.actualDecision other requested := by
  unfold Config.actualDecision EventCode.actualDecision
  split
  · next owner owned =>
      have member := mem_defaulted_complete_of_actor_ne config completed ready action value
        owner (fun completedActor => differ owner completedActor owned)
      by_cases inactive : owner ∈ config.defaulted
      · rw [ite_eq_left (member.mpr inactive), ite_eq_left inactive]
      · rw [ite_eq_right (fun active => inactive (member.mp active)), ite_eq_right inactive]
  · rfl

/-- The completion recorded for an event, if it has completed. Unlike the
chronological history, this record does not depend on completion order. -/
def completionOf (config : graph.Config) (event : graph.EventId) : Option graph.Completion :=
  config.history.find? fun completion => completion.event = event

/-- The configuration projection kept by commutation: the typed store and the
completion recorded for each event. Defaults and every player's own completions
are read from these records; completion order is not. -/
def storeRecall (graph : Vegas.EventGraph Player L) (config : graph.Config) :=
  (config.store, completionOf config)

private def outputLaw (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    PMF (graph.outputLayout event).Value :=
  ((graph.nodes event).eval? (config.effectiveAction event action) config.store).get
    (EventCode.eval?_isSome_of_reads (graph.nodes event)
      (config.effectiveAction event action) config.store
      (fun _ read => config.read_available ready read))

private theorem step_eq_outputLaw_map (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    config.step event ready action =
      (outputLaw config event ready action).map (config.complete event ready action) := rfl

private theorem outputLaw_after_complete {config : graph.Config}
    {completed reader : graph.EventId} (completedReady : config.cut.Ready completed)
    (readerReady : config.cut.Ready reader) (different : completed ≠ reader)
    (differ : graph.ActorsDiffer completed reader)
    (completedAction : graph.Action completed)
    (value : (graph.outputLayout completed).Value) (readerAction : graph.Action reader) :
    outputLaw (config.complete completed completedReady completedAction value) reader
        (readerReady.after_complete completedReady different.symm) readerAction =
      outputLaw config reader readerReady readerAction := by
  have effective := effectiveAction_complete_of_actorsDiffer config completedReady differ
    completedAction value readerAction
  have evalEq := eval?_after_complete completedReady readerReady completedAction value
    (config.effectiveAction reader readerAction)
  rw [← effective] at evalEq
  have present := EventCode.eval?_isSome_of_reads (graph.nodes reader)
    ((config.complete completed completedReady completedAction value).effectiveAction
      reader readerAction)
    (config.complete completed completedReady completedAction value).store
    (fun _ read => (config.complete completed completedReady completedAction value).read_available
      (readerReady.after_complete completedReady different.symm) read)
  cases hleft : (graph.nodes reader).eval?
      ((config.complete completed completedReady completedAction value).effectiveAction
        reader readerAction)
      (config.complete completed completedReady completedAction value).store with
  | none => simp [hleft] at present
  | some law =>
      rw [hleft, effective] at evalEq
      have hright : (graph.nodes reader).eval? (config.effectiveAction reader readerAction)
          config.store = some law := evalEq.symm
      simp only [outputLaw, hleft, hright, Option.get_some]

/-- Completing two ready events of different actors records each completion as
it would have been recorded first. -/
theorem complete_complete_history (config : graph.Config) {first second : graph.EventId}
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (differ : graph.ActorsDiffer first second)
    (firstAction : graph.Action first) (firstValue : (graph.outputLayout first).Value)
    (secondAction : graph.Action second) (secondValue : (graph.outputLayout second).Value) :
    ((config.complete first firstReady firstAction firstValue).complete second
        (secondReady.after_complete firstReady different.symm) secondAction secondValue).history =
      config.history ++
        [EventGraph.completion graph first (config.actualDecision first firstAction) firstValue,
          EventGraph.completion graph second (config.actualDecision second secondAction)
            secondValue] := by
  rw [Config.complete_history, Config.complete_history,
    actualDecision_complete_of_actorsDiffer config firstReady differ firstAction firstValue]
  simp

omit [DecidableEq Player] in
/-- Swapping two adjacent completions of distinct events keeps every event's record. -/
theorem find?_swap (history : List graph.Completion) (left right : graph.Completion)
    (different : left.event ≠ right.event) (event : graph.EventId) :
    (history ++ [left, right]).find? (fun completion => completion.event = event) =
      (history ++ [right, left]).find? (fun completion => completion.event = event) := by
  simp only [List.find?_append, List.find?_cons, List.find?_nil]
  cases history.find? (fun completion => completion.event = event) with
  | some found => rfl
  | none =>
      by_cases leftHit : left.event = event
      · have rightMiss : ¬ right.event = event := fun rightHit =>
          different (leftHit.trans rightHit.symm)
        simp [leftHit, rightMiss]
      · by_cases rightHit : right.event = event <;> simp [leftHit, rightHit]

/-- The projection after completing two ready events of different actors does
not depend on their order. -/
theorem storeRecall_complete_comm (config : graph.Config) {left right : graph.EventId}
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (differ : graph.ActorsDiffer left right)
    (leftAction : graph.Action left) (rightAction : graph.Action right)
    (leftValue : (graph.outputLayout left).Value)
    (rightValue : (graph.outputLayout right).Value) :
    graph.storeRecall ((config.complete left leftReady leftAction leftValue).complete right
      (rightReady.after_complete leftReady different.symm) rightAction rightValue) =
    graph.storeRecall ((config.complete right rightReady rightAction rightValue).complete left
      (leftReady.after_complete rightReady different) leftAction leftValue) := by
  have leftFirst := complete_complete_history config leftReady rightReady different differ
    leftAction leftValue rightAction rightValue
  have rightFirst := complete_complete_history config rightReady leftReady different.symm
    differ.symm rightAction rightValue leftAction leftValue
  refine Prod.ext (store_complete_comm leftReady rightReady different leftAction rightAction
    leftValue rightValue) ?_
  funext event
  change List.find? _ _ = List.find? _ _
  rw [leftFirst, rightFirst]
  exact find?_swap config.history _ _ different event

/-- Two fixed steps as a bind over the first event's output law. -/
private theorem stepThen_map (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (differ : graph.ActorsDiffer first second)
    (firstAction : graph.Action first) (secondAction : graph.Action second)
    {β : Type} (observe : graph.Config → β) :
    (stepThen config first second firstReady secondReady different
      firstAction secondAction).map observe =
    (outputLaw config first firstReady firstAction).bind fun firstValue =>
      (outputLaw config second secondReady secondAction).map fun secondValue =>
        observe ((config.complete first firstReady firstAction firstValue).complete second
          (secondReady.after_complete firstReady different.symm)
          secondAction secondValue) := by
  classical
  unfold stepThen
  rw [map_bindOnSupport]
  rw [bindOnSupport_eq_bind_of_eq_on_support _ (g := fun (afterFirst : graph.Config) =>
    if ready : afterFirst.cut.Ready second then
      (afterFirst.step second ready secondAction).map observe
    else PMF.pure (observe afterFirst))]
  · rw [step_eq_outputLaw_map, PMF.bind_map]
    apply bind_congr_on_support _
    intro firstValue _
    have ready : (config.complete first firstReady firstAction firstValue).cut.Ready second :=
      secondReady.after_complete firstReady different.symm
    simp only [Function.comp_apply, dite_eq_left ready]
    rw [step_eq_outputLaw_map, PMF.map_comp,
      outputLaw_after_complete firstReady secondReady different differ]
    rfl
  · intro afterFirst member
    have ready : afterFirst.cut.Ready second := by
      rw [config.step_cut first firstReady firstAction afterFirst member]
      exact secondReady.after_complete firstReady different.symm
    simp only [dite_eq_left ready]

/-- **Commutation.** Fixed actions at two distinct ready events of different
actors commute after projecting to the typed store and the completion recorded
for each event. -/
theorem stepThen_map_storeRecall_comm (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (differ : graph.ActorsDiffer left right)
    (leftAction : graph.Action left) (rightAction : graph.Action right) :
    (stepThen config left right leftReady rightReady different
      leftAction rightAction).map graph.storeRecall =
    (stepThen config right left rightReady leftReady different.symm
      rightAction leftAction).map graph.storeRecall := by
  rw [stepThen_map config left right leftReady rightReady different differ,
    stepThen_map config right left rightReady leftReady different.symm differ.symm]
  simp only [← PMF.bind_pure_comp, Function.comp_def]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro rightValue _
  apply bind_congr_on_support _
  intro leftValue _
  congr 1
  exact storeRecall_complete_comm config leftReady rightReady different differ leftAction
    rightAction leftValue rightValue

end Vegas.EventGraph
