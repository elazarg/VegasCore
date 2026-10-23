/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.StateCongruence
import Vegas.EventGraph.CompletedOutputAgreement

/-! # Reachable configurations restricted to predecessor-closed cuts -/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
namespace Config

/-- Retain the portion of an existing configuration in a predecessor-closed cut. -/
def restrict (config : graph.Config) (retained : graph.order.Cut) : graph.Config where
  inputs := config.inputs
  cut := ⟨config.cut.completed ∩ retained.completed, by
    intro event member predecessor dependency
    exact Finset.mem_inter.mpr
      ⟨config.cut.predecessor_closed (Finset.mem_inter.mp member).1 dependency,
        retained.predecessor_closed (Finset.mem_inter.mp member).2 dependency⟩⟩
  outputs := fun event => if event ∈ retained.completed then config.outputs event else none
  output_available := by
    intro event
    by_cases member : event ∈ retained.completed
    · simp only [member, ↓reduceIte, config.output_available, Finset.mem_inter, and_true]
    · simp only [member, ↓reduceIte, Option.isSome_none, Finset.mem_inter, and_false,
        Bool.false_eq_true]
  history := config.history.filter (fun completion => completion.event ∈ retained.completed)
  history_nodup := config.history_nodup.sublist (List.filter_sublist.map _)
  history_exact := by
    intro event
    constructor
    · intro member
      obtain ⟨completion, present, rfl⟩ := List.mem_map.mp member
      obtain ⟨recorded, retained⟩ := List.mem_filter.mp present
      exact Finset.mem_inter.mpr
        ⟨(config.history_exact _).mp (List.mem_map.mpr ⟨completion, recorded, rfl⟩),
          of_decide_eq_true retained⟩
    · intro member
      obtain ⟨completed, retained⟩ := Finset.mem_inter.mp member
      obtain ⟨completion, recorded, named⟩ :=
        List.mem_map.mp ((config.history_exact _).mpr completed)
      exact List.mem_map.mpr ⟨completion, List.mem_filter.mpr
        ⟨recorded, by simpa only [named, decide_eq_true_eq] using retained⟩, named⟩

/-- The structural fields determine an event configuration. -/
theorem eq_of_fields {left right : graph.Config}
    (inputs : left.inputs = right.inputs) (cut : left.cut = right.cut)
    (outputs : left.outputs = right.outputs) (history : left.history = right.history) :
    left = right := by
  cases left
  cases right
  cases inputs
  cases cut
  cases outputs
  cases history
  rfl


/-- Restricting a still-ready retained event preserves its ready read frame. -/
theorem restrict_ready (config : graph.Config) (retained : graph.order.Cut)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (member : event ∈ retained.completed) : (config.restrict retained).cut.Ready event := by
  refine ⟨fun inside => ready.1 (Finset.mem_inter.mp inside).1, ?_⟩
  intro predecessor dependency
  exact Finset.mem_inter.mpr
    ⟨ready.2 dependency, retained.predecessor_closed member dependency⟩

/-- Retaining an event retains every field read by its evaluator. -/
theorem restrict_eval (config : graph.Config) (retained : graph.order.Cut)
    (event : graph.EventId) (member : event ∈ retained.completed) (action : graph.Action event) :
    (graph.nodes event).eval? action (config.restrict retained).store =
      (graph.nodes event).eval? action config.store := by
  apply EventCode.eval?_congr
  intro field read
  cases field with
  | inl input => rfl
  | inr predecessor =>
      have kept := retained.predecessor_closed member (graph.reads_available event _ read)
      change (if predecessor ∈ retained.completed then config.outputs predecessor else none) = _
      simp only [kept, ↓reduceIte]
      rfl

/-- Completing a retained event commutes with cut restriction. -/
theorem restrict_complete_of_mem (config : graph.Config) (retained : graph.order.Cut)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (member : event ∈ retained.completed) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.complete event ready action value).restrict retained =
      (config.restrict retained).complete event (config.restrict_ready retained event ready member)
        action value := by
  apply eq_of_fields
  · rfl
  · apply EventOrder.Cut.ext
    ext query
    simp only [restrict, complete, EventOrder.Cut.mem_complete, Finset.mem_inter]
    by_cases same : query = event
    · subst query
      simp only [member, true_or, true_and]
    · simp only [same, false_or]
  · funext query
    by_cases same : query = event
    · subst query
      simp only [restrict, complete, Function.update_self, member, ↓reduceIte]
    · simp only [restrict, complete, Function.update_of_ne same]
  · simp only [restrict, complete, List.filter_append, List.filter_cons, member,
      decide_true, ↓reduceIte, List.filter_nil]

/-- Skipping an event outside the retained cut leaves its projection unchanged. -/
theorem restrict_complete_of_not_mem (config : graph.Config) (retained : graph.order.Cut)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (member : event ∉ retained.completed) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.complete event ready action value).restrict retained = config.restrict retained := by
  apply eq_of_fields
  · rfl
  · apply EventOrder.Cut.ext
    ext query
    simp only [restrict, complete, EventOrder.Cut.mem_complete, Finset.mem_inter]
    by_cases same : query = event
    · subst query
      simp only [member, and_false]
    · simp only [same, false_or]
  · funext query
    by_cases same : query = event
    · subst query
      simp only [restrict, member, ↓reduceIte]
    · simp only [restrict, complete, Function.update_of_ne same]
  · simp only [restrict, complete, List.filter_append, List.filter_cons, member,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]

/-- Any predecessor-closed restriction of a genuinely reachable configuration
is itself genuinely reachable, with the same retained supported choices. -/
theorem Reachable.restrict {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs) (retained : graph.order.Cut) :
    (config.restrict retained).Reachable inputs := by
  induction reachable with
  | initial =>
      have empty : (Config.initial inputs).restrict retained = Config.initial inputs := by
        apply eq_of_fields
        · rfl
        · apply EventOrder.Cut.ext
          change (∅ : Finset graph.EventId) ∩ retained.completed = ∅
          exact Finset.empty_inter _
        · funext event
          change (if event ∈ retained.completed then none else none) = none
          exact ite_self none
        · rfl
      rw [empty]
      exact .initial
  | @step before reachable event ready action next supported ih =>
      unfold Config.step at supported
      obtain ⟨value, selected, rfl⟩ := PMF.support_map .. ▸ supported
      by_cases member : event ∈ retained.completed
      · rw [restrict_complete_of_mem before retained event ready member action value]
        apply Reachable.step ih event (before.restrict_ready retained event ready member) action
        unfold Config.step
        simpa only [before.restrict_eval retained event member action] using
          (show
            (before.restrict retained).complete event _ action value ∈
              ((((graph.nodes event).eval? action before.store).get
                (EventCode.eval?_isSome_of_reads (graph.nodes event) action before.store
                  (fun _ read => before.read_available ready read))).map
                    ((before.restrict retained).complete event _ action)).support from by
              rw [PMF.support_map]
              exact ⟨value, selected, rfl⟩)
      · rw [restrict_complete_of_not_mem before retained event ready member action value]
        exact ih


/-- A subcut restriction has exactly the requested completed cut. -/
theorem restrict_cut_of_subset (config : graph.Config) (retained : graph.order.Cut)
    (subset : retained.completed ⊆ config.cut.completed) :
    (config.restrict retained).cut = retained := by
  apply EventOrder.Cut.ext
  exact Finset.inter_eq_right.mpr subset

/-- Restriction keeps exactly the retained original own actions, in order. -/
theorem restrict_ownCompletions [DecidableEq Player] (config : graph.Config)
    (retained : graph.order.Cut) (who : Player) :
    graph.ownCompletions who (config.restrict retained).history =
      (graph.ownCompletions who config.history).filter
        (fun completion => completion.event ∈ retained.completed) := by
  unfold ownCompletions restrict
  exact List.filter_comm _ _ _


/-- Exact retained output agreement identifies the restricted frontier's
whole partial store, including absent physical outputs. -/
theorem CompletedOutputAgreement.restrict_store (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs) :
    (frontier.restrict physical.cut).store = physical.store := by
  funext field
  cases field with
  | inl input => exact congrArg (fun values : graph.Inputs => some (values input)) inputs.symm
  | inr event =>
      by_cases completed : event ∈ physical.cut.completed
      · change (if event ∈ physical.cut.completed then frontier.outputs event else none) = _
        simp only [completed, ↓reduceIte]
        exact (agreement event completed).symm
      · have absent : physical.outputs event = none := by
          cases actual : physical.outputs event with
          | none => rfl
          | some value =>
              exact (completed ((physical.output_available event).mp
                (by simp only [actual, Option.isSome_some]))).elim
        change (if event ∈ physical.cut.completed then frontier.outputs event else none) = _
        change (if event ∈ physical.cut.completed then frontier.outputs event else none) =
          physical.outputs event
        simp only [completed, ↓reduceIte, absent]

/-- Retained outputs and all original own recalls identify the reachable
frontier restriction's full semantic state. -/
theorem CompletedOutputAgreement.restrict_semanticKey [DecidableEq Player]
    (physical frontier : graph.Config) (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (recalls : ∀ who, graph.ownCompletions who physical.history =
      (graph.ownCompletions who frontier.history).filter
        (fun completion => completion.event ∈ physical.cut.completed)) :
    graph.semanticKey (frontier.restrict physical.cut) = graph.semanticKey physical := by
  unfold semanticKey storeRecall
  apply Prod.ext
  · exact frontier.restrict_cut_of_subset physical.cut (agreement.completed_subset ..)
  · apply Prod.ext
    · exact agreement.restrict_store physical frontier inputs
    · funext who
      change graph.ownCompletions who (frontier.restrict physical.cut).history =
        graph.ownCompletions who physical.history
      rw [frontier.restrict_ownCompletions physical.cut who]
      exact (recalls who).symm


/-- An ordered original own-recall prefix is exactly the part of the frontier
own recall retained by the physical completed cut. -/
theorem ownCompletions_filter_eq_of_prefix [DecidableEq Player]
    (physical frontier : graph.Config) (who : Player)
    (prefixRecall : (graph.ownCompletions who physical.history).IsPrefix
      (graph.ownCompletions who frontier.history)) :
    (graph.ownCompletions who frontier.history).filter
      (fun completion => completion.event ∈ physical.cut.completed) =
      graph.ownCompletions who physical.history := by
  obtain ⟨tail, split⟩ := prefixRecall
  rw [← split, List.filter_append]
  have keep : (graph.ownCompletions who physical.history).filter
      (fun completion => completion.event ∈ physical.cut.completed) =
      graph.ownCompletions who physical.history := by
    apply List.filter_eq_self.mpr
    intro completion member
    have recorded := (List.mem_filter.mp member).1
    exact decide_eq_true ((physical.history_exact _).mp
      (List.mem_map.mpr ⟨completion, recorded, rfl⟩))
  have drop : tail.filter (fun completion => completion.event ∈ physical.cut.completed) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro completion member
    rw [decide_eq_true_eq]
    intro completed
    have ghostNodup : ((graph.ownCompletions who frontier.history).map
        Completion.event).Nodup :=
      frontier.history_nodup.sublist (List.filter_sublist.map _)
    rw [← split, List.map_append] at ghostNodup
    have owned : graph.actor? completion.event = some who := by
      have recalled : completion ∈ graph.ownCompletions who frontier.history := by
        rw [← split]
        exact List.mem_append_right _ member
      exact of_decide_eq_true (List.mem_filter.mp recalled).2
    obtain ⟨earlier, recorded, named⟩ := List.mem_map.mp ((physical.history_exact _).mpr completed)
    have ownEarlier : earlier ∈ graph.ownCompletions who physical.history :=
      List.mem_filter.mpr ⟨recorded, by simpa only [named, decide_eq_true_eq] using owned⟩
    exact (List.nodup_append.mp ghostNodup).2.2 completion.event
      (List.mem_map.mpr ⟨earlier, ownEarlier, named⟩) completion.event
      (List.mem_map.mpr ⟨completion, member, rfl⟩) rfl
  rw [keep, drop, List.append_nil]

/-- Actual output agreement and ordered own-recall prefixes identify the
reachable restricted frontier, without assuming a desired semantic-key law. -/
theorem CompletedOutputAgreement.restrict_semanticKey_of_prefix [DecidableEq Player]
    (physical frontier : graph.Config) (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (recalls : ∀ who, (graph.ownCompletions who physical.history).IsPrefix
      (graph.ownCompletions who frontier.history)) :
    graph.semanticKey (frontier.restrict physical.cut) = graph.semanticKey physical := by
  apply agreement.restrict_semanticKey physical frontier inputs
  intro who
  exact (ownCompletions_filter_eq_of_prefix physical frontier who (recalls who)).symm

end Config
end Vegas.EventGraph

namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

end Vegas.EventGraph

namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

private theorem stored_read_eval_step (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (action : graph.Action event)
    (supported : next ∈ (config.step event ready action).support)
    (reader : graph.EventId) (readerAction : graph.Action reader)
    (available : ∀ field ∈ (graph.nodes reader).readFields, (config.store field).isSome) :
    (graph.nodes reader).eval? readerAction next.store =
      (graph.nodes reader).eval? readerAction config.store := by
  apply EventCode.eval?_congr
  intro field member
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field member)
  exact (config.step_store_of_some next event ready action supported field value stored).trans
    stored.symm

/-- Every reachable recorded action retains its exact supported evaluator output
in the final typed store, even after later independent or dependent events. -/
theorem Config.Reachable.history_output_semantics {inputs : graph.Inputs} {config : graph.Config}
    (reachable : config.Reachable inputs) :
    ∀ completion ∈ config.history, ∃ law value,
      config.outputs completion.event = some value ∧
      (graph.nodes completion.event).eval? completion.action config.store = some law ∧
      value ∈ law.support := by
  induction reachable with
  | initial => simp [Config.initial]
  | @step config reachable event ready action next supported ih =>
      have actualSupported := supported
      rw [Config.step, PMF.support_map] at supported
      obtain ⟨output, produced, rfl⟩ := supported
      intro completion member
      change completion ∈ config.history ++ [⟨event, action⟩] at member
      rcases List.mem_append.mp member with previous | current
      · obtain ⟨law, value, stored, evaluates, positive⟩ := ih completion previous
        have completed : completion.event ∈ config.cut.completed :=
          (config.history_exact completion.event).mp (List.mem_map.mpr ⟨completion, previous, rfl⟩)
        have available : ∀ field ∈ (graph.nodes completion.event).readFields,
            (config.store field).isSome := by
          intro field read
          cases field with
          | inl input => simp
          | inr producer =>
              exact (config.output_available producer).mpr
                (config.cut.predecessor_closed completed
                  (graph.reads_available completion.event (.inr producer) read))
        refine ⟨law, value, ?_, ?_, positive⟩
        · exact config.step_store_of_some _ event ready action actualSupported
            (.inr completion.event) value stored
        · exact (stored_read_eval_step config _ event ready action actualSupported
            completion.event completion.action available).trans evaluates
      · have equal : completion = (⟨event, action⟩ : graph.Completion) :=
          List.mem_singleton.mp current
        subst completion
        let law := ((graph.nodes event).eval? action config.store).get
          (EventCode.eval?_isSome_of_reads (graph.nodes event) action config.store
            (fun _ member => config.read_available ready member))
        have evaluates : (graph.nodes event).eval? action config.store = some law :=
          (Option.some_get _).symm
        refine ⟨law, output, Config.complete_output_same _ _ _ _ _, ?_, produced⟩
        exact (stored_read_eval_step config _ event ready action actualSupported event action
          (fun _ read => config.read_available ready read)).trans evaluates

end Vegas.EventGraph

namespace Vegas.EventGraph.Config
open GameTheory.Math.Probability
variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Settling an already sampled strategic action preserves the retained sampled
output. Both outputs are derived from actual supported graph steps. -/
theorem CompletedOutputAgreement.settle_sampled_owned
    (physical frontier next : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (reachable : frontier.Reachable frontier.inputs)
    (remembered : graph.Completion) (recorded : remembered ∈ frontier.history)
    (who : Player) (actor : graph.actor? remembered.event = some who)
    (ready : physical.cut.Ready remembered.event)
    (supported : next ∈ (physical.step remembered.event ready remembered.action).support) :
    next.CompletedOutputAgreement frontier := by
  obtain ⟨law, storedValue, stored, evaluates, positive⟩ :=
    reachable.history_output_semantics remembered recorded
  obtain ⟨value, pureEval⟩ := (graph.nodes remembered.event).eval?_eq_pure_of_actor who actor
    remembered.action physical.store (fun _ read => physical.read_available ready read)
  have ghostEval := agreement.ready_eval physical frontier inputs remembered.event ready
    remembered.action
  have sameLaw : law = PMF.pure value := Option.some.inj (evaluates.symm.trans
    (ghostEval.symm.trans pureEval))
  rw [sameLaw, PMF.mem_support_pure_iff] at positive
  subst storedValue
  have stepEq := physical.step_eq_map_of_eval remembered.event ready remembered.action
    (PMF.pure value) pureEval
  rw [PMF.pure_map] at stepEq
  have nextEq : next = physical.complete remembered.event ready remembered.action value := by
    rwa [stepEq, PMF.mem_support_pure_iff] at supported
  apply agreement.physical_step physical frontier next remembered.event ready remembered.action
    supported
  rw [nextEq, complete_output_same, stored]

end Vegas.EventGraph.Config
