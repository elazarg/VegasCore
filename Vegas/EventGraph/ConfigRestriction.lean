/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.StateCongruence
import Vegas.EventGraph.CompletedOutputAgreement

/-! # Own recall prefixes and recorded outputs

The physical completed cut retains exactly an ordered own-recall prefix
(`Vegas.EventGraph.Config.ownCompletions_filter_eq_of_prefix`), and every
recorded action of a reachable configuration keeps its supported evaluator
output in the final store
(`Vegas.EventGraph.Config.Reachable.history_output_semantics`).
-/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
namespace Config

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

end Config
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
