/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePendingFrontierReadiness
import Vegas.EventGraph.ConfigRestriction
import Vegas.EventGraph.ForeignCompletionSequence
import Vegas.Pending.ReactiveOriginalContinuation
import Vegas.Pending.ReactiveFrontier

/-! # Actual sampling at retained semantic frontiers -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- At a genuine fresh source turn, the actual original-action configuration
replays to the reachable sampled frontier using only supported foreign events. -/
theorem ReactiveFrontier.foreign_sequence (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (profile : graph.BehavioralProfile) (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner,
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (relation : runtime.ReactiveFrontier leaks execution memories frontier)
    (who : Player) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    ∃ final, graph.ForeignCompletionSequence who
        (runtime.originalConfig leaks execution memories) final ∧
      graph.semanticKey frontier = graph.semanticKey final := by
  have foreignOwners : ∀ other ∈ frontier.cut.completed,
      other ∉ execution.application.config.cut.completed →
        ∃ owner, graph.actor? other = some owner ∧ owner ≠ who := by
    intro other completed unfinished
    rcases (relation.domain other).mp completed with
      physically | ⟨owner, remembered, retained, named⟩
    · exact (unfinished physically).elim
    · have owned := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
        (consistent owner) (memories owner) (supported owner) remembered retained
      refine ⟨owner, named ▸ owned, ?_⟩
      apply runtime.pending_intention_foreign_of_fresh leaks ordered execution stable
        profile memories
        consistent supported who event ready actor fresh owner remembered retained
      intro completed
      exact unfinished (named ▸ completed)
  obtain ⟨last, sequence, same⟩ :=
    relation.reachable.foreign_factor execution.application.config.cut
    ordered who foreignOwners
  let original := runtime.originalConfig leaks execution memories
  have originalAgreement : original.CompletedOutputAgreement frontier := relation.settled
  have originalInputs : original.inputs = frontier.inputs := relation.inputs.symm
  have restrictionSame : graph.semanticKey (frontier.restrict execution.application.config.cut) =
      graph.semanticKey (runtime.originalConfig leaks execution memories) :=
    originalAgreement.restrict_semanticKey_of_prefix _ frontier originalInputs relation.recalled
  obtain ⟨final, replayed, resultSame⟩ := sequence.congr_start
    (runtime.originalConfig leaks execution memories) restrictionSame
  exact ⟨final, replayed, same.trans resultSame⟩


/-- A genuine first owner sample is harmonic for the reachable joint frontier's
canonical source continuation, despite pending foreign physical settlement. -/
theorem ReactiveFrontier.sampled_response_canonicalContinuation
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (profile : graph.BehavioralProfile) (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner,
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (frontier : graph.Config)
    (relation : runtime.ReactiveFrontier leaks execution memories frontier)
    (who : Player) (event : graph.EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (actor : graph.actor? event = some who)
    (freshMemory : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event))
    (fresh : runtime.reactiveAlreadySubmitted leaks (execution.recall who) event = false)
    (undecided : runtime.reactiveAlreadyDecided leaks who (execution.recall who)
      (memories who) event = false) :
    (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
      (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).bind
      (fun response => originalDecisionContinuation graph profile frontier response.2) =
      graph.canonicalContinuation profile frontier := by
  have physicalReady : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (execution.application.publicView.ownTurn?_spec who event turn).1
  obtain ⟨last, pending, same⟩ := ReactiveFrontier.foreign_sequence runtime leaks ordered
    execution stable profile memories consistent supported frontier relation who event
      physicalReady actor freshMemory
  have originalReady : (runtime.originalConfig leaks execution memories).cut.Ready event :=
    physicalReady
  have transported := pending.normalizePolicy_eq ordered (profile who) event originalReady actor
  have frontierReady : frontier.cut.Ready event := by
    rw [semanticKey_cut_eq same]
    exact transported.1
  have policyEqual : graph.normalizePolicy who (profile who) event actor
      (graph.playerObserve who (runtime.originalConfig leaks execution memories)) =
      graph.normalizePolicy who (profile who) event actor (graph.playerObserve who frontier) := by
    rw [← transported.2]
    apply congrArg (profile who event actor)
    exact (normalizeObservation_congr_of_semanticKey_eq same event who).symm
  rw [runtime.prescribedReactiveResponse_originalConfig leaks execution memories who
    (profile who) event turn fresh undecided actor, policyEqual, PMF.bind_map]
  have evaluate (action : graph.Action event) :
      originalDecisionContinuation graph profile frontier (some ⟨event, action⟩) =
        (frontier.step event frontierReady action).bind (graph.canonicalContinuation profile) := by
    unfold originalDecisionContinuation
    exact dite_eq_left frontierReady
  simp only [Function.comp_def, evaluate]
  rw [← PMF.bind_bind]
  have continuation := (ordered.readyIndependent profile).normalizedThenCanonical_eq
    frontier event frontierReady
  have stepEq : graph.normalizedPolicyStep profile frontier event frontierReady =
      (graph.normalizePolicy who (profile who) event actor (graph.playerObserve who frontier)).bind
        (frontier.step event frontierReady) := by
    unfold normalizedPolicyStep normalizePolicy
    split
    · rename_i owner named
      have equal : owner = who := Option.some.inj (named.symm.trans actor)
      subst owner
      rfl
    · rename_i absent
      have impossible : none = some who := absent.symm.trans actor
      cases impossible
  rw [normalizedThenCanonical, stepEq] at continuation
  exact continuation

end Vegas.EventGraphRuntime
