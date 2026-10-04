/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRecordedDecisionCompletion
import Vegas.Game.SourceServiceAlignedConstructors
import Vegas.Game.SourceServiceReadyObservation
import Interaction.ReactiveRecovery

/-! # The actual source draw of a recalled resolution response

An owner following the turn-counted policy has consistent actual recall, even
with arbitrary foreign policies. A recalled transmitted response therefore
came from a supported compiler choice at its original input. While its event
is still ready, the full typed source observation is unchanged. An aligned
residual disclosure identifies that draw with its actual source kernel.

This retains earlier silent deferrals and does not assume source-draw support,
an original execution witness, or equality of network observations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem recalled_response_supported
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (count : Nat) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (before after : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (split : execution.recall owner = before ++ entry :: after) :
    entry.action ∈ (players owner before entry.beforeView).support := by
  let app := application setup leaks
  have selfRecover : (players owner).recover (players owner) = players owner := by
    funext past view
    unfold ReactiveApplication.Policy.recover
    split <;> rfl
  have invariant := (players owner).recover_invariant (players owner) owner players selfRecover.symm
  obtain ⟨initial, _, rounds⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have consistent := invariant.runRounds scheduler count (.initial app initial) execution
    ReactiveApplication.Policy.Consistent.nil rounds
  rw [split, show before ++ entry :: after = (before ++ [entry]) ++ after by simp] at consistent
  exact ((players owner).consistent_snoc_iff before entry).mp consistent.of_append |>.2

private theorem submitted_compiled_choice
    {bound : (graph setup).EventId → Nat} {turns : Nat} {timing : TurnTiming setup turns}
    {profile : BehavioralProfile setup.program} {owner : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (chosen : response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile owner
      past view).support)
    {material : (application setup leaks).Submission}
    (transmission : response.transmission = some material)
    {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? owner = some event)
    (identity : view.application.who = owner)
    (owned : (graph setup).actor? event = some owner) :
    ∃ action ∈ ((compileEventProfile setup.program profile) owner event owned
        (setup.eventGraph.fromModeObservation .sequential owner
          (identity ▸ view.application.observation))).support,
      response = (runtime setup).canonicalServiceDecision leaks owner past view event action := by
  let app := application setup leaks
  unfold sourceServiceTurnPolicy at chosen
  simp only [turn, dite_eq_left owned] at chosen
  rw [app.policyMixture_policy, PMF.support_bind] at chosen
  obtain ⟨slot, _, member⟩ := Set.mem_iUnion₂.mp chosen
  unfold sourceServiceTurnFamily ReactiveApplication.turnScheduledPolicy at member
  dsimp only at member
  split at member
  · unfold sourceServiceCanonicalOpportunity at member
    split at member
    · exact (silentPolicy_not_submit member material transmission).elim
    · split at member
      · rw [PMF.support_bind] at member
        obtain ⟨decision, sampled, selected⟩ := Set.mem_iUnion₂.mp member
        split at selected
        · exact (silentPolicy_not_submit selected material transmission).elim
        · rw [PMF.mem_support_pure_iff] at selected
          subst selected
          unfold sourceServiceCanonicalPolicy at sampled
          simp only [dite_eq_left identity, turn, dite_eq_left owned, PMF.support_map] at sampled
          obtain ⟨action, supported, equal⟩ := sampled
          exact ⟨action, supported, equal.symm⟩
      · exact (silentPolicy_not_submit member material transmission).elim
  · exact (silentPolicy_not_submit member material transmission).elim

private theorem revealSource_compiled_choice
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config) :
    ((compileEventProfile setup.program profile) site.owner event site.owned
        (setup.eventGraph.fromModeObservation .sequential site.owner
          ((graph setup).playerObserve site.owner execution.application.config))) =
      (revealKernel site.residual (site.source.view site.owner)).map
        (fun disclose => cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
          disclose) := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _, _⟩ := site
  dsimp only at *
  subst head
  let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  let observation := setup.eventGraph.fromModeObservation .sequential owner
    ((graph setup).playerObserve owner execution.application.config)
  have actor : (graph setup).actor? (embedding.event index) = some owner := by
    change (toEventGraph setup.program).actor? (embedding.event index) = some owner
    simpa [index, eventOwner?, eventCount] using aligned.actorEq index
  have law := aligned.policyEq owner index actor observation
  have ownHistory : decodeCompletions setup.program observation.ownActions =
      source.history owner := by
    change decodeCompletions setup.program
      (((graph setup).ownCompletions owner execution.application.config.history).map
        (setup.eventGraph.fromModeCompletion .sequential)) = _
    rw [ownCompletions_from_sequential]
    exact congrFun history owner
  rw [ownHistory] at law
  have decoded := decodeObservation?_playerStore_eq_some (graph := graph setup)
    refs owner source.state execution.application.config.store agree
  change _ = compilePolicyTable
    (.reveal published owner name fresh binding unresolved next)
    refs embedding.ref owner (residual owner) index
      ((graph setup).playerStore owner execution.application.config.store)
      (source.history owner) at law
  rw [compilePolicyTable_reveal_of_decode refs embedding.ref
    (residual owner) rfl _ _ (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq index)) _ _ law
  simpa [index, eventCount, outputLayout, revealKernel, Config.view, observation] using actionLaw

/-- A recalled transmitted source response is a supported compiler action at
the current ready event's full typed observation. Earlier waits and arbitrary
foreign policies are retained. -/
theorem sourceServiceTurnPolicy_recalled_compiled_choice {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (follows : players owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall owner)
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (material : (application setup leaks).Submission)
    (transmission : entry.action.transmission = some material) :
    ∃ action ∈ ((compileEventProfile setup.program profile) owner event owned
        (setup.eventGraph.fromModeObservation .sequential owner
          ((graph setup).playerObserve owner execution.application.config))).support,
      ∃ before after, execution.recall owner = before ++ entry :: after ∧
        entry.action = (runtime setup).canonicalServiceDecision leaks owner before
          entry.beforeView event action := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    count within execution reached
  have atTurn := (canonicalSlots_roundsFrom scheduler players owner timing profile follows
    count execution reached).1
  have earlier := atTurn entry member event named
  have current := ownTurn?_of_ready setup execution.application ready owned
  have identity := (recalled_ownTurn_observation setup leaks trace owner entry member event
    earlier current).1
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have chosen := recalled_response_supported scheduler players owner count execution reached
    before after entry split
  rw [follows] at chosen
  obtain ⟨action, sampled, response⟩ := submitted_compiled_choice chosen transmission earlier
    identity owned
  rw [recalled_ownTurn_compiled_choice setup leaks trace profile owner entry member event
    earlier current identity owned] at sampled
  exact ⟨action, sampled, before, after, split, response⟩

/-- The original transmitted resolution response was drawn from the current
aligned residual source kernel. Only the owner's physical policy is prescribed. -/
theorem sourceServiceTurnPolicy_recalled_resolution_choice {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId)
    (site : RevealSource setup profile event execution.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (ready : execution.application.config.cut.Ready event)
    (entry : (application setup leaks).PlayerEntry) (member : entry ∈ execution.recall site.owner)
    (named : (runtime setup).submittedEvent? leaks entry.action = some event)
    (material : (application setup leaks).Submission)
    (transmission : entry.action.transmission = some material) :
    ∃ disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support,
      ∃ before after, execution.recall site.owner = before ++ entry :: after ∧
        entry.action = (runtime setup).canonicalServiceDecision leaks site.owner before
          entry.beforeView event
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) := by
  obtain ⟨action, sampled, before, after, split, response⟩ :=
    sourceServiceTurnPolicy_recalled_compiled_choice timing profile players site.owner follows
      count within execution reached event site.owned ready entry member named material transmission
  rw [revealSource_compiled_choice execution site, PMF.support_map] at sampled
  obtain ⟨disclose, supported, rfl⟩ := sampled
  exact ⟨disclose, supported, before, after, split, response⟩

end Vegas
