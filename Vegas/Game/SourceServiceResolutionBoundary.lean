/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBoundary
import Vegas.Pending.ReactiveResolutionSettlement
import Vegas.Pending.ReactiveResolutionWindowConformance
import Vegas.Pending.ReactiveServiceEvents
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveRevealResponse

/-! # Guarded disclosure boundaries for every permitted policy

The complete service block advances the original source by one effective
Boolean disclosure. Early opening and withholding share the same boundary
invariant; neither requires a chosen source strategy or a fixed opening time.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every retained guarded disclosure block has an effective original source
successor and restores the complete operational boundary. -/
theorem ServiceBoundary.reveal_block
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (beforeRefs : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ disclose : Bool, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∃ disclose, effectiveDisclosure published binding source disclose = disclose ∧
      ServiceBoundary setup leaks rosters initial
        (revealSuccessor published binding source disclose)
        (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) final := by
  let app := application setup leaks
  have ordinary : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
    fun who past view response member => sourceServiceMenu_in_compiled setup leaks bounds
      rosters who past view (lawful who past view response member)
  have sole := soleReady_of_ready setup execution.application (boundary.ready event atRank)
  have ready := boundary.ready event atRank
  have timely := boundary.timely event atRank (by simp only [owned, Option.isSome_some])
  have phase := reached
  rw [rosterBlock_of_owner setup rosters event owner owned, List.append_assoc,
    (runtime setup).runInteractionPlan_append] at phase
  obtain ⟨included, inclusion, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phase)
  have packets := bounds.compiled_resolution_inclusion_published (runtime setup) leaks
    players ordinary network owner event payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node (rosters event) execution included sole boundary.published
      boundary.serials inclusion
  obtain ⟨result, accounted⟩ := bounds.compiled_resolution_settlement (runtime setup) leaks
    players ordinary network owner event payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq node (rosters event) execution included boundary.binding ready timely
      sole boundary.published boundary.serials boundary.accounted inclusion
  obtain ⟨disclose, effective, config, candidates, accepted, sameNetwork, sameRecall⟩ :
      ∃ disclose, effectiveDisclosure published binding source disclose = disclose ∧
        final.application.config = execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)) ∧
        final.application.candidates = execution.application.candidates ∧
        final.application.accepted = execution.application.accepted ∧
        final.network = included.network ∧ final.recall = included.recall := by
    rcases result with silent | ⟨value, resolved, completed⟩
    · obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
        ((boundary.invariant.activated_iff event).mpr
          ⟨ready, by simp only [owned, Option.isSome_some]⟩)
      have due : (runtime setup).deadline event ≤
          included.application.clock + (event.val + 1) - entered := by
        rw [silent]
        have earlier := boundary.invariant.activated_le event entered activated
        change event.val + 1 ≤ execution.application.clock + (event.val + 1) - entered
        omega
      obtain ⟨after, exactTail, afterApp, afterNetwork, _, afterRecall⟩ :=
        (runtime setup).canonical_silent_expiry leaks players network included owner event payload
          (refs.get binding)
          (compileChecks (published := published) refs source.registry source.revelations binding)
          outputEq codeEq node (by rw [silent]; exact ready) entered (event.val + 1)
          (by rw [silent]; exact activated) due
      rw [exactTail] at tail
      have finalEq := (PMF.mem_support_pure_iff _ _).mp tail
      subst final
      refine ⟨false, effectiveDisclosure_false _ _ _, ?_, ?_, ?_, afterNetwork, afterRecall⟩
      · rw [afterApp]
        simp only [EventGraphRuntime.State.complete, silent, disclosureResult_false]
      · rw [afterApp]
        change included.application.candidates = execution.application.candidates
        exact congrArg EventGraphRuntime.State.candidates silent
      · rw [afterApp]
        change included.application.accepted = execution.application.accepted
        exact congrArg EventGraphRuntime.State.accepted silent
    · have sourceResult := compiled_disclosure_result published binding source refs
        execution.application.config.store boundary.agrees true
      rw [EventGraph.EventCode.resolveOutput?_playerStore, resolved] at sourceResult
      have success : disclosureResult published binding source true = .success value :=
        (Option.some.inj sourceResult).symm
      have settled : ¬included.application.config.cut.Ready event := by
        rw [completed]
        intro active
        exact active.1 (by simp [EventGraphRuntime.State.complete, EventOrder.Cut.complete])
      obtain ⟨after, exactTail, afterApp, afterNetwork, _, afterRecall⟩ :=
        (runtime setup).settled_reveal_expiry leaks players network included event settled
          (event.val + 1)
      rw [exactTail] at tail
      have finalEq := (PMF.mem_support_pure_iff _ _).mp tail
      subst final
      refine ⟨true, ?_, ?_, ?_, ?_, afterNetwork, afterRecall⟩
      · simp only [effectiveDisclosure, success]
      · rw [afterApp, completed, success]
        rfl
      · rw [afterApp, completed]
        rfl
      · rw [afterApp, completed]
        rfl
  have checkpoint := boundary.toSourceCheckpoint.reveal published binding event atRank
    ready outputEq beforeRefs disclose (decoded disclose)
  change SourceCheckpoint setup (revealSuccessor published binding source disclose)
    (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
      (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published binding source disclose))) at checkpoint
  rw [← config] at checkpoint
  obtain ⟨invariant, valid, recalled, serialRecall, serials⟩ := boundary.run_core players network
    (rosterBlock setup rosters event) final reached
  obtain ⟨clock, timely⟩ := boundary.roster_successor_timing players network event atRank final
    reached checkpoint.ordered
  let completed := execution.application.complete event ready
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (disclosureResult published binding source disclose))
  have completedConfig : final.application.config = completed.config := config
  have publicOutput : ((graph setup).outputLayout event).IsPublic := by rw [outputEq]; trivial
  refine ⟨disclose, effective, {
    toSourceCheckpoint := checkpoint
    invariant := invariant
    binding := valid
    prepared := ?_
    represented := ?_
    acceptedRecorded := ?_
    «recall» := recalled
    serialRecall := serialRecall
    published := ?_
    serials := serials
    accounted := ?_
    counts := boundary.roster_counts players network event atRank final reached
    unsent := ?_
    clock := clock
    timely := timely }⟩
  · intro who serial
    have prior := (boundary.prepared who).complete_public event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose)) publicOutput serial
    change final.application.candidates.lookup (who, .prepared serial) = .fresh ↔
      final.application.publicView.bindingCount who ≤ serial
    have count : final.application.publicView.bindingCount who =
        completed.publicView.bindingCount who := by
      unfold PublicView.bindingCount EventGraphRuntime.State.publicView
      rw [completedConfig]
    rw [candidates, count]
    exact prior
  · apply (boundary.represented.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose))).transport accepted candidates
    intro field value stored
    rw [completedConfig]
    exact stored
  · apply boundary.acceptedRecorded.complete_of_config event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose)) _ config accepted
    intro other kind
    rw [outputEq]
    intro impossible
    cases impossible
  · rw [sameNetwork]
    exact packets
  · rw [sameNetwork]
    exact accounted
  · intro observer other future
    rw [sameRecall]
    rw [(runtime setup).runInteractionPlan_append] at inclusion
    obtain ⟨visited, window, inclusion⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ inclusion)
    have includedRecall : included.recall observer = visited.recall observer := by
      have earlier := (runtime setup).runInteractionPlan_recall_prefix leaks players network
        [.includeLatest event owner] visited included inclusion observer
      have lengths := fixed_plan_response_counts setup leaks network players
        [.includeLatest event owner] (by simp) visited included inclusion observer
      apply (earlier.eq_of_length ?_).symm
      simpa only [List.filterMap_cons, instructionActor, List.filterMap_nil, List.count_nil,
        Nat.add_zero] using lengths.symm
    rw [includedRecall, (runtime setup).compiled_window_other_events leaks bounds players ordinary
      network event (rosters event) execution visited sole window observer other
        (by intro equal; subst other; omega)]
    exact boundary.unsent observer other (by omega)

/-- Every actual historical traffic record still passes the public checker
after a complete retained disclosure block. The record keeps its transmission
phase, so later inclusion does not change the test applied to earlier traffic. -/
theorem ServiceBoundary.reveal_block_conformance
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {rosters : (graph setup).EventId → List Player} {initial : State L setup.context}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (boundary : ServiceBoundary setup leaks rosters initial source refs rank execution)
    (bounds : MessageBounds (graph setup))
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (atRank : event.val = rank)
    (owner : Player) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (traffic : ∀ record ∈ (application setup leaks).executionTraffic execution,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∀ record ∈ (application setup leaks).executionTraffic final,
      (runtime setup).permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = true := by
  have sole := soleReady_of_ready setup execution.application (boundary.ready event atRank)
  have phase := reached
  rw [rosterBlock_of_owner setup rosters event owner owned] at phase
  simp only [List.append_assoc] at phase
  rw [(runtime setup).runInteractionPlan_append] at phase
  obtain ⟨visited, window, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phase)
  have ordinary : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
    fun who past view response member => sourceServiceMenu_in_compiled setup leaks bounds
      rosters who past view (lawful who past view response member)
  obtain ⟨_, visitedTraffic, _⟩ := bounds.compiled_resolution_window_conformance
    (runtime setup) leaks players ordinary network (rosters event) owner event payload binding
      checks outputEq codeEq node execution visited boundary.binding boundary.recall sole
      (boundary.ready event atRank)
      (boundary.timely event atRank (by simp only [owned, Option.isSome_some]))
      (fun _ => boundary.accounted owner)
      ((runtime setup).service_published_conformance leaks execution boundary.published)
      traffic window
  have exactTraffic := (runtime setup).executionTraffic_passive_plan leaks players network
    ([.includeLatest event owner] ++ List.replicate (event.val + 1) .tick ++ [.expire event])
    (by
      intro instruction member
      simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at member
      rcases member with (rfl | ⟨_, rfl⟩) | rfl <;> simp)
    visited final (by simpa only [List.append_assoc] using tail)
  rw [exactTraffic]
  exact visitedTraffic

end Vegas
