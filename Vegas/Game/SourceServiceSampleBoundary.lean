/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServiceSettlement
import Vegas.Pending.ReactiveServiceEvents
import Vegas.Pending.ReactiveSilentSettlement

/-! # Public chance boundaries under every permitted roster

All participants retain their actual passive observations and silent
opportunities during a chance phase. The real sample command then
chooses an original source value, and the complete settlement restores the
dynamic operational boundary. No strategic source policy is selected.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A chance-event roster preserves the application and published network
accounting, even when there are no players or no listed opportunities. -/
theorem sourceService_sample_window
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId)
    (chance : (graph setup).actor? event = none)
    (initial final : (application setup leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (visits : List Player)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
      final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
      final.network.Satisfies
        (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := application setup leaks
  cases visits with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl, rfl, rfl, published⟩
  | cons first rest =>
      have transport : ∀ (current : app.Execution) who response,
          current.application = initial.application → initial.recall first ⊆ current.recall first →
          response ∈ (players who (current.recall who) (current.observe app who)).support →
          response = ⟨none⟩ := by
        intro current who response same _ chosen
        have silenced := bounds.compiled_foreign_transport (runtime setup) leaks who
          (current.recall who) (current.observe app who)
          (by
            change current.application.publicView.ownTurn? who = none
            rw [same]
            exact sole.ownTurn?_foreign (by rw [chance]; intro impossible; cases impossible))
          response
          (sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _
            (lawful who _ _ response chosen))
        exact app.silentPolicy_cases _ _ response silenced
      obtain ⟨application, ledger, receipts, counters, safe, _⟩ :=
        (runtime setup).silent_window_preserves leaks players network first initial transport _
          published (first :: rest) final reached
      exact ⟨application, ledger, receipts, counters, by rw [ledger]; exact safe⟩

/-- Every actual full public-chance block has a supported original source
sample and the complete next operational boundary, for arbitrary retained
player policies and observation sampling. -/
theorem ServiceBoundary.sample_block
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
    (name : VarId) (payload : L.Ty)
    (distribution : L.DistExpr (SourcePublicCtx L Γ) payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs distribution))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs distribution) outputEq codeEq)
    (chance : (graph setup).actor? event = none)
    (beforeRefs : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) execution).support) :
    ∃ value ∈ (L.evalDist distribution (sourcePublicEnv source.state)).support,
      ServiceBoundary setup leaks rosters initial (sampleSuccessor name source value)
        (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) final := by
  let app := application setup leaks
  have sole := soleReady_of_ready setup execution.application (boundary.ready event atRank)
  have phase := reached
  simp only [rosterBlock, chance, List.append_assoc] at phase
  rw [(runtime setup).runInteractionPlan_append] at phase
  obtain ⟨visited, window, phase⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phase)
  obtain ⟨sameApp, sameLedger, _, sameCounters, published⟩ := sourceService_sample_window
    setup leaks bounds rosters players lawful network event chance execution visited sole
      boundary.published (rosters event) window
  have windowCheckpoint : SourceCheckpoint setup source refs rank visited.application.config := by
    rw [sameApp]
    exact boundary.toSourceCheckpoint
  have ready : visited.application.config.cut.Ready event := by
    rw [sameApp]
    exact boundary.ready event atRank
  simp only [List.cons_append, List.nil_append, runInteractionPlan] at phase
  obtain ⟨sampled, step, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ phase)
  rw [(runtime setup).interactionStep_sample,
    source_sample_environment (runtime setup) visited.application event ready outputEq refs
      distribution codeEq node source.state windowCheckpoint.agrees, PMF.map_comp] at step
  obtain ⟨value, supported, sampledEq⟩ := PMF.support_map .. ▸ step
  let completed := visited.application.complete event ready
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
    (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
  have sampledApp : sampled.application = completed :=
    (congrArg (fun state : app.Execution => state.application) sampledEq).symm
  have sampledNetwork : sampled.network = visited.network :=
    (congrArg (fun state : app.Execution => state.network) sampledEq).symm
  have sampledRecall : sampled.recall = visited.recall :=
    (congrArg (fun state : app.Execution => state.recall) sampledEq).symm
  have checkpoint := windowCheckpoint.sample name event atRank ready outputEq
    beforeRefs decoded value
  have settled : ¬completed.config.cut.Ready event := by
    intro active
    have next := (ready_iff_rank setup _ (rank + 1) checkpoint.ordered event).mp active
    omega
  obtain ⟨after, exactTail, afterApp, afterNetwork, _, afterRecall⟩ :=
    (runtime setup).settled_reveal_expiry leaks players network sampled event
      (by rw [sampledApp]; exact settled) (event.val + 1)
  rw [exactTail] at tail
  have finalEq := (PMF.mem_support_pure_iff _ _).mp tail
  subst final
  have finalCheckpoint : SourceCheckpoint setup (sampleSuccessor name source value)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) after.application.config := by
    rw [afterApp, sampledApp]
    exact checkpoint
  obtain ⟨invariant, binding, recall, serialRecall, serials⟩ := boundary.run_core players network
    (rosterBlock setup rosters event) after reached
  obtain ⟨clock, timely⟩ := boundary.roster_successor_timing players network event atRank after
    reached finalCheckpoint.ordered
  refine ⟨value, supported, {
    toSourceCheckpoint := finalCheckpoint
    invariant := invariant
    binding := binding
    remembered := boundary.run_remembered players network
      (rosterBlock setup rosters event) after reached
    missed := by
      rw [afterApp, sampledApp]
      change visited.application.missedEvents = ∅
      rw [sameApp]
      exact boundary.missed
    prepared := ?_
    represented := ?_
    acceptedRecorded := ?_
    recall := recall
    serialRecall := serialRecall
    published := ?_
    serials := serials
    accounted := ?_
    counts := boundary.roster_counts players network event atRank after reached
    unsent := ?_
    clock := clock
    timely := timely }⟩
  · rw [afterApp, sampledApp]
    intro who
    change completed.PreparedPrefix who
    dsimp only [completed]
    apply EventGraphRuntime.State.PreparedPrefix.complete_public
    · rw [sameApp]
      exact boundary.prepared who
    · rw [outputEq]
      trivial
  · rw [afterApp, sampledApp]
    change completed.CandidatesRepresented
    dsimp only [completed]
    apply EventGraphRuntime.State.CandidatesRepresented.complete
    rw [sameApp]
    exact boundary.represented
  · rw [afterApp, sampledApp]
    change completed.AcceptedRecorded
    dsimp only [completed]
    apply EventGraphRuntime.State.AcceptedRecorded.complete
    · rw [sameApp]
      exact boundary.acceptedRecorded
    · intro owner kind
      rw [outputEq]
      intro impossible
      cases impossible
  · rw [afterNetwork, sampledNetwork]
    exact published
  · rw [afterNetwork, sampledNetwork]
    change ∀ who, visited.network.nextSerial who =
      Message.distinctAuthoredCount visited.network.ledger who
    rw [sameCounters, sameLedger]
    exact boundary.accounted
  · intro observer other future
    rw [afterRecall, sampledRecall]
    have ordinary : ∀ who past view response, response ∈ (players who past view).support →
        response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
      fun who past view response member => sourceServiceMenu_in_compiled setup leaks bounds
        rosters who past view (lawful who past view response member)
    rw [(runtime setup).compiled_window_other_events leaks bounds players ordinary network event
      (rosters event) execution visited sole window observer other
        (by intro same; subst other; omega)]
    exact boundary.unsent observer other (by omega)

end Vegas
