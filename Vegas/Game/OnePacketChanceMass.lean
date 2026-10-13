/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketReplaySteps

/-! # Chance completions and the source chance law

A chance event of the compiled graph draws from the exact source chance law,
and both the graph's completion and the source successor record the drawn
value. So at a configuration with a source residual, completing a chance event
reaches each configuration with the probability the source step gives its
decoded point, and the decoded action of a chance completion is nothing
(`Vegas.SourceResidual.chanceMass`). Hence the completion of a chance event
matches in the intended replay (`Vegas.replayStepMatches_chance`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

/-- **A chance completion has the source chance mass.** At a configuration with
a source residual, completing a chance event decodes to no action, and reaches
a configuration with the probability that the source step from the residual's
point gives its decoded point. -/
theorem SourceResidual.chanceMass {rank : Nat} {before : (graph setup).Config}
    (residual : SourceResidual setup profile rank before)
    (event : (graph setup).EventId) (ready : before.cut.Ready event)
    (action : (graph setup).Action event) (after : (graph setup).Config)
    (member : after ∈ (before.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    decodeEventAction setup.program event action = none ∧
      (((ProtocolState.step setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))
          (fun _ => none)).map some) (decodedPoint setup after)).toReal =
        ((before.step event ready action) after).toReal := by
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    admitted, effective, supports, disclosing, lift, commutes, steps, injective, transport,
    checkpoint⟩ := residual
  have atEvent := (ready_iff_rank setup before rank checkpoint.ordered event).mp ready
  have counted := aligned.graphSuffix.countEq
  change rank + eventCount program = (graph setup).order.eventCount at counted
  cases program with
  | ret payoffs =>
      have := event.isLt
      simp only [eventCount] at counted
      omega
  | @sample Γ openNames name payload fresh distribution next =>
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publicData payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .sample payload (compilePublicDist refs distribution) := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      have decoded : decodeEventAction setup.program (embedding.event index)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit) = none := by
        have lookup := aligned.actionEq index
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        simpa [index, outputEq, decodeEventAction] using lookup
      obtain ⟨marker, rfl⟩ : ∃ marker : PUnit,
          action = cast (congrArg EventGraph.EventField.Action outputEq.symm) marker :=
        ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
      cases marker
      have graphLaw := sample_step before _ ready outputEq refs distribution codeEq source.state
        checkpoint.agrees
      rw [graphLaw, PMF.support_map] at member
      obtain ⟨value, drawn, rfl⟩ := member
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      let tailRefs : ContextRefs (graphLayout setup.program)
          ((name, .publicData payload) :: Γ) := refs.cons ⟨.inr (embedding.event index), outputEq⟩
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell ref remaining
        cases ref with
        | here =>
            change (embedding.event index).val < (embedding.event remaining.succ).val
            exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
        | there ref => exact refsBefore ref remaining.succ
      have tailAligned : CompiledPolicySuffix setup.program profile next
          (afterSample residualProfile) tailRefs (sampleSuccessor name source value).revelations
          (sampleSuccessor name source value).registry tailEmbedding tailBefore (rank + 1) := by
        simpa only [sampleSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
          aligned.sampleTail setup.program profile (_openNames := names)
            fresh distribution next residualProfile refs
            source.revelations source.registry embedding refsBefore rank
      let successor : SourceResidual setup profile (rank + 1)
          (before.complete (embedding.event index) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) := {
        Γ := _, names := _, program := next, residualProfile := afterSample residualProfile,
        source := sampleSuccessor name source value, refs := tailRefs,
        embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
        admitted := fun whole who => admitted whole who,
        effective := fun whole who => effective whole who,
        supports := fun whole who => supports whole who,
        disclosing := fun whole who => disclosing whole who,
        lift := lift ∘ Sum.inr,
        commutes := fun state => by
          rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_sample_tail,
            PMF.map_comp]
        steps := fun state joint => by
          rw [Function.comp_apply, steps]
          change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
          rw [PMF.map_comp]
        injective := injective.comp Sum.inr_injective,
        transport := fun more store history => by
          rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
            decodeSourcePrefix?_sample, Option.map_map]
          rfl
        checkpoint := checkpoint.sample (native := configState before) name (embedding.event index)
          atRank ready outputEq (fun ref => refsBefore ref index) decoded value }
      refine ⟨decoded, ?_⟩
      rw [decodedPoint_eq successor, graphLaw]
      change (((ProtocolState.step setup.program (lift (Sum.inl source)) (fun _ => none)).map
          some) (some (lift (Sum.inr (ProtocolState.entry next
            (sampleSuccessor name source value)))))).toReal = _
      rw [steps]
      change ((((L.evalDist distribution (sourcePublicEnv source.state)).map fun drawn =>
          Sum.inr (ProtocolState.entry next (sampleSuccessor name source drawn))).map lift).map
            some (some (lift (Sum.inr (ProtocolState.entry next
              (sampleSuccessor name source value)))))).toReal = _
      rw [PMF.map_comp, PMF.map_comp]
      have sourceInjective : Function.Injective
          (some ∘ lift ∘ fun drawn : L.Val payload =>
            (Sum.inr (ProtocolState.entry next (sampleSuccessor name source drawn)) :
              ProtocolState (.sample name fresh distribution next))) := by
        intro first second equal
        have lifted := injective (Option.some.inj equal)
        have entries := ProtocolState.entry_injective next (Sum.inr_injective lifted)
        exact congrArg (fun config : Config Player L ((name, .publicData payload) :: Γ) =>
          config.state.get .here) entries
      have graphInjective : Function.Injective fun drawn : L.Val payload =>
          before.complete (embedding.event index) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) drawn) := by
        intro first second equal
        have outputs := congrArg (fun config : (graph setup).Config =>
          config.outputs (embedding.event index)) equal
        simp only [EventGraph.Config.complete, Function.update_self, Option.some.injEq] at outputs
        exact (cast_inj _).mp outputs
      exact congrArg ENNReal.toReal ((pmf_map_apply_of_injective _ sourceInjective value).trans
        (pmf_map_apply_of_injective _ graphInjective value).symm)
  | @commit Γ openNames name owner payload fresh guard next =>
      exfalso
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .binding owner payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) = .bind owner payload := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
      change EventGraph.EventCode.actor ((graph setup).nodes (embedding.event index)) = none
        at chance
      rw [← EventGraph.EventCode.actor_cast outputEq, codeEq] at chance
      cases chance
  | @reveal Γ openNames published owner name payload fresh selected unresolved next =>
      exfalso
      let index : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have atRank : (embedding.event index).val = rank := by
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have same : event = embedding.event index := Fin.ext (atEvent.trans atRank.symm)
      subst same
      have outputEq : (graph setup).outputLayout (embedding.event index) =
          .publication payload := by
        change outputLayout setup.program (embedding.event index) = _
        simpa [index, outputLayout, eventCount] using embedding.layout_eq index
      let checks := compileChecks (published := published) refs
        source.registry source.revelations selected
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes (embedding.event index)) =
            .resolve owner payload (refs.get selected) checks := by
        change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
          ((toEventGraph setup.program).nodes (embedding.event index)) = _
        simpa [index, compileRankedNodes, checks] using aligned.graphSuffix.nodeEq index
      change EventGraph.EventCode.actor ((graph setup).nodes (embedding.event index)) = none
        at chance
      rw [← EventGraph.EventCode.actor_cast outputEq, codeEq] at chance
      cases chance

/-- The completion mass of a completion with the given event and action is the
graph step's mass for a chance event. -/
theorem completionMass_of_chance (before after : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : before.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    completionMass setup before after =
      ((before.config.step event ready action) after.config).toReal := by
  have dropped : after.config.history.drop before.config.history.length = [⟨event, action⟩] := by
    rw [EventGraph.Config.step_history _ event ready action _ member, List.drop_left]
  unfold completionMass
  rw [dropped]
  simp only [chance, ready, ↓reduceDIte]

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **A chance completion matches** in the intended replay, from a replayed
history at the decoded point of a configuration with a source residual. -/
theorem replayStepMatches_chance (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (history : setup.intendedProtocol.History) (pending : ℝ)
    (before after : (application setup leaks).Control) (idle : before.actor = none)
    (joint : Player → Option (application setup leaks).Action) {rank : Nat}
    (residual : SourceResidual setup profile rank before.execution.application.config)
    (current : history.state =
      some (residual.lift (ProtocolState.entry residual.program residual.source)))
    {event : (graph setup).EventId} (ready : before.execution.application.config.cut.Ready event)
    {action : (graph setup).Action event}
    (member : after.execution.application.config ∈
      (before.execution.application.config.step event ready action).support)
    (chance : (graph setup).actor? event = none) :
    ReplayStepMatches setup leaks assessment who history pending (some before) joint
      (some after) := by
  obtain ⟨decoded, mass⟩ := residual.chanceMass event ready action _ member chance
  refine replayStepMatches_completion assessment who history pending before after idle joint
    ready member fun legal => ?_
  have nobody : ∀ player, (⟨actingJoint setup history.state
      (decodeEventAction setup.program event action), legal⟩ :
      { action : ∀ i, Option (setup.intendedProtocol.Action i) //
        setup.intendedProtocol.Legal history.state action }).1 player = none := by
    intro player
    change actingJoint setup history.state (decodeEventAction setup.program event action) player =
      none
    rw [current, decoded]
    simp [actingJoint]
  have opponents := setup.intendedModel.opponentsStepProb_eq_one_of_none assessment.strategy
    who history.trace _ nobody
  simp only [chance, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [completionMass_of_chance _ _ ready member chance]
  unfold counterfactualStepProb
  rw [opponents, one_mul]
  congr 1
  change (setup.protocolStep history.state (actingJoint setup history.state
    (decodeEventAction setup.program event action)) _).toReal = _
  rw [current, decoded, protocolStep_actingJoint]
  exact mass

end Vegas
