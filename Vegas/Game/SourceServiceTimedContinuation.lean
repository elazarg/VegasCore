/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Game.SourceServiceLaw

/-! # Exact timed continuations at supported source boundaries

The existing joint prefix induction also starts at an arbitrary supported
typed checkpoint. Its terminal marginal preserves the entire typed source
store, including persistent initial parameters and public outcomes. The
physical continuation uses the existing remaining service blocks.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem statePrefix_readout
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (source : Config Player L Γ) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[eventCount program]
      (PMF.pure (ProtocolState.entry program source))).map (ProtocolState.readout program) =
        (runFrom program profile source).map some := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, Function.iterate_zero_apply, ProtocolState.entry,
        ProtocolState.readout, runFrom, runWith, PMF.pure_map]
  | sample name fresh distribution next ih =>
      have law := ProtocolState.behavioralStatePrefix_sample profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_sample, PMF.map_bind]
      exact bind_congr_on_support _ fun value _ => ih (afterSample profile)
        (sampleSuccessor name source value)
  | commit name owner fresh guard next ih =>
      have law := ProtocolState.behavioralStatePrefix_commit profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_commit, PMF.map_bind]
      exact bind_congr_on_support _ fun value _ => ih (afterCommit profile)
        (commitSuccessor name guard source value)
  | reveal published owner name fresh binding unresolved next ih =>
      have law := ProtocolState.behavioralStatePrefix_reveal profile source (eventCount next)
      have mapped := congrArg (PMF.map (ProtocolState.readout _)) law
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
        ProtocolState.readout, Sum.elim_inr] at mapped
      refine mapped.trans ?_
      rw [runFrom_reveal, PMF.map_bind]
      exact bind_congr_on_support _ fun disclose _ => ih (afterReveal profile)
        (revealSuccessor published binding source disclose)

private theorem liftedPrefix_continuation
    {Γ Δ : SourceCtx Player L} {names restNames : Finset VarId}
    (whole : SourceProgram Player L Γ names) (wholeProfile : BehavioralProfile whole)
    (program : SourceProgram Player L Δ restNames) (profile : BehavioralProfile program)
    (lift : ProtocolState program → ProtocolState whole)
    (commutes : ∀ state, ProtocolState.behavioralStateStep whole wholeProfile (lift state) =
      (ProtocolState.behavioralStateStep program profile state).map lift)
    (source : Config Player L Δ) (count : Nat) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
      (PMF.pure (ProtocolState.entry program source))).bind
        (fun state => ProtocolState.continuationLaw whole wholeProfile (lift state)) =
      ProtocolState.continuationLaw whole wholeProfile
        (lift (ProtocolState.entry program source)) := by
  induction count with
  | zero => simp only [Function.iterate_zero_apply, PMF.pure_bind]
  | succ count ih =>
      rw [Function.iterate_succ_apply', PMF.bind_bind]
      trans ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
        (PMF.pure (ProtocolState.entry program source))).bind
          (fun state => ProtocolState.continuationLaw whole wholeProfile (lift state))
      · apply bind_congr_on_support _
        intro state _
        refine (PMF.bind_map _ lift
          (ProtocolState.continuationLaw whole wholeProfile)).symm.trans ?_
        rw [← commutes]
        exact sourceStep_continuation whole wholeProfile (lift state)
      · exact ih

/-- At any supported typed boundary, all remaining actual timed service blocks
have the residual source protocol state law. -/
theorem sourceServiceTimedPolicy_suffix_state_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile who))
    (focal : Player)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (source : Config Player L Γ) (execution : (application setup leaks).Execution)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile refs
      source.revelations source.registry embedding refsBefore offset)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        (rosterPlanPrefix setup rosters offset)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support)
    (effective : ∀ who, (profile who).EffectiveDisclosures program source.registry
      source.revelations) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((List.finRange (eventCount program)).flatMap fun index =>
        rosterBlock setup rosters (embedding.event index)) execution).map
          (fun final => decodeSourcePrefix? program refs source.registry source.revelations
            embedding.ref (eventCount program) final.application.config.store
            (decodeHistory setup.program (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))) =
      ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[eventCount
        program]
        (PMF.pure (ProtocolState.entry program source))).map some := by
  obtain ⟨noise, law⟩ := sourceServiceTimedPolicy_prefix_joint_factorization setup leaks bounds
    values capacity rosters opportunities timing network wholeProfile covered focal
    (eventCount program) program profile refs embedding refsBefore offset
    (PMF.pure ()) (fun _ => source) (fun _ => execution) (fun _ => aligned)
    (fun _ => checkpoint) (fun _ => supported) (fun _ => effective)
    (fun _ => PMF.pure ((runtime setup).bindingTraffic leaks focal execution))
    (by simp only [PMF.pure_map, PMF.pure_bind]) le_rfl
  have marginal := congrArg (PMF.map Prod.fst) law
  have all : (List.finRange (eventCount program)).take (eventCount program) =
      List.finRange (eventCount program) :=
    List.take_of_length_le (by rw [List.length_finRange])
  simp only [all] at marginal
  simpa only [PMF.pure_bind, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
    PMF.bind_const] using marginal

/-- At any supported typed boundary, all remaining actual timed service blocks
have the complete terminal-store law of the residual source continuation. -/
theorem sourceServiceTimedPolicy_suffix_readout_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile who))
    (focal : Player)
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (source : Config Player L Γ) (execution : (application setup leaks).Execution)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile refs
      source.revelations source.registry embedding refsBefore offset)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
        (rosterPlanPrefix setup rosters offset)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support)
    (effective : ∀ who, (profile who).EffectiveDisclosures program source.registry
      source.revelations) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing wholeProfile) network
      ((List.finRange (eventCount program)).flatMap fun index =>
        rosterBlock setup rosters (embedding.event index)) execution).map
          (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
            final.application.config.store) = (runFrom program profile source).map some := by
  have marginal := sourceServiceTimedPolicy_suffix_state_law setup leaks bounds values capacity
    rosters opportunities timing network wholeProfile covered focal program profile refs embedding
    refsBefore offset source execution aligned checkpoint supported effective
  have readout := congrArg (PMF.map fun state => state.bind (ProtocolState.readout program))
    marginal
  simp only [PMF.map_comp, Function.comp_def, Option.bind_some,
    decodeSourcePrefix?_terminal_readout] at readout
  exact readout.trans (statePrefix_readout program profile source)

/-- The complete timed suffix, from any supported native phase boundary,
preserves the whole source terminal state. In particular, mapping this law
through `setup.parameterOutcome` preserves initial types jointly with every
public result. The residual program and its decoder transport are obtained
from the actual retained prefix; they are not additional hypotheses. -/
theorem sourceServiceTimedPolicy_continuation_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who
      (sourceServiceTimedPolicy setup leaks rosters timing profile who))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (focal : Player) (offset : Nat) (within : offset ≤ eventCount setup.program)
    (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network
        (rosterPlanPrefix setup rosters offset)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (((List.finRange (graph setup).order.eventCount).drop offset).flatMap
        (rosterBlock setup rosters)) execution).map
          (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (setup.continuationLaw profile
        (sourceServicePrefix? setup offset execution.application.config)).map some := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  let players := sourceServiceTimedPolicy setup leaks rosters timing profile
  have uniform := roster_restrict_prefix_support setup leaks rosters network menu players
    covered offset execution supported
  obtain ⟨initial, _, state, _, decoded, Γ, names, program, tailProfile, source, refs,
      embedding, refsBefore, aligned, _, lift, stateEq, commutes, transport, tailEffective,
      _, boundary⟩ := initialized_sourceService_prefix_support setup leaks bounds values
    capacity rosters opportunities menu.uniformResponses
    (fun who past view action chosen =>
      (menu.uniformResponses_support who past view action).mp chosen)
    network profile offset within execution uniform
  let sourceLaw := (fun law => law.bind
    (ProtocolState.behavioralStateStep program tailProfile))^[eventCount program]
      (PMF.pure (ProtocolState.entry program source))
  let physical := (runtime setup).runInteractionPlan leaks players network
    (((List.finRange (graph setup).order.eventCount).drop offset).flatMap
      (rosterBlock setup rosters)) execution
  have indices : (List.finRange (eventCount program)).map embedding.event =
      (List.finRange (graph setup).order.eventCount).drop offset := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, List.length_drop]
      have counted := aligned.graphSuffix.countEq
      change offset + eventCount program = (graph setup).order.eventCount at counted
      omega
    · intro index leftBound rightBound
      have small : index < eventCount program := by
        simpa only [List.length_map, List.length_finRange] using leftBound
      have large : offset + index < (graph setup).order.eventCount := by
        simp only [List.length_drop, List.length_finRange] at rightBound
        omega
      have leftItem : (List.finRange (eventCount program))[index]'(by
          simpa only [List.length_finRange] using small) = ⟨index, small⟩ :=
        List.getElem_finRange _
      have rightItem : (List.finRange (graph setup).order.eventCount)[offset + index]'(by
          simpa only [List.length_finRange] using large) = ⟨offset + index, large⟩ :=
        List.getElem_finRange _
      rw [List.getElem_map, List.getElem_drop, leftItem]
      exact (Fin.ext (aligned.graphSuffix.rankEq ⟨index, small⟩)).trans rightItem.symm
  have plans : (List.finRange (eventCount program)).flatMap
      (fun index => rosterBlock setup rosters (embedding.event index)) =
        ((List.finRange (graph setup).order.eventCount).drop offset).flatMap
          (rosterBlock setup rosters) := by
    rw [← List.flatMap_map, indices]
  have residual := sourceServiceTimedPolicy_suffix_state_law setup leaks bounds values capacity
    rosters opportunities timing network profile covered focal program tailProfile refs embedding
    refsBefore offset source execution aligned boundary.toSourceCheckpoint supported
    (tailEffective effective)
  have decoder (final : (application setup leaks).Execution) :
      sourceServicePrefix? setup (eventCount setup.program) final.application.config =
        (decodeSourcePrefix? program refs source.registry source.revelations embedding.ref
          (eventCount program) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion .sequential)))).map lift := by
    have same := transport (eventCount program) final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
    rw [aligned.graphSuffix.countEq] at same
    exact same
  have marginal : physical.map
      (fun final => sourceServicePrefix? setup (eventCount setup.program)
        final.application.config) = sourceLaw.map (fun state => some (lift state)) := by
    have mapped := congrArg (PMF.map (Option.map lift)) residual
    simpa only [PMF.map_comp, Function.comp_def, Option.map_some, plans, decoder,
      physical, sourceLaw, players] using mapped
  have stopped (current : ProtocolState program) (chosen : current ∈ sourceLaw.support) :
      ProtocolState.terminal setup.program (lift current) := by
    have member : some (lift current) ∈ (physical.map
        (fun final => sourceServicePrefix? setup (eventCount setup.program)
          final.application.config)).support := by
      rw [marginal, PMF.support_map]
      exact ⟨current, chosen, rfl⟩
    obtain ⟨final, _, same⟩ := PMF.support_map .. ▸ member
    exact decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ _ same
  have readout := congrArg (PMF.map setup.protocolReadout) marginal
  simp only [PMF.map_comp, Function.comp_def, sourceServicePrefix?_terminal_readout]
    at readout
  have conserved := liftedPrefix_continuation setup.program profile program tailProfile lift
    commutes.1 source (eventCount program)
  have finished : sourceLaw.map (fun current => ProtocolState.readout setup.program
      (lift current)) =
        (ProtocolState.continuationLaw setup.program profile
          (lift (ProtocolState.entry program source))).map some := by
    rw [← conserved, PMF.map_bind]
    calc
      _ = sourceLaw.bind (fun current => PMF.pure
          (ProtocolState.readout setup.program (lift current))) := (PMF.bind_pure_comp _ _).symm
      _ = _ := bind_congr_on_support _ fun current chosen =>
        (ProtocolState.continuationLaw_terminal setup.program profile (lift current)
          (stopped current chosen)).symm
  rw [decoded, stateEq]
  change physical.map (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) = _
  simpa only [sourceReadout_eq_decode, Setup.continuationLaw] using readout.trans finished

end Vegas
