/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixSupport
import Vegas.Game.RevealServiceClock
import Vegas.Game.SourceStateKernel
import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Source-state laws at every revelation prefix

The runtime prefix is the actual finite service plan. The source side iterates
its existing protocol transition kernel, which `SourceContinuation` identifies
with the state marginal of standard behavioral histories. Native alias recall
is retained and may be selected differently without changing Boolean marginals.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem iterate_kernel_map {A B : Type}
    (left : A → PMF A) (right : B → PMF B) (readout : A → B)
    (commutes : ∀ state, right (readout state) = (left state).map readout)
    (law : PMF A) (count : Nat) :
    (fun distribution => distribution.bind right)^[count] (law.map readout) =
      ((fun distribution => distribution.bind left)^[count] law).map readout := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => commutes state

/-- Every source-compatible alias policy has the exact source protocol-state law
at each prefix, including private setup cells and source action history. -/
theorem run_source_prefix_option_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup)) who past view)
    (projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks wholeProfile who view)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations []
        embedding refsBefore offset →
      ∀ (count : Nat), count ≤ eventCount program →
      ∀ execution, Checkpoint setup leaks initial source refs offset execution →
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount program)).take count).flatMap fun index =>
          block setup watcher (embedding.event index)) execution).map
        (fun final => decodePrefix? program refs source.revelations embedding.ref count
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
          (PMF.pure (ProtocolState.entry program source))).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro _reveals profile source refs embedding refsBefore offset _aligned count countBound
        execution checkpoint
      have zero : count = 0 := by simpa [eventCount] using countBound
      subst count
      simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
        PMF.pure_map, Function.iterate_zero_apply]
      apply congrArg PMF.pure
      rw [checkpoint.history]
      exact decodePrefix?_zero_of_agrees _ refs embedding.ref source checkpoint.emptyRegistry _
        checkpoint.agrees
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile source refs embedding refsBefore offset aligned count countBound
        execution checkpoint
      cases count with
      | zero =>
          simp only [List.take_zero, List.flatMap_nil, runInteractionPlan,
            PMF.pure_map, Function.iterate_zero_apply]
          apply congrArg PMF.pure
          rw [checkpoint.history]
          exact decodePrefix?_zero_of_agrees _ refs embedding.ref source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count =>
          let index : Fin (eventCount
            (.reveal published owner name fresh selected unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have eventRank : event.val = offset := by
            simpa [event, index] using aligned.graphSuffix.rankEq index
          have actor : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have different : owner ≠ watcher := by
            intro same
            exact observer event (same ▸ actor)
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
            reveal_head_code setup fresh selected unresolved next refs source.revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get selected) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          obtain ⟨opportunity, activeCheckpoint, granted, _clock, _activation,
              opportunityLaw, _opportunityRecall⟩ :=
            checkpoint.owner_opportunity players ((runtime setup).reportNetwork leaks watcher)
              event owner
          obtain ⟨value, bound⟩ := activeCheckpoint.openable selected
          obtain ⟨candidate, associated, owned, fixed, selectedOpening⟩ :=
            opening_at_checkpoint setup leaks selected source.state refs opportunity
              activeCheckpoint.agrees activeCheckpoint.binding event actor outputEq codeEq node
              granted value bound
          have covered := opening_available_of_initial_tables setup leaks bounds initial
            initialSupport opportunity activeCheckpoint.accepted activeCheckpoint.candidates _
            candidate associated owner owned ⟨payload, value⟩ fixed event
          have choiceLaw := projects owner different (opportunity.recall owner)
            (opportunity.observe (application setup leaks) owner) _ selectedOpening covered
          rw [sourceChoiceLaw_reveal setup leaks fresh selected unresolved next wholeProfile profile
            refs source embedding refsBefore offset aligned opportunity activeCheckpoint.agrees
            activeCheckpoint.history granted] at choiceLaw
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          let resultRef : EventGraph.FieldRef (graphLayout setup.program) (.publication payload) :=
            ⟨.inr event, outputEq⟩
          let tailRefs := refs.cons (name := published) (cell := .publication payload) resultRef
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                apply embedding.strictMono
                exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
            | there ref => exact refsBefore ref (Fin.succ remaining)
          have tailAligned := aligned.revealTail (whole := setup.program)
            (wholeProfile := wholeProfile) fresh selected unresolved next profile refs
            source.revelations [] embedding refsBefore offset
          let suffix : List (ServiceInstruction (graph setup)) :=
            [.includeLatest event owner, .player watcher, .wire] ++
              List.replicate (event.val + 1) .tick ++ [.expire event]
          let remaining := ((List.finRange (eventCount next)).take count).flatMap fun tail =>
            block setup watcher (tailEmbedding.event tail)
          have planEq : (((List.finRange (eventCount
              (.reveal published owner name fresh selected unresolved next))).take
                (count + 1)).flatMap fun i =>
                block setup watcher (embedding.event i)) =
              [.grant event, .player owner] ++ (suffix ++ remaining) := by
            simp only [eventCount, List.finRange_succ, List.take_succ_cons, ← List.map_take,
              List.flatMap_cons, List.flatMap_map]
            change block setup watcher event ++ remaining = _
            rw [block_of_owner setup watcher owner event actor]
            simp only [suffix, List.append_assoc, List.cons_append, List.nil_append]
          rw [planEq, runInteractionPlan_append, opportunityLaw, PMF.bind_map, PMF.map_bind]
          rw [ProtocolState.behavioralStatePrefix_reveal, ← choiceLaw,
            PMF.bind_map, PMF.map_bind]
          apply bind_congr_on_support _
          intro response supported
          have member := ordinary owner different _ _ response supported
          have decoded (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal owner name disclose) := by
            have embedded := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using embedded
          obtain ⟨after, afterLaw, afterCheckpoint, _recall⟩ :=
            activeCheckpoint.reveal_response (bounds.withInitialValues (initialLaw setup)) players
              watcher watcherPolicy published selected event eventRank actor outputEq codeEq node
              (fun ref => refsBefore ref index) decoded granted response member
          rw [runInteractionPlan_append, afterLaw, PMF.pure_bind]
          have nextAligned : CompiledPolicySuffix setup.program wholeProfile next
              (afterReveal profile) tailRefs
              (revealSuccessor published selected source
                (sourceChoice setup leaks response)).revelations
              [] tailEmbedding tailBefore (offset + 1) := by
            simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, resultRef,
              tailEmbedding, OutputEmbedding.ref] using tailAligned
          have nextBound : count ≤ eventCount next := by simpa [eventCount] using countBound
          have tailLaw := ih reveals (afterReveal profile)
            (revealSuccessor published selected source (sourceChoice setup leaks response))
            tailRefs tailEmbedding tailBefore (offset + 1) nextAligned count nextBound after
            afterCheckpoint
          simp only [decodePrefix?_reveal]
          have lifted := congrArg (fun law : PMF (Option (ProtocolState next)) =>
            law.map (Option.map (Sum.inr (α := Config Player L Γ)))) tailLaw
          simp only [PMF.map_comp, Function.comp_def, Option.map_some] at lifted
          convert lifted using 1
          · rfl
          · simp only [PMF.map_comp, Function.comp_def]

/-- Initialized prefix correspondence with the actual source behavioral
history runner. The source takes one additional step to draw its private setup;
the native service starts from the same initialized finite law. -/
theorem initialized_prefix_source_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup)) who past view)
    (projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks profile who view)
    (count : Nat) (within : count ≤ eventCount setup.program) :
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players ((runtime setup).reportNetwork leaks watcher)
        (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
          (fun final => sourcePrefix? setup count final.application.config) =
      ((setup.informationModel admission).runBehavioral
        (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
        (count + 1)).map GameTheory.Protocol.ExecutionProtocol.History.state := by
  rw [GameTheory.Protocol.InformationModel.runBehavioral, setup.runBehavioralFrom_state,
    Function.iterate_succ_apply, PMF.pure_bind]
  change _ = (fun law : PMF setup.ProtocolState => law.bind (setup.behavioralStateStep admission
    (fun who => setup.toProtocolBehavioralPolicy admission who (profile who)
      (permitted who))))^[count]
    (setup.behavioralStateStep admission
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who)
        (permitted who)) none)
  rw [setup.behavioralStateStep_none]
  have split := iterate_bind
    (setup.behavioralStateStep admission
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who)))
    count setup.initialLaw
    (fun initial => PMF.pure
      (some (ProtocolState.entry setup.program (setup.initialConfig initial))))
  rw [← ← PMF.bind_pure_comp, Function.comp_def] at split
  rw [split, initialLaw, PMF.bind_map, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial supported
  have wrapped := iterate_kernel_map
    (ProtocolState.behavioralStateStep setup.program profile)
    (setup.behavioralStateStep admission
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who)))
    some (setup.behavioralStateStep_encoded_some admission profile permitted)
    (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial))) count
  rw [PMF.pure_map] at wrapped
  rw [wrapped]
  exact run_source_prefix_option_law setup leaks bounds watcher observer profile players
    watcherPolicy ordinary projects initial supported setup.program reveals profile
    (setup.initialConfig initial) (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program) (initialRefsBefore setup.program) 0
    (CompiledPolicySuffix.whole setup.program profile) count within
    (ReactiveApplication.Execution.initial (application setup leaks)
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)))
    (checkpoint_initial setup leaks reveals initial (openable initial supported))

/-- The executable response compiler preserves every source behavioral prefix,
including arbitrary correlated private setup and every choice of alias weight.
The right side uses the supplied legal source protocol profile itself. -/
theorem compiled_plan_prefix_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : GameTheory.Profile (setup.informationModel admission).behavioralSignature)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (count : Nat) (within : count ≤ eventCount setup.program) :
    ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks
        (policy setup leaks (bounds.withInitialValues (initialLaw setup)) watcher
          (setup.decodeBehavioralProfile admission profile) weight nonnegative atMostOne)
        ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).map
          (fun final => sourcePrefix? setup count final.application.config) =
      ((setup.informationModel admission).runBehavioral profile (count + 1)).map
        GameTheory.Protocol.ExecutionProtocol.History.state := by
  let source := setup.decodeBehavioralProfile admission profile
  have permitted (who : Player) : (source who).Admitted setup.program admission :=
    ((setup.behavioralPolicyEquiv admission who).symm (profile who)).2
  have encoded : (fun who => setup.toProtocolBehavioralPolicy admission who
      (source who) (permitted who)) = profile :=
    funext fun who => (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  let extended := bounds.withInitialValues (initialLaw setup)
  let players := policy setup leaks extended watcher source weight nonnegative atMostOne
  have reports : players watcher = (application setup leaks).reportFirstUnpublished := by
    simp only [players, policy, ↓reduceIte]
  have ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support →
        response ∈ ordinaryActions setup leaks extended who past view := by
    intro who different past view response supported
    change response ∈ (policy setup leaks extended watcher source weight nonnegative atMostOne
      who past view).support at supported
    rw [policy, ite_eq_right different] at supported
    exact ordinaryPolicy_covered setup leaks extended source weight nonnegative atMostOne
      who past view response supported
  have projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ (extended.menu (runtime setup) leaks).actions who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks source who view := by
    intro who different past view opening selected covered
    change (policy setup leaks extended watcher source weight nonnegative atMostOne
      who past view).map _ = _
    rw [policy, ite_eq_right different]
    exact ordinaryPolicy_projects setup leaks extended source weight nonnegative atMostOne
      who past view opening selected covered
  have law := initialized_prefix_source_law setup leaks bounds watcher reveals observer openable
    admission source permitted players reports ordinary projects count within
  rw [encoded] at law
  exact law

end Vegas
