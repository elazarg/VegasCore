/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDeviationPhase

/-! # The deviator's choice in its own phase

In a phase of its own binding or guarded disclosure, a deviator within the
permitted menu chooses at some roster visit, from its complete native input.
Every other player is silent. The phase leaves the decoded source
configuration at a source successor of the phase's entry configuration, and the
deviator's native traffic at the end of the phase determines its new source
view. Its traffic at the end of the phase has a law that depends on the native
execution only through its traffic at the start.

Together with an entry factorization of that traffic through the deviator's
source view, this makes the deviator's source choice a behavioral choice of
its source view, and restores the factorization at the successor.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The owner's view after its commitment determines its view before and its
choice. -/
private theorem commit_owner_view_reflects {Γ : SourceCtx Player L} {who : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ who name payload)
    (left right : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view who =
      (commitSuccessor name guard right second).view who) :
    left.view who = right.view who ∧ first = second := by
  constructor
  · calc left.view who = ((commitSuccessor name guard left first).view who).back
            (decide (who = who)) := (back_commit_view who name guard left first).symm
      _ = ((commitSuccessor name guard right second).view who).back (decide (who = who)) :=
          congrArg _ same
      _ = right.view who := back_commit_view who name guard right second
  · have cell := congrArg (fun view : DecisionView who ((name, .commitment who payload) :: Γ) =>
      view.1.cells.get .here) same
    simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons, ite_true] at cell
    exact Option.some.inj cell

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The owner's view after its guarded disclosure determines its view before
and its choice, which it records in its own history. -/
private theorem reveal_owner_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    left.view who = right.view who ∧ first = second := by
  refine ⟨reveal_view_reflects who published selected left right first second same, ?_⟩
  have last := congrArg (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    view.2.getLast?) same
  simp only [Config.view, revealSuccessor, Function.update_self, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.some.injEq, OwnAction.reveal.injEq,
    true_and] at last
  exact last

omit [Fintype Player] in
/-- Equal deviator traffic gives equal deviator observations. -/
private theorem observe_eq_of_traffic (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (left right : (application setup leaks).Execution)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right) :
    left.observe (application setup leaks) who = right.observe (application setup leaks) who := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks]
  exact congrArg₂ (fun view evidence =>
    (⟨right.network.observe who, view, evidence⟩ : (application setup leaks).PlayerView))
    views receipts

/-- **The deviator's binding.** In its own binding phase the deviator's
permitted policy draws a source binding that is a behavioral choice of its
source view, supported on bound values and, at unreached views, on a given
fallback; the deviator's traffic again factors through its new view. -/
theorem sourceService_deviator_binding_factorization
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (deviation past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    {Γ : SourceCtx Player L} {openNames : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ who name payload)
    (next : SourceProgram Player L ((name, .commitment who payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name who fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name who fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.commit name who fresh guard next) profile refs (source seed).revelations
        (source seed).registry embedding refsBefore rank)
    (boundary : ∀ seed ∈ prior.support,
      ServiceBoundary setup leaks rosters (initial seed) (source seed) refs rank (execution seed))
    (network : (runtime setup).NetworkPolicy leaks)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.commit name who fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := Function.update (sourceServiceTimedPolicy setup leaks rosters timing
      wholeProfile) who deviation
    ∃ kernel : DecisionView who Γ → PMF (PublicationResult (L.Val payload)),
      (∀ view choice, choice ∈ (kernel view).support →
        choice ∈ (commitKernel profile view).support ∨ ∃ value, choice = .success value) ∧
      ∃ nextNoise : DecisionView who ((name, .commitment who payload) :: Γ) → PMF _,
        (prior.bind fun seed =>
          ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution seed)).map fun final =>
              (decodeSourcePrefix? (.commit name who fresh guard next) refs
                (source seed).registry (source seed).revelations embedding.ref 1
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks who final)) =
        ((prior.map source).bind fun config =>
          (kernel (config.view who)).map (commitSuccessor name guard config)).bind fun config =>
            (nextNoise (config.view who)).map fun extra =>
              ((some (Sum.inr (ProtocolState.entry next config)) :
                Option (ProtocolState (.commit name who fresh guard next))), extra) := by
  intro index event players
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some who := by
    change (toEventGraph setup.program).actor? event = some who
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .binding who payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using
      (aligned prior.support_nonempty.choose).graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind who payload outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_bind _ _
  have decodedAction (value : L.Val payload) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value)) =
        some (.commit who name payload (.success value)) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.success value))
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let lawfulPlayers := Function.update (permittedSilence setup leaks bounds rosters) who deviation
  have allLawful : ∀ player past view response,
      response ∈ (lawfulPlayers player past view).support →
        response ∈ (sourceServiceMenu setup leaks bounds rosters).actions player past view := by
    intro player past view response member
    by_cases same : player = who
    · subst player
      simp only [lawfulPlayers, Function.update_self] at member
      exact lawful past view response member
    · simp only [lawfulPlayers, Function.update_of_ne same] at member
      exact permittedSilence_lawful setup leaks bounds rosters player past view response member
  have sole (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.publicView.SoleReady event :=
    soleReady_of_ready setup (execution seed).application
      ((boundary seed supported).ready event eventRank)
  have blocks (seed : Seed) (supported : seed ∈ prior.support) :=
    deviation_owned_block setup leaks bounds rosters timing wholeProfile who deviation network
      event owned (execution seed) (sole seed supported)
  let decode := fun (seed : Seed) (final : (application setup leaks).Execution) =>
    decodeSourcePrefix? (.commit name who fresh guard next) refs (source seed).registry
      (source seed).revelations embedding.ref 1 final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((name, .commitment who payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.commit name who fresh guard next)))
  have successor (seed : Seed) (supported : seed ∈ prior.support)
      (final : (application setup leaks).Execution)
      (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
        (rosterBlock setup rosters event) (execution seed)).support) :
      ∃ value : L.Val payload,
        ServiceBoundary setup leaks rosters (initial seed)
          (commitSuccessor name guard (source seed) (.success value))
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1) final ∧
        decode seed final = embed (commitSuccessor name guard (source seed) (.success value)) := by
    rw [(blocks seed supported).2] at reached
    obtain ⟨value, _, nextBoundary⟩ := (boundary seed supported).binding_block bounds values
      lawfulPlayers allLawful network event eventRank name who payload guard outputEq codeEq node
        owned (fun ref => refsBefore ref index) decodedAction
        (opportunities event who payload outputEq)
        ((boundary seed supported).binding_capacity bounds capacity event eventRank who)
        final reached
    refine ⟨value, nextBoundary, ?_⟩
    simp only [decode, decodeSourcePrefix?_commit]
    exact congrArg (Option.map Sum.inr)
      (nextBoundary.toSourceCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  have embedInjective : Function.Injective embed := fun left right same =>
    ProtocolState.entry_injective next (Sum.inr_injective (Option.some.inj same))
  have : Nonempty (PublicationResult (L.Val payload)) := ⟨.failure⟩
  obtain ⟨kernel, kernelSupport, nextNoise, law⟩ := exists_observed_choice_factorization prior
    source (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun seed => (runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) (execution seed))
    ((runtime setup).bindingTraffic leaks who)
    (fun left leftSupport right rightSupport same => by
      have shape : rosterBlock setup rosters event =
          (rosters event).map ServiceInstruction.player ++ (.includeLatest event who ::
            List.replicate (event.val + 1) .tick ++ [.expire event]) := by
        rw [rosterBlock_of_owner setup rosters event who owned]
        simp
      rw [(blocks left leftSupport).1, (blocks right rightSupport).1, shape]
      exact (runtime setup).owner_phase_focal_law leaks network (rosters event) who deviation
        event (event.val + 1) (execution left) (execution right)
        (boundary left leftSupport).recall (boundary right rightSupport).recall same)
    (commitSuccessor name guard) (fun config => config.view who) decode embed
    (fun seed supported final reached => by
      obtain ⟨value, _, decoded⟩ := successor seed supported final reached
      exact ⟨.success value, decoded⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
        leftChoice rightChoice leftDecoded rightDecoded same => by
      obtain ⟨leftValue, leftBoundary, leftActual⟩ := successor left leftSupport leftFinal
        leftReached
      obtain ⟨rightValue, rightBoundary, rightActual⟩ := successor right rightSupport rightFinal
        rightReached
      have leftConfig := embedInjective (leftDecoded.symm.trans leftActual)
      have rightConfig := embedInjective (rightDecoded.symm.trans rightActual)
      rw [leftConfig, rightConfig]
      exact Vegas.source_view_eq_of_observe_eq setup leaks _ who _ _ leftFinal rightFinal
        leftBoundary.agrees rightBoundary.agrees leftBoundary.history rightBoundary.history
        (observe_eq_of_traffic setup leaks who leftFinal rightFinal same))
    (fun left leftChoice right rightChoice same =>
      commit_owner_view_reflects name guard left right leftChoice rightChoice same)
    (commitKernel profile)
  refine ⟨kernel, ?_, nextNoise, law⟩
  intro view choice member
  rcases kernelSupport view choice member with fallback | ⟨seed, supported, final, reached, same⟩
  · exact Or.inl fallback
  · right
    obtain ⟨value, _, actual⟩ := successor seed supported final reached
    have configs := embedInjective (same.symm.trans actual)
    exact ⟨value, (commit_owner_view_reflects name guard _ _ _ _
      (congrArg (fun config => config.view who) configs)).2⟩

/-- **The deviator's guarded disclosure.** In its own disclosure phase the
deviator's permitted policy draws a source disclosure that is a behavioral
choice of its source view; the deviator's traffic again factors through its
new view. -/
theorem sourceService_deviator_reveal_factorization
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters) (wholeProfile : BehavioralProfile setup.program)
    (who : Player) (deviation : (application setup leaks).Policy)
    (lawful : ∀ past view response, response ∈ (deviation past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment who payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published who name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published who name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (rank : Nat)
    (prior : PMF Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile
      (.reveal published who name fresh binding unresolved next) profile
      refs (source seed).revelations (source seed).registry embedding refsBefore rank)
    (boundary : ∀ seed ∈ prior.support,
      ServiceBoundary setup leaks rosters (initial seed) (source seed) refs rank (execution seed))
    (network : (runtime setup).NetworkPolicy leaks)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    let index : Fin (eventCount (.reveal published who name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event : (graph setup).EventId := embedding.event index
    let players := Function.update (sourceServiceTimedPolicy setup leaks rosters timing
      wholeProfile) who deviation
    ∃ kernel : DecisionView who Γ → PMF Bool,
      ∃ nextNoise : DecisionView who ((published, .publication payload) :: Γ) → PMF _,
        (prior.bind fun seed =>
          ((runtime setup).runInteractionPlan leaks players network
            (rosterBlock setup rosters event) (execution seed)).map fun final =>
              (decodeSourcePrefix? (.reveal published who name fresh binding unresolved next)
                refs (source seed).registry (source seed).revelations embedding.ref 1
                final.application.config.store (decodeHistory setup.program
                  (final.application.config.history.map
                    (setup.eventGraph.fromModeCompletion .sequential))),
                (runtime setup).bindingTraffic leaks who final)) =
        ((prior.map source).bind fun config =>
          (kernel (config.view who)).map (revealSuccessor published binding config)).bind
            fun config => (nextNoise (config.view who)).map fun extra =>
              ((some (Sum.inr (ProtocolState.entry next config)) :
                Option (ProtocolState (.reveal published who name fresh binding unresolved
                  next))), extra) := by
  intro index event players
  have eventRank : event.val = rank := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using
      (aligned prior.support_nonempty.choose).graphSuffix.rankEq index
  have owned : (graph setup).actor? event = some who := by
    change (toEventGraph setup.program).actor? event = some who
    simpa [event, index, eventOwner?, eventCount] using
      (aligned prior.support_nonempty.choose).actorEq index
  have outputEq : (graph setup).outputLayout event = .publication payload := by
    change outputLayout setup.program event = _
    simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
  have codeEq (seed : Seed) :
      cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve who payload (refs.get binding)
          (compileChecks (published := published) refs (source seed).registry
            (source seed).revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using (aligned seed).graphSuffix.nodeEq index
  have node (seed : Seed) : nodeView (graph setup) event =
      .resolve who payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding) outputEq (codeEq seed) :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have decodedAction (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal who name disclose) := by
    have lookup := (aligned prior.support_nonempty.choose).actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using lookup
  let lawfulPlayers := Function.update (permittedSilence setup leaks bounds rosters) who deviation
  have allLawful : ∀ player past view response,
      response ∈ (lawfulPlayers player past view).support →
        response ∈ (sourceServiceMenu setup leaks bounds rosters).actions player past view := by
    intro player past view response member
    by_cases same : player = who
    · subst player
      simp only [lawfulPlayers, Function.update_self] at member
      exact lawful past view response member
    · simp only [lawfulPlayers, Function.update_of_ne same] at member
      exact permittedSilence_lawful setup leaks bounds rosters player past view response member
  have sole (seed : Seed) (supported : seed ∈ prior.support) :
      (execution seed).application.publicView.SoleReady event :=
    soleReady_of_ready setup (execution seed).application
      ((boundary seed supported).ready event eventRank)
  have blocks (seed : Seed) (supported : seed ∈ prior.support) :=
    deviation_owned_block setup leaks bounds rosters timing wholeProfile who deviation network
      event owned (execution seed) (sole seed supported)
  let decode := fun (seed : Seed) (final : (application setup leaks).Execution) =>
    decodeSourcePrefix? (.reveal published who name fresh binding unresolved next) refs
      (source seed).registry (source seed).revelations embedding.ref 1
      final.application.config.store
      (decodeHistory setup.program (final.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)))
  let embed := fun config : Config Player L ((published, .publication payload) :: Γ) =>
    (some (Sum.inr (ProtocolState.entry next config)) :
      Option (ProtocolState (.reveal published who name fresh binding unresolved next)))
  have successor (seed : Seed) (supported : seed ∈ prior.support)
      (final : (application setup leaks).Execution)
      (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
        (rosterBlock setup rosters event) (execution seed)).support) :
      ∃ disclose : Bool,
        ServiceBoundary setup leaks rosters (initial seed)
          (revealSuccessor published binding (source seed) disclose)
          (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) final ∧
        decode seed final = embed (revealSuccessor published binding (source seed) disclose) := by
    rw [(blocks seed supported).2] at reached
    obtain ⟨disclose, _, nextBoundary⟩ := (boundary seed supported).reveal_block bounds
      lawfulPlayers allLawful network event eventRank published binding outputEq (codeEq seed)
        (node seed) owned (fun ref => refsBefore ref index) decodedAction final reached
    refine ⟨disclose, nextBoundary, ?_⟩
    simp only [decode, decodeSourcePrefix?_reveal]
    exact congrArg (Option.map Sum.inr)
      (nextBoundary.toSourceCheckpoint.decode next (fun tail => embedding.ref tail.succ))
  have embedInjective : Function.Injective embed := fun left right same =>
    ProtocolState.entry_injective next (Sum.inr_injective (Option.some.inj same))
  obtain ⟨kernel, _, nextNoise, law⟩ := exists_observed_choice_factorization prior
    source (fun seed => (runtime setup).bindingTraffic leaks who (execution seed))
    (fun config => config.view who) noise factor
    (fun seed => (runtime setup).runInteractionPlan leaks players network
      (rosterBlock setup rosters event) (execution seed))
    ((runtime setup).bindingTraffic leaks who)
    (fun left leftSupport right rightSupport same => by
      have shape : rosterBlock setup rosters event =
          (rosters event).map ServiceInstruction.player ++ (.includeLatest event who ::
            List.replicate (event.val + 1) .tick ++ [.expire event]) := by
        rw [rosterBlock_of_owner setup rosters event who owned]
        simp
      rw [(blocks left leftSupport).1, (blocks right rightSupport).1, shape]
      exact (runtime setup).owner_phase_focal_law leaks network (rosters event) who deviation
        event (event.val + 1) (execution left) (execution right)
        (boundary left leftSupport).recall (boundary right rightSupport).recall same)
    (revealSuccessor published binding) (fun config => config.view who) decode embed
    (fun seed supported final reached => by
      obtain ⟨disclose, _, decoded⟩ := successor seed supported final reached
      exact ⟨disclose, decoded⟩)
    (fun left leftSupport leftFinal leftReached right rightSupport rightFinal rightReached
        leftChoice rightChoice leftDecoded rightDecoded same => by
      obtain ⟨leftDisclose, leftBoundary, leftActual⟩ := successor left leftSupport leftFinal
        leftReached
      obtain ⟨rightDisclose, rightBoundary, rightActual⟩ := successor right rightSupport
        rightFinal rightReached
      have leftConfig := embedInjective (leftDecoded.symm.trans leftActual)
      have rightConfig := embedInjective (rightDecoded.symm.trans rightActual)
      rw [leftConfig, rightConfig]
      exact Vegas.source_view_eq_of_observe_eq setup leaks _ who _ _ leftFinal rightFinal
        leftBoundary.agrees rightBoundary.agrees leftBoundary.history rightBoundary.history
        (observe_eq_of_traffic setup leaks who leftFinal rightFinal same))
    (fun left leftChoice right rightChoice same =>
      reveal_owner_view_reflects published binding left right leftChoice rightChoice same)
    (revealKernel profile)
  exact ⟨kernel, nextNoise, law⟩

end Vegas
