/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosurePhase
import Vegas.Game.SourceServiceBoundary
import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel
import Vegas.Source.DisclosureBehavioral
import Interaction.ReactiveMenuPolicy

/-! # Full-source service execution laws

These laws compose the actual roster service with the existing source syntax
and its deterministic checkpoint readout. Public chance retains its source
distribution. Guarded disclosure records effective choices; original failed
intentions belong to the source normalization's private-memory distribution.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The original source policy is normalized with its private-intention
posterior before compilation. Finite restriction makes this a legal strategy
at every native information input, including inconsistent inputs. Execution
exactness uses coverage at the actual source checkpoints. -/
def sourceServiceCompiledProfile [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program) :
    GameTheory.Profile ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).behavioralSignature := fun who =>
  (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
    (sourceServiceLastPolicy setup leaks rosters
      (normalizeDisclosureProfile setup.program []
        (Revelations.initial setup.context) original) who)

/-- Decoding the finite compiler has globally legal physical support. No
assumption on unreachable private catalogues is needed for this fact. -/
theorem sourceServiceCompiledProfile_covered [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (supported : response ∈ ((sourceServiceMenu setup leaks bounds rosters).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
      (sourceServiceCompiledProfile setup leaks bounds rosters network original)
        who past view).support) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view :=
  (sourceServiceMenu setup leaks bounds rosters).decode_embedPolicy_covered
    (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
    (sourceServiceCompiledProfile setup leaks bounds rosters network original who)
    past view response supported

/-- Totalization leaves every waiting opportunity unchanged, including public
chance phases, foreign visits, early owner visits, and visits after submission.
This is proved from the actual retained response menu at the supplied input. -/
theorem sourceServiceCompiledProfile_wait [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (granted : view.application.publicView.serviceGrant = some event)
    (waiting : (graph setup).actor? event ≠ some who ∨
      (runtime setup).eventRecorded leaks past event = true ∨
      past.length + 1 ≠ rosterOffset setup rosters who event + (rosters event).count who) :
    (sourceServiceMenu setup leaks bounds rosters).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
      (sourceServiceCompiledProfile setup leaks bounds rosters network original) who past view =
        (application setup leaks).replayPolicy past view := by
  classical
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  let policy := sourceServiceLastPolicy setup leaks rosters normalized who
  have law : policy past view = app.replayPolicy past view :=
    sourceServiceLastPolicy_wait setup leaks rosters normalized who past view event granted waiting
  have optional : ¬ bindingRequired setup leaks rosters who past view := by
    rintro ⟨other, payload, otherGrant, _binding, owned, _ready, unsent, last⟩
    have same : other = event := Option.some.inj (otherGrant.symm.trans granted)
    subst other
    rcases waiting with foreign | recorded | earlier
    · exact foreign owned
    · simp only [recorded, Bool.true_eq_false] at unsent
    · exact earlier last
  have covered : ∀ response ∈ (policy past view).support,
      response ∈ menu.actions who past view := by
    intro response supported
    rw [law] at supported
    change response ∈ sourceServiceActions setup leaks bounds rosters who past view
    rw [sourceServiceActions, ite_eq_right optional]
    exact bounds.replay_compiled (runtime setup) leaks who past view response supported
  change ((menu.embedPolicy (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
      (menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) who policy)) (some (past, view))).map _ = _
  rw [menu.embed_restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who policy past view covered]
  change app.decodePolicy (app.encodePolicy policy) past view = _
  rw [app.decode_encodePolicy, law]

/-- A public-chance phase retains every player activation and replay before
executing the original sample distribution and the actual deadline suffix. -/
theorem sourceServiceLastPolicy_sample_roster
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (profile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs law) outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
      ((rosters event).map ServiceInstruction.player ++
        (.sample event :: List.replicate ticks .tick ++ [.expire event])) execution).map
        (fun final => (final.application.config, final.receipts)) =
      (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value),
          execution.receipts) := by
  let app := application setup leaks
  let players := sourceServiceLastPolicy setup leaks rosters profile
  have chance : (graph setup).actor? event = none := by
    change EventGraph.EventCode.actor ((graph setup).nodes event) = none
    rw [← EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event), codeEq]
    rfl
  let expected := (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) value), execution.receipts)
  cases rosterEq : rosters event with
  | nil =>
      simpa only [rosterEq, List.map_nil, List.nil_append] using
        source_sample_settlement setup leaks source refs execution agree event ready outputEq
          law codeEq node players network ticks
  | cons focal rest =>
      rw [← rosterEq]
      rw [(runtime setup).runInteractionPlan_append, FinDist.map_bind]
      trans ((runtime setup).runInteractionPlan leaks players network
        ((rosters event).map ServiceInstruction.player) execution).bind (fun _ => expected)
      · apply FinDist.bind_congr
        intro current reached
        have transport (point : app.Execution) who response
            (same : point.application = execution.application)
            (_ : execution.recall focal ⊆ point.recall focal)
            (supported : response ∈ (players who (point.recall who)
              (point.observe app who)).support) :
            response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
          have currentGrant : (point.observe app who).application.publicView.serviceGrant =
              some event := by change point.application.serviceGrant = _; rw [same]; exact granted
          have waiting := sourceServiceLastPolicy_wait setup leaks rosters profile who
            (point.recall who) (point.observe app who) event currentGrant
              (Or.inl (by simp only [chance, ne_eq, reduceCtorEq, not_false_eq_true]))
          change response ∈ (sourceServiceLastPolicy setup leaks rosters profile who
            (point.recall who) (point.observe app who)).support at supported
          rw [waiting] at supported
          exact app.replayPolicy_cases _ _ response supported
        obtain ⟨same, _, receipts, _, _, _⟩ :=
          (runtime setup).replay_window_preserves leaks players network focal execution
            transport _ packets (rosters event) current reached
        have currentAgree : refs.Agrees source.state current.application.config.store := by
          rw [same]; exact agree
        have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
        simpa only [same, receipts] using source_sample_settlement setup leaks source refs current
          currentAgree event currentReady outputEq law codeEq node players network ticks
      · exact FinDist.bind_const _ expected

/-- The actual guarded roster reconstructs its effective source protocol state.
The original failed intention is deliberately retained in the source lottery
but is not claimed to be recoverable from the native completion. -/
theorem sourceServiceLastPolicy_reveal_roster_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (valid : execution.application.BindingInvariant)
    (entered ticks : Nat)
    (packets : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (network : (runtime setup).NetworkPolicy leaks)
    (visited remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let _outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_position : rosters event = visited ++ owner :: remaining)
      (_granted : execution.application.serviceGrant = some event)
      (ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_activated : execution.application.activatedAt event = some entered)
      (_due : (runtime setup).deadline event ≤ execution.application.clock + ticks - entered)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event),
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
      ((rosters event).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event]))
      execution).map (fun final =>
        decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
          refs source.registry source.revelations embedding.ref 1
          final.application.config.store (decodeHistory setup.program
            (final.application.config.history.map
              (setup.eventGraph.fromModeCompletion .sequential)))) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        some (Sum.inr (ProtocolState.entry next
          (revealSuccessor published binding source
            (effectiveDisclosure published binding source disclose)))) := by
  intro index event outputEq position granted ready timely activated due unsent counted
  have law := sourceServiceLastPolicy_reveal_roster setup leaks rosters fresh binding unresolved
    next wholeProfile profile refs source embedding refsBefore offset aligned execution checkpoint
      valid entered ticks packets serials network visited remaining absent position granted ready
        timely activated due unsent counted
  let readout (result : (graph setup).Config × List (MessageId Player × Bool)) :=
    decodeSourcePrefix? (.reveal published owner name fresh binding unresolved next)
      refs source.registry source.revelations embedding.ref 1 result.1.store
        (decodeHistory setup.program
          (result.1.history.map (setup.eventGraph.fromModeCompletion .sequential)))
  have projected := congrArg (FinDist.map readout) law
  rw [FinDist.map_comp, FinDist.map_comp] at projected
  refine projected.trans ?_
  rw [FinDist.map_eq_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro disclose _
  apply congrArg FinDist.pure
  have eventRank : event.val = offset := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source disclose)) =
        some (.reveal owner name (effectiveDisclosure published binding source disclose)) := by
    have action := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (effectiveDisclosure published binding source disclose))
    simpa [event, index, outputEq, decodeEventAction] using action
  have completed := checkpoint.reveal published binding event eventRank ready outputEq
    (fun ref => refsBefore ref index)
    (effectiveDisclosure published binding source disclose) decoded
  rw [disclosureResult_effectiveDisclosure] at completed
  have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
  dsimp only [readout, Function.comp_def]
  rw [decodeSourcePrefix?_reveal]
  change (decodeSourcePrefix? next _ _ _ _ 0 _ _).map Sum.inr = _
  exact congrArg (Option.map Sum.inr) recovered

/-- For the compiler's normalized policy, the reconstructed state law is
the original source protocol's own transition kernel. Effectiveness is a
structural property of disclosure normalization, including at zero-mass views. -/
theorem effective_reveal_state_law [Fintype Player]
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ)
    (effective : (profile owner).EffectiveDisclosures
      (.reveal published owner name fresh binding unresolved next)
        source.registry source.revelations) :
    ((revealKernel profile (source.view owner)).map fun disclose =>
      some (Sum.inr (ProtocolState.entry next (revealSuccessor published binding source
        (effectiveDisclosure published binding source disclose))))) =
      (ProtocolState.behavioralStateStep
        (.reveal published owner name fresh binding unresolved next) profile
          (ProtocolState.entry _ source)).map some := by
  change _ = (ProtocolState.behavioralStateStep _ profile (.inl source)).map some
  rw [ProtocolState.behavioralStateStep_reveal_entry, FinDist.map_comp,
    FinDist.map_eq_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro disclose supported
  have fixed := effective.1 rfl (source.view owner) disclose supported
  change effectiveDisclosureView published binding source.registry source.revelations
    (sourceObserve owner source.state) disclose = disclose at fixed
  rw [effectiveDisclosureView_observe] at fixed
  simp only [fixed, Function.comp_def]

end Vegas
