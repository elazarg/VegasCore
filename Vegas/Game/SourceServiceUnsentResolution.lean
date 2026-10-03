/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceForeignDisclosure
import Vegas.Game.SourceServiceUnsentBinding

/-! # The owner's unrecorded resolution decision

Both Boolean source decisions submit a packet. Waiting conditions only the
private timing index, leaving the source decision lottery unchanged. Native
resolution responses are compared with original source alternatives using the
source-owner posterior and complete typed continuation laws.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- At a real aligned unrecorded resolution, the source Boolean lottery is
realized by actual evidence-free withholding or an authentic opening. -/
theorem RevealSource.decision_law {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {wholeProfile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup wholeProfile event execution.application.config)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (application setup leaks))
    (origins : (runtime setup).ResolutionEvidenceOrigins leaks execution)
    (effective : (site.residual site.owner).EffectiveDisclosures
      (.reveal site.published site.owner site.name site.fresh site.binding site.unresolved
        site.next) site.source.registry site.source.revelations)
    (ready : execution.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (execution.recall site.owner) event = false) :
    sourceServiceOpportunity setup leaks wholeProfile site.owner event
      (execution.recall site.owner) (execution.observe (application setup leaks) site.owner) =
      (revealKernel site.residual (site.source.view site.owner)).map fun disclose =>
        (runtime setup).windowDecision leaks event (rosterOpening? setup leaks site.owner event
          (execution.observe (application setup leaks) site.owner)) disclose := by
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next, residual,
    refs, source, embedding, refsBefore, aligned, agree, history, head, _inherits,
    _effectiveChoices⟩ := site
  dsimp only at *
  subst head
  have actual := sourceServiceOpportunity_reveal setup leaks fresh binding unresolved next
    wholeProfile residual refs source embedding refsBefore _ aligned execution agree history
    valid recalled origins
    effective ready unsent
  exact actual.trans (PMF.bind_pure_comp _ _)

/-- A concrete current decision packet fixes the next calendar configuration.
The packet's authentic material and actual handler result are explicit local
operational premises; canonical source decisions discharge them below. -/
theorem sourceService_windowDecision_config_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (opening : Option (Handle (graph setup) × Raw L)) (disclose : Bool)
    (openingOwned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (material : disclose = true → ∀ candidate raw, opening = some (candidate, raw) →
      execution.application.candidates.lookup candidate = .openable raw)
    (completed : EventGraphRuntime.State (graph setup))
    (accepted : (application setup leaks).handle execution.application
      ((runtime setup).decisionEnvelope leaks owner event opening disclose execution) =
        some completed)
    (settled : ¬completed.config.cut.Ready event) (visits : List Player) (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner] ++
        (List.replicate ticks .tick ++ [.expire event]))
      (execution.respond (application setup leaks) owner
        ((runtime setup).windowDecision leaks event opening disclose))).map
      (fun final => final.application.config) = PMF.pure completed.config := by
  let app := application setup leaks
  let selected : Fin 1 × Bool := (0, disclose)
  let message := (runtime setup).decisionEnvelope leaks owner event opening disclose execution
  let after := execution.respond app owner
    ((runtime setup).windowDecision leaks event opening disclose)
  have frame := (DecisionWindowFrame.initial (runtime setup) leaks owner event opening selected
    execution serials published).decision_response (runtime setup) leaks owner event opening
      (execution.recall owner).length selected execution execution openingOwned material
  have recorded : (runtime setup).eventRecorded leaks (after.recall owner) event = true := by
    apply (runtime setup).eventRecorded_respond leaks execution owner _ event
    cases disclose
    · rfl
    · cases opening <;> rfl
  have law := sourceService_recorded_plan_application_law setup leaks rosters timing profile
    network event owner owned after
    (by rw [frame.application]; exact soleReady_of_ready setup execution.application ready)
    recorded message rfl ((runtime setup).decisionEnvelope_addressed leaks owner event opening
      disclose execution) (by rw [frame.ledger]; exact frame.packets)
    (frame.sent (by simp [selected, decisionPassed]))
    (by rw [frame.ledger]; exact serials.next_unpublished owner) visits ticks
  dsimp only at law
  have handled : (app.handle after.application message).getD after.application = completed := by
    rw [frame.application, accepted]
    rfl
  rw [handled] at law
  obtain ⟨endpoint, expiry, endpointApp, _⟩ := (runtime setup).settled_reveal_expiry leaks
    (sourceServiceTimedPolicy setup leaks rosters timing profile) network
    { after with application := completed } event settled ticks
  rw [expiry, PMF.pure_map] at law
  have mapped := congrArg (PMF.map EventGraphRuntime.State.config) law
  simp only [PMF.map_comp, PMF.pure_map, Function.comp_def] at mapped
  rw [mapped, endpointApp]

/-- An effective source Boolean sent now has its actual source successor,
including evidence-free false and authentic true. The empty cache is a real
initialized-history invariant, rather than an assumed handler equivalence. -/
theorem RevealSource.decision_config_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (network : (runtime setup).NetworkPolicy leaks)
    {event : (graph setup).EventId} (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (valid : execution.application.BindingInvariant)
    (unremembered : execution.application.remembered = fun _ => none)
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (disclose : Bool) (effective : disclose = false ∨ ∃ value : L.Val site.payload,
      disclose = true ∧ disclosureResult site.published site.binding site.source true =
        .success value) (visits : List Player) (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player ++ [.includeLatest event site.owner] ++
        (List.replicate ticks .tick ++ [.expire event]))
      (execution.respond (application setup leaks) site.owner
        ((runtime setup).windowDecision leaks event (rosterOpening? setup leaks site.owner event
          (execution.observe (application setup leaks) site.owner)) disclose))).map
      (fun final => final.application.config) =
        PMF.pure (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
            (disclosureResult site.published site.binding site.source disclose))) := by
  have outputEq := site.outputEq
  have owned := site.owned
  obtain ⟨Γ, names, publishedName, owner, name, payload, fresh, binding, unresolved, next,
    residual, refs, source, embedding, refsBefore, aligned, agree, history, head, _inherits,
    _effectiveChoices⟩ := site
  dsimp only at *
  subst head
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) =
        .resolve owner payload (refs.get binding)
          (compileChecks (published := publishedName) refs source.registry
            source.revelations binding) := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
    simpa [compileRankedNodes] using aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
  have node := EventGraphRuntime.nodeView_eq_resolve outputEq codeEq
  let app := application setup leaks
  rcases effective with rfl | ⟨value, rfl, success⟩
  · let completed := execution.application.complete
      (embedding.event ⟨0, by simp [eventCount]⟩) ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
    have accepted : app.handle execution.application ((runtime setup).decisionEnvelope leaks
        owner (embedding.event ⟨0, by simp [eventCount]⟩) none false execution) =
          some completed := by
      rw [reactiveApplication_handle_of_current_token (runtime setup) leaks _ _ rfl]
      exact (runtime setup).handle_withhold_unremembered_eq execution.application
        (owner, execution.network.nextSerial owner) _ owner payload (refs.get binding)
        (compileChecks (published := publishedName) refs source.registry source.revelations binding)
        outputEq codeEq node ready timely rfl (by rw [unremembered])
    have settled : ¬completed.config.cut.Ready (embedding.event ⟨0, by simp [eventCount]⟩) := by
      intro active
      exact active.1 (Finset.mem_insert_self ..)
    change ((runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player ++ [.includeLatest _ owner] ++
        (List.replicate ticks .tick ++ [.expire _]))
      (execution.respond app owner ((runtime setup).windowDecision leaks _ none false))).map
      (fun final => final.application.config) = _
    simpa only [completed, State.complete, disclosureResult_false] using
      sourceService_windowDecision_config_law setup leaks rosters timing profile network owner
        _ owned execution ready serials published none false
        (by intro _ _ impossible; cases impossible) (by intro impossible; cases impossible)
        completed accepted settled visits ticks
  · obtain ⟨candidate, associated, candidateOwned, fixed, opening⟩ :=
      guarded_rosterOpening_success setup leaks publishedName binding source refs execution agree
        valid _ outputEq codeEq node value success
    rw [opening]
    have resolved := compiled_disclosure_result (graph := graph setup) publishedName binding
      source refs execution.application.config.store agree true
    rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
    have stored := EventGraph.EventCode.binding_success_of_resolve_success
      (graph := graph setup) (refs.get binding)
      (compileChecks (published := publishedName) refs source.registry source.revelations binding)
      true execution.application.config.store value resolved
    let completed := execution.application.complete
      (embedding.event ⟨0, by simp [eventCount]⟩) ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) (.success value))
    have accepted : app.handle execution.application ((runtime setup).decisionEnvelope leaks
        owner (embedding.event ⟨0, by simp [eventCount]⟩) (some (candidate, ⟨payload, value⟩)) true
        execution) = some completed := by
      exact (reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
        ((runtime setup).windowEnvelope_tokenValid leaks owner _ candidate _ execution ready)).trans
        (handle_opening_eq (runtime setup) execution.application _ _ candidate owner payload
          (refs.get binding) _ outputEq codeEq node ready timely rfl candidateOwned associated
          value fixed stored (.success value) resolved)
    have settled : ¬completed.config.cut.Ready (embedding.event ⟨0, by simp [eventCount]⟩) := by
      intro active
      exact active.1 (Finset.mem_insert_self ..)
    simpa only [completed, State.complete, success] using
      sourceService_windowDecision_config_law setup leaks rosters timing profile network owner
        _ owned execution ready serials published (some (candidate, ⟨payload, value⟩)) true
        (by intro selected raw same; cases Option.some.inj same; exact candidateOwned)
        (by intro _ selected raw same; cases Option.some.inj same; exact fixed)
        completed accepted settled visits ticks

/-- The current response publicly distinguishes opening from withholding. This
reads only the submitted packet constructor, never hidden application state. -/
def resolutionResponse? {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (response : (application setup leaks).Action) : Option Bool :=
  match response.transmission with
  | none => none
  | some material => match material.call.packet with
    | .opening _ _ _ => some true
    | .withhold _ => some false
    | _ => none

/-- A supported normalized disclosure is false or has authentic successful
opening material. This is a source support fact, with no belief premise. -/
theorem RevealSource.effective_choice {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config)
    (effective : (site.residual site.owner).EffectiveDisclosures
      (.reveal site.published site.owner site.name site.fresh site.binding site.unresolved
        site.next) site.source.registry site.source.revelations)
    (disclose : Bool)
    (supported : disclose ∈ (revealKernel site.residual (site.source.view site.owner)).support) :
    disclose = false ∨ ∃ value : L.Val site.payload,
      disclose = true ∧ disclosureResult site.published site.binding site.source true =
        .success value := by
  exact effective_reveal_supported site.fresh site.binding site.unresolved site.next
    site.residual site.source effective disclose supported

/-- Every effective source decision has the same public Boolean packet
classification at every hidden history of its information set. -/
theorem RevealSource.decision_responseChoice
    {setup : Setup (Player := Player) (L := L)}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    (execution : (application setup leaks).Execution)
    (site : RevealSource setup profile event execution.application.config)
    (valid : execution.application.BindingInvariant)
    (disclose : Bool) (effective : disclose = false ∨ ∃ value : L.Val site.payload,
      disclose = true ∧ disclosureResult site.published site.binding site.source true =
        .success value) :
    resolutionResponse? ((runtime setup).windowDecision leaks event
      (rosterOpening? setup leaks site.owner event
        (execution.observe (application setup leaks) site.owner)) disclose) = some disclose := by
  have outputEq := site.outputEq
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next, residual,
    refs, source, embedding, refsBefore, aligned, agree, history, head, _inherits,
    _effectiveChoices⟩ := site
  dsimp only at *
  subst head
  rcases effective with rfl | ⟨value, rfl, success⟩
  · rfl
  · have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) =
          .resolve owner payload (refs.get binding)
            (compileChecks (published := published) refs source.registry source.revelations
              binding) := by
      change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
        ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
      simpa [compileRankedNodes] using aligned.graphSuffix.nodeEq ⟨0, by simp [eventCount]⟩
    obtain ⟨candidate, _, _, _, opening⟩ := guarded_rosterOpening_success setup leaks published
      binding source refs execution agree valid _ outputEq codeEq
      (EventGraphRuntime.nodeView_eq_resolve outputEq codeEq) value success
    rw [opening]
    rfl

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- The actual source prefix identifies the residual Boolean decision, its
complete typed successors, every source alternative step, and the prescribed
source action marginal. No native posterior equation is assumed. -/
theorem exists_resolutionSource_step (profile : BehavioralProfile service.setup.program)
    {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (isPublication : (graph service.setup).outputLayout phase.event = .publication payload) :
    ∃ site : RevealSource service.setup profile phase.event execution.application.config,
      (∀ disclose, decodeEventAction service.setup.program phase.event
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose) =
          some (.reveal site.owner site.name disclose)) ∧
      ∀ ready : execution.application.config.cut.Ready phase.event,
        (service.setup.continuationLaw profile
          (sourceServicePrefix? service.setup phase.event.val execution.application.config) =
        (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
          service.setup.continuationLaw profile (sourceServicePrefix? service.setup
            (phase.event.val + 1) (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                (disclosureResult site.published site.binding site.source disclose))))) ∧
        (∀ joint : Player → Option (OwnAction Player L),
          service.setup.protocolStep
            (sourceServicePrefix? service.setup phase.event.val execution.application.config)
            joint =
          PMF.pure (sourceServicePrefix? service.setup (phase.event.val + 1)
            (execution.application.config.complete phase.event ready
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
                (OwnAction.disclosure (joint site.owner)))
              (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
                (disclosureResult site.published site.binding site.source
                  (OwnAction.disclosure (joint site.owner))))))) ∧
        ∀ state, sourceServicePrefix? service.setup phase.event.val
            execution.application.config = some state →
          ¬ ProtocolState.terminal service.setup.program state →
          ((profile site.owner).protocolAction service.setup.program
              (ProtocolState.observe site.owner service.setup.program state)).map
            OwnAction.disclosure =
          revealKernel site.residual (site.source.view site.owner) := by
  obtain ⟨phaseEvent, phaseSlot, phaseSelected, phasePosition, phaseReady⟩ :=
    phase
  dsimp only at isPublication ⊢
  obtain ⟨event, slot, _, _, _, Γ, names, remaining, remainingProfile, source, refs, embedding,
      refsBefore, aligned, _, ⟨supported, inherits, lift, commutes, transport⟩, phaseStart, prior,
      sample,
      boundary, startReadyFact, reachedPrior, _, sampled, _, publicEq, checkpoint, position,
      startOrigins⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities service.network profile
      who ⟨remaining, some who, execution⟩ trace rfl
  have same : event = phaseEvent :=
    (soleReady_of_ready service.setup execution.application phaseReady).2 event startReadyFact.1
  subst same
  have sameSlot : slot = phaseSlot := by
    have lengths := position.symm.trans phasePosition
    omega
  subst sameSlot
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount service.setup.program at inside
      omega
  | sample name fresh law next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have layout := embedding.layout_eq ⟨0, by simp [eventCount]⟩
      simp only [outputLayout, eventCount] at layout
      rw [headEq] at layout
      cases layout.symm.trans isPublication
  | @commit Γ names name owner sitePayload fresh guard next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph service.setup).outputLayout event = .binding owner sitePayload := by
        rw [← headEq]
        change outputLayout service.setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans isPublication
  | @reveal Γ names published siteOwner name sitePayload fresh binding unresolved next =>
      have headEq : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      subst headEq
      let site : RevealSource service.setup profile (embedding.event ⟨0, by simp [eventCount]⟩)
          execution.application.config :=
        ⟨Γ, names, published, siteOwner, name, sitePayload, fresh, binding, unresolved, next,
          remainingProfile, refs, source, embedding, refsBefore, aligned, checkpoint.agrees,
          checkpoint.history, rfl, inherits, supported⟩
      have outputEq : (graph service.setup).outputLayout
          (embedding.event ⟨0, by simp [eventCount]⟩) = .publication sitePayload :=
        site.outputEq
      have decoded (disclose : Bool) :
          decodeEventAction service.setup.program (embedding.event ⟨0, by simp [eventCount]⟩)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
              some (.reveal siteOwner name disclose) := by
        have action := aligned.actionEq ⟨0, by simp [eventCount]⟩
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        simpa [outputEq, decodeEventAction] using action
      refine ⟨site, decoded, fun ready => ?_⟩
      have now := transport 0 execution.application.config.store
        (decodeHistory service.setup.program (execution.application.config.history.map
          (service.setup.eventGraph.fromModeCompletion .sequential)))
      rw [checkpoint.decode _ embedding.ref] at now
      simp only [Nat.add_zero, Option.map_some] at now
      change sourceServicePrefix? service.setup _ execution.application.config = _ at now
      have later (disclose : Bool) :
          sourceServicePrefix? service.setup ((embedding.event ⟨0, by simp [eventCount]⟩).val + 1)
            (execution.application.config.complete (embedding.event ⟨0, by simp [eventCount]⟩)
              ready (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (disclosureResult published binding source disclose))) =
          some (lift (Sum.inr (ProtocolState.entry next
            (revealSuccessor published binding source disclose)))) := by
        have completed := checkpoint.reveal published binding _ rfl ready outputEq
          (fun ref => refsBefore ref ⟨0, by simp [eventCount]⟩) disclose (decoded disclose)
        have recovered := completed.decode next (fun tail => embedding.ref tail.succ)
        change sourceServicePrefix? service.setup _
          (execution.application.complete (embedding.event ⟨0, by simp [eventCount]⟩) ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (disclosureResult published binding source disclose))).config = _
        unfold sourceServicePrefix?
        rw [transport 1, decodeSourcePrefix?_reveal]
        exact congrArg (fun decoded => (Option.map Sum.inr decoded).map lift) recovered
      refine ⟨?_, ?_, ?_⟩
      · rw [now]
        change ProtocolState.continuationLaw service.setup.program profile
          (lift (ProtocolState.entry _ source)) = _
        rw [← sourceStep_continuation, commutes.1]
        change (((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift).bind _) = _
        rw [ProtocolState.behavioralStateStep_reveal_entry, PMF.bind_map, PMF.bind_map]
        apply bind_congr_on_support _
        intro disclose _
        rw [later disclose]
        rfl
      · intro joint
        rw [now, later]
        change ((ProtocolState.step _ (lift (ProtocolState.entry _ source)) joint).map some) = _
        rw [commutes.2.1]
        change ((PMF.pure (Sum.inr (ProtocolState.entry next (revealSuccessor published
          binding source (OwnAction.disclosure (joint siteOwner)))))).map lift).map some = _
        simp only [PMF.pure_map]
        rfl
      · intro state decodedState running
        rw [now] at decodedState
        have stateEq := Option.some.inj decodedState
        subst stateEq
        have viaResidual := commutes.1 (ProtocolState.entry _ source)
        change _ = ((ProtocolState.behavioralStateStep _ remainingProfile (.inl source)).map
          lift) at viaResidual
        rw [ProtocolState.behavioralStateStep_reveal_entry] at viaResidual
        let advance := fun disclose : Bool =>
          lift (Sum.inr (ProtocolState.entry next (revealSuccessor published binding source
            disclose)))
        have viaWhole : ProtocolState.behavioralStateStep service.setup.program profile
            (lift (ProtocolState.entry _ source)) =
            ((profile siteOwner).protocolAction service.setup.program
              (ProtocolState.observe siteOwner service.setup.program
                (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.disclosure action)) := by
          unfold ProtocolState.behavioralStateStep
          simp only [running, ↓reduceIte]
          have stepped (joint : Player → Option (OwnAction Player L)) :
              ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source))
                joint = PMF.pure (advance (OwnAction.disclosure (joint siteOwner))) := by
            rw [commutes.2.1]
            change (PMF.pure (Sum.inr (ProtocolState.entry next (revealSuccessor published
              binding source (OwnAction.disclosure (joint siteOwner)))))).map lift = _
            simp only [PMF.pure_map]
            rfl
          rw [show ProtocolState.step service.setup.program (lift (ProtocolState.entry _ source)) =
            fun joint : Player → Option (OwnAction Player L) => PMF.pure (advance
              (OwnAction.disclosure (joint siteOwner))) from funext stepped,
                ← PMF.bind_pure_comp, Function.comp_def]
          change (independentProduct _).map ((fun action => advance (OwnAction.disclosure action)) ∘
              fun joint : Player → Option (OwnAction Player L) => joint siteOwner) = _
          rw [← PMF.map_comp, independentProduct_map_eval]
          exact (pmf_bind_pure_eq_map _ _).symm
        have injective : Function.Injective advance := by
          intro first second same
          have successor := commutes.2.2 same
          have entries := (Sum.inr_injective successor)
          have configs := ProtocolState.entry_injective next entries
          have recalled := congrArg (fun config : Config Player L
            ((published, .publication sitePayload) :: Γ) =>
              (config.history siteOwner).getLast?) configs
          simpa [revealSuccessor] using recalled
        apply pmf_map_injective injective
        rw [PMF.map_comp]
        change ((profile siteOwner).protocolAction service.setup.program
          (ProtocolState.observe siteOwner service.setup.program
            (lift (ProtocolState.entry _ source)))).map
              (fun action => advance (OwnAction.disclosure action)) = _
        rw [← viaWhole, viaResidual, PMF.map_comp]
        rfl


end SourceServiceSpec

/-- The full typed configuration resulting from one effective source Boolean. -/
def RevealSource.decisionCompletion {setup : Setup (Player := Player) (L := L)}
    {profile : BehavioralProfile setup.program} {event : (graph setup).EventId}
    {config : (graph setup).Config} (site : RevealSource setup profile event config)
    (ready : config.cut.Ready event) (disclose : Bool) : (graph setup).Config :=
  config.complete event ready
    (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
    (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
      (disclosureResult site.published site.binding site.source disclose))

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- At the owner's unsent resolution, a current transport response leaves the
source Boolean law: the next-boundary configuration completes the
publication with the source disclosure lottery. The response only rules out the
current timing slot, and every later slot is still reached. -/
theorem unsent_resolution_transport_config_law {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (site : RevealSource service.setup approx.profile phase.event execution.application.config)
    (ownerEq : site.owner = who)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (ready : execution.application.config.cut.Ready phase.event)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (transport : response = ⟨none⟩) :
    approx.phaseConfigLaw phase response =
      (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
        PMF.pure (execution.application.config.complete phase.event ready
          (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
            (disclosureResult site.published site.binding site.source disclose))) := by
  obtain ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next, residual,
    refs, source, embedding, refsBefore, aligned, agree, history, head, inherits,
    effectiveChoices⟩ := site
  dsimp only at ownerEq
  subst ownerEq
  let site : RevealSource service.setup approx.profile phase.event
      execution.application.config :=
    ⟨Γ, names, published, owner, name, payload, fresh, binding, unresolved, next, residual,
      refs, source, embedding, refsBefore, aligned, agree, history, head, inherits,
      effectiveChoices⟩
  change approx.phaseConfigLaw phase response =
    (revealKernel site.residual (site.source.view site.owner)).bind fun disclose =>
      PMF.pure (execution.application.config.complete phase.event ready
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
            (disclosureResult site.published site.binding site.source disclose)))
  let app := application service.setup service.leaks
  have owned : (graph service.setup).actor? phase.event = some owner := site.owned
  obtain ⟨_, state, _, _, _, timely, valid, recalled, origins, unremembered⟩ :=
    service.disclosure_decision_resources trace phase owned site.outputEq
  have serials := state.2.1
  have publishedPackets := state.2.2.1 unsent
  have effective := site.inherits approx.effective site.owner
  let offset := rosterOffset service.setup service.rosters owner phase.event
  let family := sourceServiceTimedFamily service.setup service.leaks service.rosters
    approx.profile owner phase.event
  let mixtureImpl := app.policyMixture (approx.timing phase.event owner owned) family
  let rest : List (ServiceInstruction (graph service.setup)) :=
    List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]
  have passive : ∀ instruction ∈ rest, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [rest, List.mem_append, List.mem_replicate, List.mem_singleton] at member
    rcases member with ⟨_, rfl⟩ | rfl <;> simp
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event owner :: rest := by
    simp only [rosterPhaseEnding, owned, rest, List.cons_append, List.nil_append]
  have counted := service.recall_count trace phase
  have visitsCount : ((service.rosters phase.event).take phase.slot).count owner + 1 +
      phase.visits.count owner = (service.rosters phase.event).count owner := by
    conv_rhs => rw [phase.roster_split]
    simp only [List.count_append, List.count_cons_self]
    omega
  have positive : 0 < (service.rosters phase.event).count owner := by omega
  let last : Fin ((service.rosters phase.event).count owner) :=
    ⟨(service.rosters phase.event).count owner - 1, by omega⟩
  have posteriorFuture := sourceServiceTimedMixture_decision_future service.setup service.leaks
    service.bounds service.values service.initialValues service.capacity service.rosters
    service.opportunities service.network approx.profile approx.admitted
    owner ⟨remaining, some owner, execution⟩ trace rfl phase.event phase.ready owned
    unsent (approx.timing phase.event owner owned) last
    (approx.timingFull phase.event owner owned last) (by dsimp only [last]; omega)
  have opening := RevealSource.decision_law service.leaks execution site valid recalled origins
    effective
    phase.ready unsent
  have preserved := (runtime service.setup).silent_response_preserves service.leaks _
    execution publishedPackets owner response transport
  have counters := (runtime service.setup).silent_response_preserves service.leaks _
    execution serials owner response transport
  have afterUnsent := (runtime service.setup).eventRecorded_respond_transport service.leaks
    execution owner owner response transport phase.event
  have afterLength := app.respond_recall_length execution owner owner response
  simp only [↓reduceIte] at afterLength
  have serving : (execution.observe app owner).application.publicView.ownTurn? owner =
      some phase.event :=
    PublicView.ownTurn?_of_ownTurn _ owner phase.event (phase.sole.ownTurn owned)
  have policyEq : approx.players owner (execution.recall owner)
      (execution.observe app owner) =
      mixtureImpl.policy (execution.recall owner) (execution.observe app owner) := by
    simp only [players, sourceServiceTimedPolicy_turn _ _ _ _ _ owner _ _ phase.event owned
      serving]
    rfl
  have present := service.menu.fullyMixed_response_support (initialLaw service.setup)
    service.planLength service.scheduler approx.players approx.covered approx.assessment
    approx.strategy approx.mixed owner remaining execution trace response allowed
  rw [policyEq, ReactiveApplication.Implementation.policy_eq, PMF.support_map] at present
  obtain ⟨witness, witnessSupport, witnessAction⟩ := present
  have meets : ∃ pair ∈ Prod.fst ⁻¹' {response}, pair ∈ ((mixtureImpl.posterior
      (execution.recall owner)).bind fun memory => mixtureImpl.respond memory
        (execution.recall owner, execution.observe app owner)).support :=
    ⟨witness, witnessAction, witnessSupport⟩
  set after := execution.respond app owner response with afterDef
  have sameApp : after.application = execution.application := preserved.1
  have afterSole : after.application.publicView.SoleReady phase.event := by
    rw [sameApp]
    exact phase.sole
  have afterPublished : after.network.Satisfies fun message =>
      message.id ∈ after.network.ledger.map Message.id := by
    rw [preserved.2.1]
    exact preserved.2.2.2.2.1
  have afterSerials : after.network.SerialsBeforeNext := by
    unfold MessageNetwork.SerialsBeforeNext
    rw [counters.2.2.2.1]
    exact counters.2.2.2.2.1
  have mixed : (runtime service.setup).runInteractionPlan service.leaks approx.players
      service.network (phase.visits.map ServiceInstruction.player ++
        .includeLatest phase.event owner :: rest) after =
      (runtime service.setup).runInteractionPlan service.leaks
        (Function.update (fun _ => app.silentPolicy) owner mixtureImpl.policy)
        service.network (phase.visits.map ServiceInstruction.player ++
          .includeLatest phase.event owner :: rest) after := by
    rw [runInteractionPlan_append, runInteractionPlan_append,
      sourceServiceTimedPolicy_window_eq service.setup service.leaks service.rosters
        approx.timing approx.profile phase.event owner owned service.network phase.visits
        after afterSole]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq service.setup service.leaks _ _ service.network _
      (by simp [rest]) (by intro actor; simp [rest]) current
  have mixture := (runtime service.setup).runInteractionPlan_policyMixture service.leaks
    (approx.timing phase.event owner owned) family owner (fun _ => app.silentPolicy)
    service.network (phase.visits.map ServiceInstruction.player ++
      .includeLatest phase.event owner :: rest) after
  dsimp only at mixture
  have later (slot : Fin ((service.rosters phase.event).count owner))
      (member : slot ∈ (mixtureImpl.posterior (after.recall owner)).support) :
      (after.recall owner).length ≤ offset + slot.val ∧
        offset + slot.val < (after.recall owner).length + phase.visits.count owner := by
    rw [afterDef, ReactiveApplication.Implementation.posterior_respond, PMF.support_map]
      at member
    obtain ⟨pair, conditioned, rfl⟩ := member
    obtain ⟨matched, supported⟩ := mem_support_fiberPosterior (mem_support_map_of_exists_mem_fiber
        meets) conditioned
    obtain ⟨memory, memorySupport, drawn⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
    obtain ⟨action, actionSupport, rfl⟩ := PMF.support_map .. ▸ drawn
    change action = response at matched
    subst matched
    have notBefore := posteriorFuture memory memorySupport
    have notNow : offset + memory.val ≠ (execution.recall owner).length := by
      intro now
      have scheduled : rosterOffset service.setup service.rosters owner phase.event + memory.val =
          (execution.recall owner).length := now
      have fires : family memory (execution.recall owner) (execution.observe app owner) =
          sourceServiceOpportunity service.setup service.leaks approx.profile owner phase.event
            (execution.recall owner) (execution.observe app owner) := by
        simp only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, scheduled, ↓reduceIte]
      change action ∈ (family memory (execution.recall owner)
        (execution.observe app owner)).support at actionSupport
      rw [fires, opening, PMF.support_map] at actionSupport
      obtain ⟨choice, _, submitted⟩ := actionSupport
      rw [transport] at submitted
      have impossible := congrArg ReactiveApplication.Action.transmission submitted
      cases impossible
    dsimp only
    rw [afterLength]
    change (execution.recall owner).length ≤ offset + memory.val at notBefore
    have within := memory.isLt
    change (execution.recall owner).length =
      offset + ((service.rosters phase.event).take phase.slot).count owner at counted
    constructor <;> omega
  unfold phaseConfigLaw phaseLaw DecisionPhase.tail
  rw [ending, mixed, ← mixture, PMF.map_bind]
  calc
    _ = (mixtureImpl.posterior (after.recall owner)).bind fun _ =>
        (revealKernel site.residual (site.source.view owner)).bind fun disclose =>
          PMF.pure (execution.application.config.complete phase.event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) disclose)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm)
            (disclosureResult site.published site.binding site.source disclose))) := by
      apply bind_congr_on_support _
      intro slot member
      obtain ⟨notPassed, within⟩ := later slot member
      exact reveal_slot_config_law service.setup service.leaks service.rosters service.network
        approx.profile after site (by rw [sameApp]) (afterUnsent.trans unsent) effective ready
        (by rw [sameApp]; exact timely) (by rw [sameApp]; exact valid)
        (by rw [sameApp]; exact unremembered)
        (app.respond_inputRecall execution owner response recalled)
        ((runtime service.setup).resolutionEvidenceOrigins_respond service.leaks service.bounds
          execution recalled valid origins owner response
          (sourceServiceMenu_in_compiled service.setup service.leaks service.bounds
            service.rosters owner _ _ allowed))
        (phase.event.val + 1) afterSerials afterPublished phase.visits slot notPassed within
    _ = _ := PMF.bind_const _ _


/-- Complete typed source continuation after a Boolean publication decision. -/
def resolutionContinuation {execution : (application service.setup service.leaks).Execution}
    {event : (graph service.setup).EventId}
    (ready : execution.application.config.cut.Ready event) {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (result : Bool → PublicationResult (L.Val payload)) (disclose : Bool) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  approx.boundaryContinuation (event.val + 1)
    (execution.application.config.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm) (result disclose)))

/-- Actual native and original source continuations at an owner's unrecorded
resolution. Waiting keeps the source lottery; either submitted constructor fixes
the corresponding Boolean. All laws retain the complete typed terminal state. -/
structure UnsentResolutionLaws {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (ready : execution.application.config.cut.Ready event) where
  name : VarId
  values : PMF Bool
  result : Bool → PublicationResult (L.Val payload)
  decoded : ∀ disclose, decodeEventAction service.setup.program event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
      some (.reveal who name disclose)
  boundary : (service.setup.continuationLaw approx.profile (sourceServicePrefix? service.setup
    event.val execution.application.config)).map some =
      values.bind (approx.resolutionContinuation ready outputEq result)
  step : ∀ joint : Player → Option (OwnAction Player L),
    service.setup.protocolStep (sourceServicePrefix? service.setup event.val
      execution.application.config) joint =
    PMF.pure (sourceServicePrefix? service.setup (event.val + 1)
      (execution.application.config.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (OwnAction.disclosure (joint who)))
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (result (OwnAction.disclosure (joint who))))))
  marginal : ∀ state, sourceServicePrefix? service.setup event.val
      execution.application.config = some state →
    ¬ ProtocolState.terminal service.setup.program state →
    ((approx.profile who).protocolAction service.setup.program
      (ProtocolState.observe who service.setup.program state)).map OwnAction.disclosure = values
  prescribed : (approx.players who (execution.recall who)
    (execution.observe (application service.setup service.leaks) who)).bind
      (approx.responseReadout phase) =
        values.bind (approx.resolutionContinuation ready outputEq result)
  responses : ∀ response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who),
    (∃ disclose ∈ values.support, resolutionResponse? response = some disclose ∧
      approx.responseReadout phase response =
        approx.resolutionContinuation ready outputEq result disclose) ∨
    (response = ⟨none⟩ ∧ approx.responseReadout phase response =
      values.bind (approx.resolutionContinuation ready outputEq result))

/-- The actual retained history supplies all source and native resolution laws,
including missing opening material. No posterior or continuation equality is
assumed, and the original source comparison remains available below. -/
theorem unsent_resolution_decision {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout phase.event = .publication payload)
    (owned : (graph service.setup).actor? phase.event = some who)
    (unsent : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      phase.event = false)
    (ready : execution.application.config.cut.Ready phase.event) :
    Nonempty (approx.UnsentResolutionLaws phase outputEq ready) := by
  obtain ⟨site, decodedAction, stepFacts⟩ := service.exists_resolutionSource_step approx.profile
    trace phase outputEq
  have ownerEq := Option.some.inj (site.owned.symm.trans owned)
  have payloadEq := EventGraph.EventField.publication.inj (site.outputEq.symm.trans outputEq)
  obtain ⟨Γ, names, publishedName, siteOwner, name, sitePayload, fresh, binding, unresolved,
    next, residual, refs, source, embedding, refsBefore, aligned, agree, history, head,
    inherits, effectiveChoices⟩ := site
  dsimp only at ownerEq payloadEq
  subst ownerEq
  subst payloadEq
  let site : RevealSource service.setup approx.profile phase.event
      execution.application.config :=
    ⟨Γ, names, publishedName, siteOwner, name, sitePayload, fresh, binding, unresolved,
      next, residual, refs, source, embedding, refsBefore, aligned, agree, history, head,
      inherits, effectiveChoices⟩
  obtain ⟨sourceStep, anyStep, marginal⟩ := stepFacts ready
  obtain ⟨_, state, _, _, _, timely, valid, recalled, origins, unremembered⟩ :=
    service.disclosure_decision_resources trace phase owned outputEq
  let values := revealKernel residual (source.view siteOwner)
  let result := disclosureResult publishedName binding source
  let decision := fun disclose => (runtime service.setup).windowDecision service.leaks
    phase.event (rosterOpening? service.setup service.leaks siteOwner phase.event
      (execution.observe (application service.setup service.leaks) siteOwner)) disclose
  have effective := site.inherits approx.effective site.owner
  have choiceValid (disclose : Bool) (member : disclose ∈ values.support) :
      disclose = false ∨ ∃ value : L.Val sitePayload,
        disclose = true ∧ result true = .success value :=
    site.effective_choice effective disclose member
  have opportunity := site.decision_law service.leaks execution valid recalled origins effective
    ready unsent
  have ending : rosterPhaseEnding service.setup phase.event =
      .includeLatest phase.event siteOwner :: (List.replicate (phase.event.val + 1) .tick ++
        [.expire phase.event]) := by
    simp only [rosterPhaseEnding, owned, List.cons_append, List.nil_append]
  have submitted (disclose : Bool) (member : disclose ∈ values.support)
      (allowed : decision disclose ∈ service.menu.actions siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner)) :
      approx.responseReadout phase (decision disclose) =
        approx.resolutionContinuation ready outputEq result disclose := by
    rw [approx.response_continuation_law trace phase _ allowed]
    have actual : approx.phaseConfigLaw phase (decision disclose) =
        PMF.pure (execution.application.config.complete phase.event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) (result disclose))) := by
      unfold phaseConfigLaw phaseLaw DecisionPhase.tail
      rw [ending]
      simpa only [players, decision, site, result, List.append_assoc, List.singleton_append] using
        site.decision_config_law service.setup service.leaks
        service.rosters approx.timing approx.profile service.network execution ready timely valid
        unremembered state.2.1 (state.2.2.1 unsent) disclose (choiceValid disclose member)
        phase.visits (phase.event.val + 1)
    rw [actual, PMF.pure_bind]
    rfl
  have transported (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner))
      (transport : response = ⟨none⟩) :
      approx.responseReadout phase response =
        values.bind (approx.resolutionContinuation ready outputEq result) := by
    rw [approx.response_continuation_law trace phase response allowed,
      approx.unsent_resolution_transport_config_law trace phase site rfl unsent ready response
        allowed transport, PMF.bind_bind]
    simp only [PMF.pure_bind]
    rfl
  have serving : (execution.observe (application service.setup service.leaks)
      siteOwner).application.publicView.ownTurn? siteOwner = some phase.event :=
    PublicView.ownTurn?_of_ownTurn _ siteOwner phase.event (phase.sole.ownTurn owned)
  let mixtureImpl := (application service.setup service.leaks).policyMixture
    (approx.timing phase.event siteOwner owned)
    (sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
      siteOwner phase.event)
  have policyEq : approx.players siteOwner (execution.recall siteOwner)
      (execution.observe (application service.setup service.leaks) siteOwner) =
      (mixtureImpl.posterior (execution.recall siteOwner)).bind fun slot =>
        sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
          siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) := by
    simp only [players, sourceServiceTimedPolicy_turn _ _ _ _ _ siteOwner _ _ phase.event owned
      serving]
    exact (application service.setup service.leaks).policyMixture_policy _ _ _ _
  have slotLaw (slot : Fin ((service.rosters phase.event).count siteOwner)) :
      sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
        siteOwner phase.event slot (execution.recall siteOwner)
          (execution.observe (application service.setup service.leaks) siteOwner) =
          values.map decision ∨
      sourceServiceTimedFamily service.setup service.leaks service.rosters approx.profile
        siteOwner phase.event slot (execution.recall siteOwner)
          (execution.observe (application service.setup service.leaks) siteOwner) =
          (application service.setup service.leaks).silentPolicy (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner) := by
    by_cases now : rosterOffset service.setup service.rosters siteOwner phase.event + slot.val =
        (execution.recall siteOwner).length
    · left
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
        now, ↓reduceIte]
      exact opportunity
    · right
      simp only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy, Option.map_some,
        Option.some.injEq, now, ↓reduceIte]
  have classify (response : (application service.setup service.leaks).Action)
      (supported : response ∈ (approx.players siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner)).support) :
      (∃ disclose ∈ values.support, response = decision disclose) ∨ response = ⟨none⟩ := by
    rw [policyEq, PMF.support_bind] at supported
    obtain ⟨slot, _, drawn⟩ := Set.mem_iUnion₂.mp supported
    rcases slotLaw slot with fires | waits
    · rw [fires, PMF.support_map] at drawn
      obtain ⟨disclose, member, same⟩ := drawn
      exact Or.inl ⟨disclose, member, same.symm⟩
    · rw [waits] at drawn
      exact Or.inr ((application service.setup service.leaks).silentPolicy_cases _ _ response drawn)
  have allowedOf (response : (application service.setup service.leaks).Action)
      (supported : response ∈ (approx.players siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner)).support) :
      response ∈ service.menu.actions siteOwner (execution.recall siteOwner)
        (execution.observe (application service.setup service.leaks) siteOwner) :=
    approx.covered siteOwner ⟨remaining, some siteOwner, execution⟩ trace rfl response supported
  refine ⟨⟨name, values, result, decodedAction, ?_, anyStep, marginal, ?_, ?_⟩⟩
  · rw [sourceStep, PMF.map_bind]
    rfl
  · rw [policyEq, PMF.bind_bind]
    refine (bind_congr_on_support _ (g := fun _ => values.bind
      (approx.resolutionContinuation ready outputEq result)) ?_).trans (PMF.bind_const _ _)
    intro slot slotSupport
    have present (response : (application service.setup service.leaks).Action)
        (drawn : response ∈ (sourceServiceTimedFamily service.setup service.leaks
          service.rosters approx.profile siteOwner phase.event slot (execution.recall siteOwner)
            (execution.observe (application service.setup service.leaks) siteOwner)).support) :
        response ∈ (approx.players siteOwner (execution.recall siteOwner)
          (execution.observe (application service.setup service.leaks) siteOwner)).support := by
      rw [policyEq, PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨slot, slotSupport, drawn⟩
    rcases slotLaw slot with fires | waits
    · rw [fires, PMF.bind_map]
      apply bind_congr_on_support _
      intro disclose member
      exact submitted disclose member (allowedOf _ (present _ (by
        rw [fires, PMF.support_map]
        exact ⟨disclose, member, rfl⟩)))
    · rw [waits]
      refine (bind_congr_on_support _ ?_).trans (PMF.bind_const _ _)
      intro response supported
      exact transported response (allowedOf response (present response (by
        rw [waits]
        exact supported)))
        ((application service.setup service.leaks).silentPolicy_cases _ _ response supported)
  · intro response allowed
    have present := service.menu.fullyMixed_response_support (initialLaw service.setup)
      service.planLength service.scheduler approx.players approx.covered
      approx.assessment approx.strategy approx.mixed siteOwner remaining execution trace
      response allowed
    rcases classify response present with ⟨disclose, member, rfl⟩ | transport
    · exact Or.inl ⟨disclose, member,
        site.decision_responseChoice service.leaks execution valid disclose
          (choiceValid disclose member), submitted disclose member allowed⟩
    · exact Or.inr ⟨transport, transported response allowed transport⟩

end TimedApproximant

namespace TimedApproximant

open Classical in
/-- At an owner's visit to its own unsent resolution, every local lottery of the
`ofSource` approximant has prescribed and alternative laws equal to the
prescribed and alternative laws of one mixture of original source assessment
comparisons. A native Boolean decision is simulated by the same source
publication decision, and a transport response by the prescribed source
action law, which it leaves unchanged. -/
theorem unsent_resolution_comparisons (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : service.sourceModel.BehavioralAssessment)
    (full : ∀ who info, FullSupport (source.strategy who info))
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      service.sourceModel source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (owned : (graph service.setup).actor? event = some who)
    (readyView : view.application.publicView.EventReady event)
    (unsent : (runtime service.setup).eventRecorded service.leaks past event = false)
    (law : PMF (service.model.Choice who site.1)) :
    ∃ mixture : PMF (service.sourceModel.AssessmentDeviation who),
      (service.model.assessmentComparisonWith (service.model.truncatedRunner service.fuel)
          service.readout approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).prescribed =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).prescribed) ∧
      (service.model.assessmentComparisonWith (service.model.truncatedRunner service.fuel)
          service.readout approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).alternative =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).alternative) := by
  obtain ⟨sourceView, sourceHistories⟩ := owner_site_source_histories service timing
    timingFull source full sourceBayes approx built who site past view observed owned readyView
  let admission := CommitmentInterface.values service.setup.program
  let baseline := service.setup.toProtocolBehavioralPolicy admission who (approx.profile who)
    (approx.admitted who) (some sourceView)
  -- The decision data of every history of the site.
  have atHistory (history : service.model.InformationHistory who site.1) :
      ∃ (remaining : Nat) (execution : (application service.setup service.leaks).Execution)
        (_ : history.1.state = some ⟨remaining, some who, execution⟩)
        (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
        (_ : phase.event = event) (trace : (service.menu.protocol (initialLaw service.setup)
          service.planLength service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
        (ready : execution.application.config.cut.Ready event),
        execution.recall who = past ∧
          execution.observe (application service.setup service.leaks) who = view ∧
          Nonempty (approx.UnsentResolutionLaws phase outputEq ready) := by
    obtain ⟨remaining, execution, current, phase, same, recallEq, viewEq⟩ :=
      site_decision who site past view observed readyView history
    have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
        service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
      current ▸ history.1.trace
    obtain ⟨phaseEvent, slot, selected, position, phaseReady⟩ := phase
    dsimp only at same
    subst same
    let phase : DecisionPhase service.setup service.leaks service.rosters who execution :=
      ⟨phaseEvent, slot, selected, position, phaseReady⟩
    obtain ⟨_, _, _, _, ready, _⟩ :=
      service.disclosure_decision_resources trace phase owned outputEq
    have unsentNow : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
        phaseEvent = false := recallEq ▸ unsent
    exact ⟨remaining, execution, current, phase, rfl, trace, ready, recallEq, viewEq,
      approx.unsent_resolution_decision trace phase outputEq owned unsentNow ready⟩
  obtain ⟨reference, _, _⟩ := site.2
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨⟨name, _, _, referenceDecoded, _⟩⟩⟩ := atHistory reference
  let realize : Bool →
      (service.setup.informationModel admission).Choice who (some sourceView) := fun disclose =>
    if found : ∃ choice ∈ baseline.support, OwnAction.disclosure choice.1 = disclose
    then found.choose else baseline.support_nonempty.choose
  let sourceLaw : PMF ((service.setup.informationModel admission).Choice who
      (some sourceView)) :=
    law.bind fun choice => match resolutionResponse? (choice.1.getD ⟨none⟩) with
      | some disclose => PMF.pure (realize disclose)
      | none => baseline
  obtain ⟨alternative, admittedAlternative, alternativeLaw⟩ :=
    service.setup.exists_admitted_local_law admission approx.profile approx.admitted who
      (some sourceView) sourceLaw
  apply owner_comparisons_of_continuations service timing timingFull source full sourceBayes
    approx built who site past view observed owned readyView law alternative admittedAlternative
  · intro history _
    obtain ⟨remaining, execution, current, phase, _, trace, ready, recallEq, viewEq,
      ⟨⟨_, values, result, _, sourceStep, _, _, prescribed, _⟩⟩⟩ := atHistory history
    have localLaw := approx.local_law_readout history.1 current phase history.2
      (approx.assessment.strategy who site.1)
    rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at localLaw
    rw [localLaw, prescribed_response_law approx trace site.1
      (observed.trans (by rw [recallEq, viewEq])), prescribed, ← sourceStep]
    simp only [decodedState, current, Option.bind_some]
  · intro history member
    obtain ⟨remaining, execution, current, phase, _, trace, ready, recallEq, viewEq,
      ⟨⟨otherName, values, result, decodedHere, sourceStep, anyStep, marginal, _, responses⟩⟩⟩ :=
        atHistory history
    have sameName : otherName = name := by
      have both := (decodedHere false).symm.trans (referenceDecoded false)
      simpa using both
    subst sameName
    obtain ⟨sourceHistory, sourceState, running, active, info⟩ := sourceHistories history member
    have decodedEq : decodedState service event history.1 =
        sourceServicePrefix? service.setup event.val execution.application.config := by
      simp only [decodedState, current, Option.bind_some]
    rw [decodedEq] at sourceState
    obtain ⟨state, stateEq⟩ : ∃ state, sourceServicePrefix? service.setup event.val
        execution.application.config = some state := by
      cases decoded : sourceServicePrefix? service.setup event.val execution.application.config
        with
      | none =>
          rw [show (service.setup.informationModel admission).infoOf who sourceHistory.trace =
            service.setup.protocolObserve who sourceHistory.state from
              service.setup.protocol_info admission who sourceHistory.trace, sourceState,
                decoded] at info
          cases info
      | some state => exact ⟨state, rfl⟩
    have stateRunning : ¬ ProtocolState.terminal service.setup.program state := by
      intro stopped
      apply running
      rw [sourceState, stateEq]
      exact stopped
    have stateView : ProtocolState.observe who service.setup.program state = sourceView := by
      rw [show (service.setup.informationModel admission).infoOf who sourceHistory.trace =
        service.setup.protocolObserve who sourceHistory.state from
          service.setup.protocol_info admission who sourceHistory.trace, sourceState,
            stateEq] at info
      exact Option.some.inj info
    have baselineValues : (baseline.map Subtype.val).map OwnAction.disclosure =
        values := by
      rw [Setup.toProtocolBehavioralPolicy_map_val]
      rw [← marginal state stateEq stateRunning, stateView]
      rfl
    have localLaw := approx.local_law_readout history.1 current phase history.2 law
    rw [localLaw, decodedEq, ← sourceState, alternativeLaw sourceHistory running active info,
      sourceState]
    simp only [anyStep, ↓reduceIte, PMF.pure_bind, PMF.map_bind, PMF.bind_map,
      sourceLaw, PMF.bind_bind]
    apply bind_congr_on_support _
    intro choice _
    have allowed := service.choice_allowed history.1 current history.2 choice
    rcases responses _ allowed with ⟨disclose, member, classified, readout⟩ |
      ⟨transport, readout⟩
    · have realizable : ∃ realized ∈ baseline.support,
          OwnAction.disclosure realized.1 = disclose := by
        rw [← baselineValues, PMF.support_map, PMF.support_map] at member
        obtain ⟨action, ⟨realized, realizedSupport, rfl⟩, same⟩ := member
        exact ⟨realized, realizedSupport, same⟩
      have realized : OwnAction.disclosure (realize disclose).1 = disclose := by
        simp only [realize, realizable, ↓reduceDIte]
        exact realizable.choose_spec.2
      rw [Function.comp_apply, classified, readout]
      simp only [PMF.pure_bind, realized]
      rfl
    · have classified : resolutionResponse? (choice.1.getD ⟨none⟩) = none := by
        rw [transport]
        rfl
      rw [Function.comp_apply, classified, readout, ← baselineValues, PMF.bind_map, PMF.bind_map]
      rfl

end TimedApproximant

end Vegas
