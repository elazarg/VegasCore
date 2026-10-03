/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionComplement
import Vegas.Game.SourceServiceRiskSlots

/-! # The private binding residual outside actual charged classes

At a clear legal risk-menu prefix, an effective response outside the public
packet and recalled-duplicate classifiers is retained or is one canonical bare
commitment whose private opening is absent or mistyped. The latter is a real
remaining continuation-comparison obligation. It is not public bad evidence.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The exact local private-material residual: one unrecorded current binding
at the canonical counted handle, with no effective opening evidence and no
well-typed private value. The predicate does not assert detectability or utility. -/
def unusableServiceBindingResponse (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    Prop :=
  ∃ (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload),
    nodeView (graph setup) event = .bind who payload outputEq codeEq ∧
      view.application.publicView.ownTurn? who = some event ∧
      (runtime setup).eventRecorded leaks past event = false ∧
      ∃ opening, response = ⟨some ⟨⟨.commitment event
        (who, .prepared (view.application.publicView.bindingCount who)), opening⟩, .none⟩⟩ ∧
        opening.bind (fun raw => raw.as? payload) = none

/-- The private unusable-binding residual is determined by the native
information value and chosen response, uniformly across its hidden histories. -/
def unusableServiceBindingChoice (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) (who : Player)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info) : Prop :=
  ∃ past view response, info = some (past, view) ∧ choice.1 = some response ∧
    unusableServiceBindingResponse setup leaks who past view response

variable {setup leaks} [Fintype Player]

/-- Outside the actual charged classes, a first effective binding has its
canonical public packet. Its private material is either a retained represented
value or exactly the unusable private-material residual. -/
theorem unclassifiedBinding_cases
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (material : (application setup leaks).Submission)
    (available : (⟨some material⟩ : (application setup leaks).Action) ∈
      (bounds.menu (runtime setup) leaks).actions who (execution.recall who)
        (execution.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) ⟨some material⟩)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) ⟨some material⟩) :
    (⟨some material⟩ : (application setup leaks).Action) ∈ bounds.riskActions (runtime setup) leaks
        bound who (execution.recall who) (execution.observe (application setup leaks) who) ∨
      unusableServiceBindingResponse setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) ⟨some material⟩ := by
  classical
  let app := application setup leaks
  let view := execution.observe app who
  let serial := execution.application.publicView.bindingCount who
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  obtain ⟨other, named, owned, ready, selected, unrecorded, fits⟩ :=
    unclassifiedSubmission_opportunity bound execution who rawTrace clear material notPacket
      notRecorded
  have same : other = event := Option.some.inj (selected.symm.trans turn)
  subst other
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨(who, execution.network.nextSerial who), app.packet
      (app.submit execution.application who material) who (execution.network.known who) material⟩
  have notAuditable : ¬ AuditableServicePacket setup execution.application.publicView who
      message := by
    intro classified
    apply notPacket
    refine ⟨material, rfl, ?_⟩
    rw [localServiceEnvelope_actual setup leaks rawTrace who material]
    exact classified
  have compatible : message.payload.call.MatchesNode := by
    by_contra incompatible
    exact notAuditable (Or.inr (Or.inr (Or.inl incompatible)))
  have called : message.payload.call = .commitment event (who, .prepared serial) := by
    have packetNamed : message.payload.call.event? (graph setup) = some event := named
    cases call : message.payload.call with
    | malformed raw => rw [call] at packetNamed; cases packetNamed
    | withhold addressed | opening addressed candidate raw =>
        rw [call] at packetNamed
        cases Option.some.inj packetNamed
        simp only [Payload.MatchesNode, call, node] at compatible
    | commitment addressed candidate =>
        rw [call] at packetNamed
        cases Option.some.inj packetNamed
        have canonical : candidate = (who, .prepared serial) := by
          by_contra other
          apply notAuditable
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨event, turn,
            Or.inl ⟨candidate, call, other⟩⟩)))
        rw [canonical]
  have empty : message.payload.evidence = none := by
    by_contra present
    exact notAuditable (Or.inl (Or.inr (Or.inr
      (Or.inl ⟨event, (who, .prepared serial), called, present⟩))))
  have token : message.payload.token = some ⟨event⟩ :=
    ((runtime setup).reactiveApplication_packet_token leaks execution.application who
      (execution.network.known who) material).trans
        (execution.application.publicView_tokenFor_of_ready material.call.packet event named ready)
  have emitted : material.emit (app.submit execution.application who material) who
      (execution.network.known who) =
        ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩ := by
    have eta : message.payload =
        ⟨message.payload.call, message.payload.evidence, message.payload.token⟩ := rfl
    rw [called, empty, token] at eta
    exact eta
  have persistent := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  have fresh := riskCanonicalSlot_fresh_at_turn bounds bound _ trace who persistent event turn
    unrecorded
  have selectedSlot : canonicalFreshSlot who view.application = some serial :=
    canonicalFreshSlot_canonical who view.application fresh
  have member := (bounds.menu_mem (runtime setup) leaks who _ _ _).mp available
  have normal : material.normalizeReactive who (app.observePlayer execution.application who)
      (execution.network.known who) = material := by
    have fixed := member.2
    change (⟨some (material.normalizeReactive who _ _)⟩ : app.Action) = ⟨some material⟩ at fixed
    have recalled := app.known_from_recall execution who
      (legalFacts setup leaks horizon scheduler _ rawTrace).inputs
    change execution.network.known who = ReactiveApplication.ResponseMenu.knownPackets
      (execution.recall who) (execution.observe app who) at recalled
    exact (by
      have same := Option.some.inj (congrArg ReactiveApplication.Action.transmission fixed)
      rw [← recalled] at same
      exact same)
  have shape := (runtime setup).normal_binding_of_canonical_packet leaks execution.application who
    (execution.network.known who) material event serial fresh normal emitted
  have bounded : bounds.AllowsOpening material.call.opening := member.1.1.2
  have unusable (missing : material.call.opening.bind (fun raw => raw.as? payload) = none) :
      unusableServiceBindingResponse setup leaks who (execution.recall who) view
        ⟨some material⟩ :=
    ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, material.call.opening,
      congrArg (fun submission => (⟨some submission⟩ : app.Action)) shape, missing⟩
  cases opening : material.call.opening with
  | none => exact Or.inr (unusable (by rw [opening]; rfl))
  | some raw =>
      cases decoded : raw.as? payload with
      | none => exact Or.inr (unusable (by rw [opening, Option.bind_some, decoded]))
      | some value =>
          have rawEq : raw = ⟨payload, value⟩ := by
            rcases raw with ⟨kind, input⟩
            unfold Raw.as? at decoded
            split at decoded
            · rename_i kindEq
              change kind = payload at kindEq
              subst kind
              cases Option.some.inj decoded
              rfl
            · cases decoded
          have included : (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
            rw [opening] at bounded
            change raw ∈ bounds.values at bounded
            rwa [rawEq] at bounded
          have responseEq : (⟨some material⟩ : app.Action) =
              (runtime setup).canonicalServiceDecision leaks who (execution.recall who) view event
                (cast (congrArg EventField.Action outputEq.symm) (.success value)) := by
            rw [(runtime setup).canonicalServiceDecision_binding leaks who (execution.recall who)
              view event payload outputEq codeEq node serial selectedSlot]
            rw [shape, opening, rawEq]
            rfl
          left
          rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear, responseEq]
          apply bounds.canonical_decision_retained (runtime setup) leaks who _ _ event _ turn owned
            ((execution.application.publicView_eventReady event).mpr ready)
            fits.withinDeadline unrecorded
          · simp only [MessageBounds.canonicalChoices, node]
            exact Finset.mem_image.mpr ⟨value,
              (bounds.typedValues_mem payload value).mpr
                ⟨⟨payload, value⟩, included, Raw.as?_mk payload value⟩, rfl⟩
          · rw [← responseEq]
            exact available

/-- The complete effective-response partition at an actual clear legal prefix.
All nonretained responses outside the two charged classes have precisely the
private unusable-binding form. No payoff comparison is inferred for that form. -/
theorem unclassifiedResponse_cases
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (available : response ∈ (bounds.menu (runtime setup) leaks).actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (notPacket : ¬ auditableServiceResponse setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) response)
    (notRecorded : ¬ recordedServiceResponse setup leaks (execution.recall who) response) :
    response ∈ bounds.riskActions (runtime setup) leaks bound who (execution.recall who)
        (execution.observe (application setup leaks) who) ∨
      unusableServiceBindingResponse setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) response := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none =>
          left
          rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear]
          exact bounds.silence_canonical (runtime setup) leaks who _ _
      | some material =>
          have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace
            (initialLaw setup) horizon scheduler trace
          obtain ⟨event, _, owned, _, turn, _, _⟩ := unclassifiedSubmission_opportunity bound
            execution who rawTrace clear material notPacket notRecorded
          cases node : nodeView (graph setup) event with
          | sample payload law outputEq codeEq =>
              have actor := nodeView_sample_actor outputEq codeEq
              rw [owned] at actor
              cases actor
          | bind owner payload outputEq codeEq =>
              have actor := nodeView_bind_actor outputEq codeEq
              rw [owned] at actor
              cases Option.some.inj actor
              exact unclassifiedBinding_cases bounds bound execution who trace clear event payload
                outputEq codeEq node turn material available notPacket notRecorded
          | resolve owner payload binding checks outputEq codeEq =>
              have actor := nodeView_resolve_actor outputEq codeEq
              rw [owned] at actor
              cases Option.some.inj actor
              exact Or.inl (unclassifiedResolution_retained bounds bound execution who trace clear
                event payload binding checks outputEq codeEq node turn _ available notPacket
                notRecorded)

end Vegas
