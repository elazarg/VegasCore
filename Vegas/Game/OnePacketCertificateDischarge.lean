/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSlotLaw
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport
import Vegas.Game.OnePacketUnintendedCommitment
import Vegas.Game.OnePacketSlotLawDischarge
import Vegas.Game.OnePacketRelevantLumping
import Vegas.Game.OnePacketSwapFiberSum

/-! # Inputs of the one-packet certificate

The local gain at a site of the one-packet game of installing a law
(`Vegas.onePacketSiteGain`), its failure and success parts, and the inputs of
the certificate for one source sequence: honest counterparts at a site
(`Vegas.OnePacketCounterpartInputs`), the base inputs
(`Vegas.OnePacketBaseInputs`), the base inputs with late commitments of intended
values (`Vegas.OnePacketCoreInputs`), and those with the value decompositions
(`Vegas.OnePacketOpenInputs`). Beliefs converge at forced own-turn sites
(`Vegas.onePacket_beliefConverges`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

section Law

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

/-- **Mixtures of one-packet components keep as-if-honest play away from late
deliveries.** At every forced information state that some history reaches and
that is not a late delivery, every mixture of the components of the one-packet
certificate gives each choice at least the slot retention of the scale times
its as-if-honest mass: its components are all the slot-trembled prescribed
component. -/
theorem onePacketMixture_ge_honest_of_not_late
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (n : ℕ)
    (weights : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    {who : Player} {info : (application setup leaks).Info}
    (notLate : ¬ LateDelivery setup leaks who info)
    (occurs : ∃ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History, (onePacketN).infoOf who history.trace = info)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who info)
    (choice : (onePacketN).Choice who info) :
    slotRetention (scale n) * ((honestProfile setup leaks bounds (initialLaw setup) horizon
        scheduler (sequence n) who info) choice).toReal ≤
      (((onePacketN).agentBehavior (onePacketN).playedInformation
        (onePacketFallback setup leaks bounds horizon scheduler)
        (fun agent => (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
          (freeKeyedComponent
            (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n)
            (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one (slots := slots) n) agent)) who info) choice).toReal := by
  classical
  have retention_le_one := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  by_cases present : info ∈ (onePacketN).playedInformation who
  · let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
      ⟨who, ⟨info, present⟩⟩
    have notFree : ¬ FreeAgent setup leaks bounds horizon scheduler agent :=
      fun unforced => unforced forced
    have notKeyed : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      fun keyed => notLate keyed.1
    obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free
      (key := agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree
    have constant : ∀ part, freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent part =
        onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := fun part => by
      rw [componentEq]
      exact keyedComponent_of_not_keyed _ _ notKeyed _
    have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
      (onePacketFallback setup leaks bounds horizon scheduler)
      (fun agent => (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent)) agent
    change _ ≤ (((onePacketN).agentBehavior _ _ _ agent.1 agent.2.1) choice).toReal
    have mixture : (weights (onePacketPool setup leaks bounds horizon scheduler agent)).bind
        (freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent) =
        onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n agent := by
      rw [show freeKeyedComponent
          (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
          (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n)
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n) agent = fun _ =>
          onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one n agent from funext constant]
      exact PMF.bind_const _ _
    rw [atAgent]
    refine le_of_le_of_eq (slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon
      scheduler (scale_pos n).le (scale_le_one n) who info
      (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who info)
      (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who info))
      (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who info)
      choice) ?_
    exact congrArg (fun law => (law choice).toReal) mixture.symm
  · have none : info = none := by
      obtain ⟨history, infoEq⟩ := occurs
      cases infoCase : info with
      | none => rfl
      | some observed =>
          exfalso
          apply present
          rw [← infoEq]
          apply (onePacketN).mem_playedInformation
          have active : (application setup leaks).observe who history.state = some observed :=
            ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
              scheduler who history.trace).symm.trans (infoEq.trans infoCase)
          have isSome := ((application setup leaks).observe_isSome who history.state).mp
            (by rw [active]; rfl)
          intro stopped
          revert stopped isSome
          cases history.state with
          | none => exact fun _ stopped => stopped.elim
          | some control =>
              rintro actorSome ⟨_, actorNone⟩
              simp [ReactiveApplication.actor, actorNone] at actorSome
    subst none
    have : Subsingleton ((onePacketN).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact retention_le_one

end Law

section Transmits

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source action other than withholding encodes, at a publication event, to
disclosure. -/
theorem encodeEventAction?_discloses :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (event : Fin (eventCount program)) →
    (action : OwnAction Player L) → (∀ owner name, action ≠ .reveal owner name false) →
    ∀ encoded, encodeEventAction? program event action = some encoded →
    ∀ payload (publication : outputLayout program event = .publication payload),
      cast (congrArg EventGraph.EventField.Action publication) encoded = true
  | _, _, .ret _, event, _, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, event, action, discloses, encoded, encodes => by
      cases event using Fin.cases with
      | zero => cases encodes
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes
  | _, _, .commit name owner fresh guard next, event, action, discloses, encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro _ publication
          cases publication
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes
  | _, _, .reveal published owner name fresh selected unresolved next, event, action, discloses,
      encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro _ publication
          cases action with
          | commit => cases encodes
          | reveal actionOwner actionName disclose =>
              simp only [encodeEventAction?, Fin.cases_zero] at encodes
              split_ifs at encodes with ownerEq nameEq
              cases encodes
              cases publication
              revert encoded
              change ∀ value : Bool, (∀ owner name, OwnAction.reveal actionOwner actionName value ≠
                .reveal owner name false) → value = true
              intro value discloses
              cases value
              · exact (discloses actionOwner actionName rfl).elim
              · rfl
      | succ tail =>
          exact encodeEventAction?_discloses next tail action discloses encoded encodes

end Transmits

section FirstActivation

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Transmitting first activations.** At a forced first activation for
`event` with recall `past` and view `view`, the canonical decision of every
source action encoding at the event, committing no failure and disclosing,
transmits. -/
def CanonicalTransmitsAt (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) : Prop :=
  ∀ action graphAction, encodeEventAction? setup.program event action = some graphAction →
    (∀ owner name payload, action ≠ .commit owner name payload .failure) →
    (∀ owner name, action ≠ .reveal owner name false) →
    ((runtime setup).canonicalServiceDecision leaks who past view event graphAction).transmission ≠
      none

end FirstActivation

section Open

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- **The failure set of an agent of the one-packet game**: the event-level
failed histories of its pending event, and none without one. -/
def onePacketFailed (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History :=
  match pendingEvent setup leaks agent.1 agent.2.1 with
  | none => ∅
  | some event => EventFailedHistory setup leaks bounds horizon scheduler agent.1 event

/-- Profiles assembled from mixtures of the components of the one-packet
certificate: at each index, every agent mixes its pool's components with the
pool's weights. -/
def OnePacketAssembled (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) : Prop :=
  ∀ n, (targetSequence n).strategy = (onePacketN).agentBehavior (onePacketN).playedInformation
    (onePacketFallback setup leaks bounds horizon scheduler)
    fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)

/-- The local failure probability of a law at a site of the one-packet game:
the probability of the event-level failure of the site's pending event. -/
def onePacketSiteFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localFailure (2 * horizon + 1) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- The successful part of the local exclusion payoff of a law at a site of the
one-packet game: its value on histories outside the event-level failure of the
site's pending event. -/
def onePacketSiteSuccess (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localSuccessValue (2 * horizon + 1)
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) (payoffComponent setup) assessment site
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- A response commits no value: it transmits no commitment packet. -/
def CommitsNoValue (response : (application setup leaks).Action) : Prop :=
  ∀ material, response.transmission = some material →
    ∀ event handle, material.call.packet ≠ .commitment event handle

/-- **The marked choices of the one-packet certificate**: silence at a late
delivery, and elsewhere the choices that commit no value and send only for the
event at the player's own turn. Their success continuation is the agent's
continuation value; every other choice is compared with a late option, a
source deviation, the prescribed component, or has no gain. -/
def onePacketCompared (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  (LateDelivery setup leaks who site.1 → choice.1 = some ⟨none⟩) ∧
    ∀ response, choice.1 = some response → CommitsNoValue setup leaks response ∧
      ∀ event, (runtime setup).submittedEvent? leaks response = some event →
        ∃ past view, site.1 = some (past, view) ∧
          view.application.publicView.ownTurn? who = some event

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- At a decision input, every choice is some response of the one-packet menu. -/
theorem choice_response {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (onePacketN).Choice who site.1) :
    ∃ response, choice.1 = some response ∧
      response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := choice.2
  exact ⟨action, actionEq, member⟩


variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **One packet per event.** At every history of the default runtime, a
response of the one-packet menu transmitting for an event is sent before the
recall has submitted for that event. -/
theorem onePacket_unrecorded_of_member {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who))
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    (runtime setup).eventRecorded leaks (control.execution.recall who) event = false := by
  let app := application setup leaks
  cases recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨_, sent⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mp member
      rcases sent with silent | ⟨material, transmits, permitted⟩
      · unfold EventGraphRuntime.submittedEvent? at submitted
        rw [silent] at submitted
        cases submitted
      · have named : material.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at submitted
          rw [transmits] at submitted
          exact submitted
        have recalled := (runtime setup).countRecall_history leaks trace
        rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
          recalled.2.1 who material, countPermits_eq_true_iff] at permitted
        obtain ⟨entry, entryMember, entrySubmitted⟩ :=
          ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
        obtain ⟨entryMaterial, entryTransmits⟩ : ∃ entryMaterial,
            entry.action.transmission = some entryMaterial := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          cases transmission : entry.action.transmission with
          | none => rw [transmission] at entrySubmitted; cases entrySubmitted
          | some entryMaterial => exact ⟨entryMaterial, rfl⟩
        have entryNamed : entryMaterial.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at entrySubmitted
          rw [entryTransmits] at entrySubmitted
          exact entrySubmitted
        obtain ⟨message, emitted, call⟩ :=
          ((transmissionsEmitted_serviceInvariant scheduler).history (initialLaw setup) horizon
            (fun _ _ _ entry member => (List.not_mem_nil member).elim) trace) who entry
            entryMember entryMaterial entryTransmits
        have output : message ∈ app.outputs (control.execution.recall who) :=
          List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
        have earlier := earlierOwnPacket_of_output trace who
          (app.packet (app.submit control.execution.application who material) who
            (control.execution.network.known who) material) message output
        apply permitted.2.2 message earlier
        change message.payload.call.event? (graph setup) =
          material.call.packet.event? (graph setup)
        rw [call, entryNamed, named]

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **A submission for the turn's event leaves it pending.** At a site whose
view has `event` as the player's turn, if some choice submits for `event`, then
`event` is pending: the one-packet menu sends for an event only before the
recall has submitted for it. -/
theorem pendingEvent_of_turnSubmission {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response)
    (submitted : (runtime setup).submittedEvent? leaks response = some event) :
    pendingEvent setup leaks who site.1 = some event := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨offered, offeredEq, member⟩ := choice_response setup leaks bounds horizon scheduler
    site atSite choice
  rw [selected, Option.some.injEq] at offeredEq
  rw [← offeredEq] at member
  obtain ⟨⟨start, observed⟩, _⟩ := site.2
  have observedState : (application setup leaks).observe who start.state =
      some (past, view) :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans
      (observed.trans atSite)
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at observedState
    cases observedState
  rw [startState] at observedState
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    cases observedState
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
    at observedState
  obtain ⟨rfl, rfl⟩ := observedState
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (startState ▸ start.trace)
  rw [atSite]
  exact pendingEvent_of_spec turn
    (onePacket_unrecorded_of_member rawTrace who event response member submitted)

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- A transmitting response of the one-packet menu names an event. -/
theorem submittedEvent_of_transmits {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) :
    ∃ event, (runtime setup).submittedEvent? leaks response = some event := by
  unfold EventGraphRuntime.submittedEvent?
  rw [sends]
  cases packet : material.call.packet with
  | commitment event _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | opening event _ _ => exact ⟨event, by simp only [packet, Payload.event?]⟩
  | malformed raw => exact (onePacket_not_malformed bounds member sends raw packet).elim

/-- A choice at a site transmits a packet for the event at the player's own
turn. -/
def CommitsAtTurn (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  ∃ past view response event, site.1 = some (past, view) ∧ choice.1 = some response ∧
    (runtime setup).submittedEvent? leaks response = some event ∧
    view.application.publicView.ownTurn? who = some event

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Commitments away from the turn are owed failures.** For a well-formed
setup, at every history of a site, a choice transmitting a packet for an event
that is not the player's own turn leaves the player owing a failure at the
decoded point: a readiness token is issued only once all earlier events have
completed. -/
theorem owes_of_not_commitsAtTurn (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketN).InformationSite who) (choice : (onePacketN).Choice who site.1)
    (offTurn : ¬ CommitsAtTurn setup leaks bounds horizon scheduler who site choice)
    {response : (application setup leaks).Action} (chosen : choice.1 = some response)
    {event : (graph setup).EventId}
    (submitted : (runtime setup).submittedEvent? leaks response = some event)
    (history : (onePacketN).InformationHistory who site.1) :
    DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.1.state := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : app.observe who fullHistory.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who fullHistory.trace).symm.trans infoEq
  have menuTrace := fullHistory.trace
  change DecodedState setup leaks profile _ fullHistory.state
  generalize fullHistory.state = state at observed menuTrace
  rcases state with _ | ⟨remaining, actor, execution⟩
  · obtain ⟨info, decision⟩ := site
    change none = info at observed
    subst observed
    have legal := choice.2
    change choice.1 ∈ ({none} : Set _) at legal
    rw [chosen] at legal
    cases legal
  by_cases active : actor = some who
  swap
  · obtain ⟨info, decision⟩ := site
    simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
    change none = info at observed
    subst observed
    have legal := choice.2
    change choice.1 ∈ ({none} : Set _) at legal
    rw [chosen] at legal
    cases legal
  subst active
  have atSite : site.1 = some (execution.recall who, execution.observe app who) := by
    rw [← observed]
    simp [ReactiveApplication.observe]
  obtain ⟨rank, ⟨residual⟩, _⟩ := decodedState_intended_or_owes wellFormed profile menu horizon
    scheduler menuTrace _ rfl
  have legal := choice.2
  obtain ⟨info, decision⟩ := site
  change info = _ at atSite
  subst atSite
  obtain ⟨action, member, actionEq⟩ := legal
  rw [chosen] at actionEq
  cases Option.some.inj actionEq
  rcases onePacket_submission_atTurn bounds profile
      (menu.toRawTrace (initialLaw setup) horizon scheduler menuTrace) residual response member
      event submitted with turn | owes
  · exact (offTurn ⟨_, _, response, event, rfl, chosen, submitted, turn⟩).elim
  · exact ⟨rank, ⟨residual⟩, owes⟩

/-- A site at which `who` owes no failure at the decoded point of any history. -/
def SiteDebtFree {who : Player} (site : (onePacketN).InformationSite who) : Prop :=
  ∀ history : (onePacketN).InformationHistory who site.1,
    ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point

omit [Finite setup.intendedProtocol.History] in
/-- The site of an agent owing no failure is debt free. -/
theorem siteDebtFree_of_not_owing {who : Player} {site : (onePacketN).InformationSite who}
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) :
    SiteDebtFree setup leaks bounds horizon scheduler site :=
  fun history point decoded owes => notOwing ⟨history, point, decoded, owes⟩

open Classical in
/-- **The honest counterparts at one site** along a source sequence and a
target sequence: a tremble scale negligible against a floor to a depth, and at
every stage an honest counterpart of each history at which another player
responded irregularly, reached at least the floor to the depth times the square
of the scale as often as the irregular history up to the cube of the scale. -/
structure OnePacketCounterpartInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) where
  /-- The tremble scale of irregular histories. -/
  scale : ℕ → ℝ
  /-- The floor of honest masses. -/
  floors : ℕ → ℝ
  /-- The depth of the floor. -/
  depth : ℕ
  /-- The slack of the honest counterparts. -/
  slack : ℝ
  floors_pos : ∀ n, 0 < floors n
  scale_nonneg : ∀ n, 0 ≤ scale n
  negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0)
  slack_nonneg : 0 ≤ slack
  /-- The honest counterpart of each irregular history at each stage. -/
  counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
    (onePacketN).InformationHistory who site.1
  /-- The weight common to an irregular history and its counterpart. -/
  commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ
  counterpart_regular : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      (counterpart n history).1.trace
  irregular_le : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
      who history.1.trace →
    ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
      scale n ^ 3 * commonWeight n history
  counterpart_ge : ∀ n history, ¬ RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    scale n ^ 2 * floors n ^ depth * commonWeight n history ≤
      slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
        (counterpart n history).1).toReal

open Classical in
/-- **The own and replay inputs at one own-turn site** along a source sequence
and a target sequence: operational steps for the target profiles, and at every
stage the intended own completions of regular histories and the common fibers
of the replay projection. -/
structure OnePacketOwnInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1) where
  /-- Operational steps of the target profiles. -/
  steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    (fun n => (targetSequence n).strategy) who
  /-- Own completions along regular histories decode to intended actions. -/
  ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
    OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
      history.1.trace
  /-- The common operational mass of the fibers at each stage. -/
  fiberMass : ℕ → ℝ
  fiber : ∀ n point, ∑ history with RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace ∧
      replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
        history = point,
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler history.1.trace) = fiberMass n

/-- **The forced-belief inputs at one own-turn site** along a source sequence
and a target sequence: the honest counterparts of irregular histories, and the
own and replay inputs. -/
structure OnePacketBeliefInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1) extends
    OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence site,
    OnePacketOwnInputs setup leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected

omit [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Beliefs converge at an own-turn site.** For a well-formed setup, at a
forced site of `who` at its own turn whose projected view is an intended site,
along a fully mixed Bayes source sequence and a fully mixed Bayes target
sequence with the forced-belief inputs, the native belief pushed forward along
the replay projection approaches the intended belief in `ℓ¹`. -/
theorem onePacket_beliefConverges (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup leaks who site.1)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (inputs : OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence
      site sourceSite decision projected) :
    Tendsto (fun n => ∑' point,
      |((((targetSequence n).belief who site).map
          (replayProjection setup leaks bounds horizon scheduler sourceSite site decision
            projected)) point).toReal -
        ((sequence n).belief who sourceSite point).toReal|) atTop (nhds 0) := by
  classical
  let := Fintype.ofFinite (setup.intendedModel.InformationHistory who sourceSite.1)
  simp only [tsum_fintype]
  exact tendsto_projectedBelief_sub
    (fun n => ForcedBeliefInputs.ofRegularHistories (n := n) wellFormed forced decision turn
      projected (sourceMixed n) (inputs.ownIntended n) (inputs.fiberMass n) (inputs.fiber n)
      (inputs.counterpart n) (inputs.commonWeight n) (inputs.counterpart_regular n)
      (inputs.irregular_le n) (inputs.counterpart_ge n))
    decision (fun _ => rfl) mixed bayes sourceMixed sourceBayes inputs.floors_pos
    inputs.scale_nonneg inputs.negligible inputs.slack_nonneg

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Irregular histories vanish at a site with honest counterparts.** Along a
fully mixed Bayes target sequence, the belief mass of the histories at which
another player responded irregularly vanishes when each has an honest
counterpart reached more often by a factor the tremble scale over the floor to
the depth makes negligible. -/
theorem onePacket_irregularVanishes {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    (inputs : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace
      then (0 : ℝ) else 1)) atTop (nhds 0) := by
  let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
  have limit := tendsto_irregularRatio (slack := inputs.slack) inputs.negligible
    (Fintype.card ((onePacketN).InformationHistory who site.1))
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) limit
  rw [expect_eq_sum]
  have bound := sum_belief_le_of_counterpart
    (fun history : (onePacketN).InformationHistory who site.1 =>
      ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace)
    (inputs.counterpart n) (bayes n)
    (InformationModel.informationMass_pos_of_fullSupport _ _ (mixed n) who site)
    (div_nonneg (mul_nonneg inputs.slack_nonneg (inputs.scale_nonneg n))
      (pow_nonneg (inputs.floors_pos n).le _))
    (fun history irregular => not_not.mpr (inputs.counterpart_regular n history irregular))
    (fun history irregular => le_mul_of_tremble_counterpart (inputs.scale_nonneg n)
      (inputs.floors_pos n) (inputs.irregular_le n history irregular)
      (inputs.counterpart_ge n history irregular))
  refine le_trans (le_of_eq ?_) bound
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun history _ => ?_
  split_ifs <;> simp

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Histories outside the forced region vanish at a forced site.** Along a
fully mixed Bayes target sequence, at a forced decision input with honest
counterparts, the belief mass of the histories outside the forced region
vanishes when the owner's own completions along regular histories are
intended: such a regular history is in a forced state
(`Vegas.forcedState_of_regular`), and irregular histories vanish
(`Vegas.onePacket_irregularVanishes`). -/
theorem onePacket_unforcedVanishes (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (counterparts : OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence
      targetSequence site)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1)) atTop (nhds 0) := by
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) (onePacket_irregularVanishes setup leaks bounds horizon scheduler mixed bayes
      counterparts)
  refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  by_cases regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
    history.1.trace
  · have inForced := forcedState_of_regular wellFormed (sequence n) decision forced history
      regular (ownIntended n history regular)
    simp only [inForced, regular, ↓reduceIte, le_refl]
  · simp only [regular, ↓reduceIte]
    split <;> norm_num

omit [Finite setup.intendedProtocol.History] in
/-- A function bounded by `bound` has expectations under two laws on a finite
type within `bound` times their `ℓ¹` distance. -/
theorem expect_sub_le_of_bounded {α : Type*} [Finite α] (first second : PMF α) (value : α → ℝ)
    {bound : ℝ} (bounded : ∀ point, |value point| ≤ bound) :
    expect first value - expect second value ≤
      bound * ∑' point, |(first point).toReal - (second point).toReal| := by
  let := Fintype.ofFinite α
  rw [tsum_fintype, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun point _ => ?_
  rw [← sub_mul]
  calc _ ≤ |((first point).toReal - (second point).toReal) * value point| := le_abs_self _
    _ = |(first point).toReal - (second point).toReal| * |value point| := abs_mul _ _
    _ ≤ _ := by
        rw [mul_comm bound]
        exact mul_le_mul_of_nonneg_left (bounded point) (abs_nonneg _)

/-- The local gain at a site of the one-packet game of installing a law: the
expected exclusion payoff of the deviation minus that of the assessment. -/
def onePacketSiteGain (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) : ℝ :=
  let comparison := (onePacketN).assessmentComparisonWith
    ((onePacketN).truncatedRunner (2 * horizon + 1))
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) assessment who (site, (assessment.strategy who).withLaw site.1 law)
  expect comparison.alternative ((payoffComponent setup) · who) -
    expect comparison.prescribed ((payoffComponent setup) · who)

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **A late delivery decides its pending event.** At a decision input of `who`
with pending event `event`, along a history whose recall of `who` is the
input's, the late-delivery key decides `event`. -/
theorem decidedEvent_eq_of_pending {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key) :
    decidedEvent key = some event := by
  obtain ⟨turn, _, owned, unrecorded⟩ := pendingEvent_spec pending
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst ownerEq
      unfold decidedEvent
      rw [turnEvent_of_publicationTurn ⟨turn, payload, binding, checks, outputEq, codeEq, node⟩]
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((EventGraph.actor?_of_outputLayout_binding _ outputEq).symm.trans
          owned)
      subst ownerEq
      have noPublication : turnEvent (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } = none := by
        cases found : turnEvent (setup := setup) (leaks := leaks) _ with
        | none => rfl
        | some other =>
            obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent found
            have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
            subst same
            rw [node] at otherNode
            cases otherNode
      have unsent : UnsentFor (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } event := by
        intro recalledEntry member message emitted named
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        have recorded := (history_eventRecorded_iff trace owner event).mpr
          ⟨message, by
            rw [recallEq]
            exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
        rw [recallEq, unrecorded] at recorded
        cases recorded
      have binding : BindingTurn (setup := setup) (leaks := leaks)
          { owner := owner, current := operationalView setup leaks view,
            recalled := past.map fun entry =>
              (operationalView setup leaks entry.beforeView, entry.emitted),
            delivered := deliveredValue setup leaks owner view } event payload :=
        ⟨turn, ⟨outputEq, codeEq, node⟩, unsent⟩
      unfold decidedEvent
      rw [noPublication]
      cases found : bindingTurn (setup := setup) (leaks := leaks) _ with
      | none =>
          unfold bindingTurn at found
          split at found
          · cases found
          · rename_i noTurn
            exact (noTurn ⟨(event, payload), binding⟩).elim
      | some decided =>
          obtain ⟨decidedTurn, _, _⟩ := bindingTurn_spec found
          exact congrArg some (Option.some.inj (decidedTurn.symm.trans turn))

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- Along a history, the owner has sent nothing for an event exactly when its
recall has not recorded the event. -/
theorem unsentFor_iff_unrecorded {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key)
    (event : (graph setup).EventId) :
    UnsentFor key event ↔ (runtime setup).eventRecorded leaks past event = false := by
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  constructor
  · intro unsent
    apply Bool.eq_false_of_not_eq_true
    intro recorded
    rw [← recallEq] at recorded
    obtain ⟨message, member, named⟩ := (history_eventRecorded_iff trace who event).mp recorded
    rw [recallEq] at member
    obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
    exact unsent _ (List.mem_map_of_mem entryMember) message emitted named
  · intro unrecorded recalledEntry member message emitted named
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    have recorded := (history_eventRecorded_iff trace who event).mpr
      ⟨message, by
        rw [recallEq]
        exact List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩, named⟩
    rw [recallEq, unrecorded] at recorded
    cases recorded

/-- The failure expectation of `fuel` steps of a lumping's image kernel from the
image read off an operational record. -/
def lumpedFailure {assessment : (onePacketN).BehavioralAssessment} {who : Player}
    {LateOption : Type}
    {profileOf : (onePacketN).InformationSite who → LateOption → ∀ player,
      (onePacketN).BehavioralPolicy player}
    {failedState : LateKey setup leaks → (application setup leaks).ProtocolState → Prop}
    {relevant : (onePacketN).InformationSite who → Prop}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn assessment who relevant profileOf failedState δ Y)
    (fuel : Nat) (key : LateKey setup leaks) (option : LateOption)
    (record : List (Option (OperationalState setup leaks))) : ℝ :=
  expect ((fun law => law.bind (lumping.kernel key option))^[fuel]
    (PMF.pure (lumping.start key record))) (lumping.failure key)

/-- The intended site at the projected view of a site, when that view is an
intended decision site. -/
def projectedSite {who : Player} {info : (application setup leaks).Info}
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who info)) :
    setup.intendedModel.InformationSite who :=
  ⟨projectView setup leaks who info, decision⟩

open Classical in
/-- The options of the certificate's lumping at a late key: the installed option
at the key, and the key's weights at every other key. -/
def certificateOptions {slots : Nat}
    (weights : ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (key : LateKey setup leaks) (option : LateOption slots) (other : LateKey setup leaks) :
    PMF (LateOption slots) :=
  if other = key then PMF.pure option
  else keyWeights setup leaks bounds horizon scheduler weights (some other)

omit [Finite setup.intendedProtocol.History] in
/-- **The certificate's components at forced decisions.** At a history in a
forced state of `who` acting at a decision with an event ready that `who` was
activated for, a profile assembled from the certificate's components plays the
late component of the key's weights while `who` has not sent for the event, and
the slot-trembled prescribed component once it has. -/
theorem certificate_strategyShape (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (forcedState : ForcedState setup leaks who history.state)
    (ready : execution.application.config.cut.Ready event)
    (activated : ∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry) :
    ((runtime setup).eventRecorded leaks (execution.recall who) event = false →
      (targetSequence n).strategy who
          (some (execution.recall who, execution.observe (application setup leaks) who)) =
        slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) who
          (some (execution.recall who, execution.observe (application setup leaks) who))
          ((keyWeights setup leaks bounds horizon scheduler (weights n)
              (some (LateKey.ofView setup leaks who (execution.recall who)
                (execution.observe (application setup leaks) who)))).bind
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who, execution.observe (application setup leaks) who))))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
            (some (execution.recall who, execution.observe (application setup leaks) who))))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
            (some (execution.recall who, execution.observe (application setup leaks) who)))) ∧
    ((runtime setup).eventRecorded leaks (execution.recall who) event = true →
      ∃ main : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
          scheduler).Choice who (some (execution.recall who,
            execution.observe (application setup leaks) who))),
        (main = honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
            (sequence n) who (some (execution.recall who,
              execution.observe (application setup leaks) who)) ∨
          ∃ others : PMF (LateOption slots), main = others.bind
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who,
                execution.observe (application setup leaks) who)))) ∧
        (targetSequence n).strategy who (some (execution.recall who,
            execution.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scale n)
            (scale_pos n).le (scale_le_one n) who (some (execution.recall who,
              execution.observe (application setup leaks) who)) main
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
              who (some (execution.recall who,
                execution.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
              (some (execution.recall who,
                execution.observe (application setup leaks) who)))) := by
  have observed : (onePacketN).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    refine ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
      scheduler who history.trace).trans ?_
    rw [current]
    simp [ReactiveApplication.observe]
  have running : ¬ (onePacketProtocol setup leaks bounds horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, actorNone⟩
    cases actorNone
  have played := (onePacketN).mem_playedInformation (who := who) running
  rw [observed] at played
  have forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who (some (execution.recall who,
        execution.observe (application setup leaks) who)) :=
    observed ▸ forcedAgent_of_history history forcedState
  let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
    ⟨who, ⟨_, played⟩⟩
  have notFree : ¬ FreeAgent setup leaks bounds horizon scheduler agent :=
    fun unforced => unforced forced
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup leaks bounds horizon scheduler agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
        (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) agent
  obtain ⟨entry, member, activatedAt⟩ := activated
  have owned : (graph setup).actor? event = some who :=
    (PublicView.ownTurn?_spec _ who event activatedAt).2
  have turn : execution.application.publicView.ownTurn? who = some event :=
    ownTurn?_of_ready setup execution.application ready owned
  constructor
  · intro unrecorded
    have late : LateDelivery setup leaks who (some (execution.recall who,
        execution.observe (application setup leaks) who)) :=
      ⟨_, _, event, rfl, pendingEvent_of_spec turn unrecorded, entry, member, activatedAt⟩
    have keyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      ⟨late, notFree⟩
    have weightsEq : keyWeights setup leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who))) =
        weights n (.inr (some ⟨agentLateKey setup leaks bounds (initialLaw setup) horizon
          scheduler agent, ⟨agent, keyed⟩, rfl⟩)) := by
      have present : some (LateKey.ofView setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who)) ∈ Set.range
            fun agent : {agent : (onePacketN).InformationAgent (onePacketN).playedInformation //
              ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
                (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
                  agent} =>
            agentLateKey setup leaks bounds (initialLaw setup) horizon scheduler agent.1 :=
        ⟨⟨agent, keyed⟩, rfl⟩
      unfold keyWeights
      rw [dite_eq_left_of_eq_true (eq_true present)]
      rfl
    have mixture := freeKeyedMixture_of_keyed (key := agentLateKey setup leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture, weightsEq]
    exact bind_lateComponent setup leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) _ (scale n) (scale_pos n).le (scale_le_one n) who _
  · intro recorded
    have notLate : ¬ LateDelivery setup leaks who (some (execution.recall who,
        execution.observe (application setup leaks) who)) := by
      rintro ⟨_, _, other, same, pending, _⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      obtain ⟨otherTurn, _, _, unrecorded⟩ := pendingEvent_spec pending
      have sameEvent : other = event := Option.some.inj (otherTurn.symm.trans turn)
      subst sameEvent
      rw [recorded] at unrecorded
      cases unrecorded
    have unkeyed : ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler) agent :=
      fun keyed => notLate keyed.1
    have mixture := freeKeyedMixture_of_not_keyed (key := agentLateKey setup leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup leaks bounds horizon scheduler scale scale_pos scale_le_one n)
      (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree unkeyed
    refine ⟨_, Or.inl rfl, ?_⟩
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture]
    rfl

/-- **The owner's debt is clear at an event.** The event has completed, or it is
ready and the owner owes no failure at the decoded point. -/
def DebtClear (who : Player) (event : (graph setup).EventId) :
    (application setup leaks).ProtocolState → Prop
  | none => True
  | some control => event ∈ control.execution.application.config.cut.completed ∨
      (control.execution.application.config.cut.Ready event ∧
        ∀ point, decodedPoint setup control.execution.application.config = some point →
          ¬ ProtocolState.OwesFailure who setup.program point)

/-- The event of the owner's turn at an information state, if any. -/
def siteTurnEvent (who : Player) : (application setup leaks).Info → Option (graph setup).EventId
  | none => none
  | some (_, view) => view.application.publicView.ownTurn? who

/-- **States through a debt-free site.** States consistent with a site at which
the owner's debt is clear at the site's turn event. -/
def SiteThrough (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  SiteConsistent who info state ∧
    ∀ event, siteTurnEvent setup leaks who info = some event → DebtClear setup leaks who event state

/-- **The activation past a site.** At a state whose owner's recall extends the
site's, the first entry past the site's recall was taken at a view showing the
site's pending event as the owner's turn. -/
def SiteActivated (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  ∀ control, state = some control → ∀ entry rest,
    control.execution.recall who = infoRecall info ++ entry :: rest →
      ∀ event, pendingEvent setup leaks who info = some event →
        ActivatedAt setup leaks who event entry

/-- The site is a late delivery, or play past it recalls the activation of its
pending event. -/
def ActivationTracked (who : Player) (info : (application setup leaks).Info)
    (state : (application setup leaks).ProtocolState) : Prop :=
  LateDelivery setup leaks who info ∨ SiteActivated setup leaks who info state

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The control step appends to the recall of an acting player one entry taken at
its current view, and keeps every other player's recall. -/
theorem controlStep_recall_entry (players : Player → (application setup leaks).Policy)
    (control : (application setup leaks).Control) {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players (some control)).support) (who : Player) :
    ∃ control', next = some control' ∧
      (control.actor = some who → ∃ entry : (application setup leaks).PlayerEntry,
        entry.beforeView = control.execution.observe (application setup leaks) who ∧
          control'.execution.recall who = control.execution.recall who ++ [entry]) ∧
      (control.actor ≠ some who →
        control'.execution.recall who = control.execution.recall who) := by
  rcases control with ⟨remaining, actor, execution⟩
  unfold ReactiveApplication.controlStep at member
  cases actor with
  | none =>
      have idle : (none : Option Player) ≠ some who := fun same => by cases same
      cases remaining with
      | zero =>
          exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member, fun acting => (idle acting).elim,
            fun _ => rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨next', supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, fun acting => (idle acting).elim, fun _ => congrFun
            ((application setup leaks).environmentStep_recall execution next' command supported)
            who⟩
  | some actor =>
      simp only [ReactiveApplication.actor, Option.bind_some] at member
      rw [PMF.mem_support_bind_iff] at member
      obtain ⟨action, _, reached⟩ := member
      refine ⟨_, (PMF.mem_support_pure_iff _ _).mp reached, ?_, ?_⟩
      · intro acting
        cases Option.some.inj acting
        simp only [↓reduceIte, Option.getD_some, ReactiveApplication.Execution.respond]
        rcases action with ⟨_ | _⟩ <;> exact ⟨_, rfl, rfl⟩
      · intro idle
        have different : who ≠ actor := fun same => idle (by rw [same])
        simp only [↓reduceIte, Option.getD_some]
        exact (application setup leaks).respond_recall_other execution actor who different _

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The activation stays tracked along play.** A control step from a state
consistent with a site keeps the activation of its pending event tracked: the
first entry past the site's recall is taken at the site's own view. -/
theorem activationTracked_step (players : Player → (application setup leaks).Policy)
    (who : Player) (info : (application setup leaks).Info)
    {state : (application setup leaks).ProtocolState} (consistent : SiteConsistent who info state)
    (tracked : ActivationTracked setup leaks who info state)
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players state).support) :
    ActivationTracked setup leaks who info next := by
  rcases tracked with late | activated
  · exact Or.inl late
  right
  cases state with
  | none => exact consistent.elim
  | some control =>
      obtain ⟨control', rfl, acted, idle⟩ := controlStep_recall_entry setup leaks horizon
        scheduler players control member who
      intro other otherEq entry rest recallEq event pending
      have same := Option.some.inj otherEq
      subst same
      rcases consistent with ⟨isSome, atSite⟩ | ⟨first, earlier, longer⟩
      · have acting : control.actor = some who := by
          by_contra notActing
          simp only [ReactiveApplication.observe, notActing, ↓reduceIte] at atSite
          rw [← atSite] at isSome
          cases isSome
        obtain ⟨added, before, appended⟩ := acted acting
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at atSite
        subst atSite
        rw [appended] at recallEq
        change control.execution.recall who ++ [added] =
          control.execution.recall who ++ entry :: rest at recallEq
        obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
        unfold ActivatedAt
        rw [before]
        exact (pendingEvent_spec (setup := setup) pending).1
      · have activatedFirst := activated _ rfl first earlier longer event pending
        by_cases acting : control.actor = some who
        · obtain ⟨added, _, appended⟩ := acted acting
          rw [appended, longer, List.append_assoc, List.cons_append] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst
        · rw [idle acting, longer] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The histories of a site track the activation of its pending event: their
owner's recall is the site's. -/
theorem siteActivated_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (history : (onePacketN).InformationHistory who site.1) :
    SiteActivated setup leaks who site.1 history.1.state := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = site.1
    at seen
  rw [onePacket_infoOf] at seen
  intro control current entry rest recallEq event pending
  change state = some control at current
  rw [current] at seen
  by_cases acting : control.actor = some who
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at recallEq
    change control.execution.recall who = control.execution.recall who ++ entry :: rest
      at recallEq
    have lengths := congrArg List.length recallEq
    simp at lengths
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at pending
    cases pending

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Debt stays clear along play.** A control step from an initialized state
keeps the owner's debt clear at an event: the configuration is unchanged, or the
one ready event completes, so a ready event either stays ready with the same
decoded point or completes. -/
theorem debtClear_step (players : Player → (application setup leaks).Policy)
    (who : Player) (event : (graph setup).EventId) {control : (application setup leaks).Control}
    (clear : DebtClear setup leaks who event (some control))
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      players (some control)).support) :
    DebtClear setup leaks who event next := by
  obtain ⟨control', rfl, step⟩ := controlStep_configStep (horizon := horizon)
    (scheduler := scheduler) players control member
  change control'.execution.application.config = control.execution.application.config ∨ _
    at step
  rcases step with same | ⟨completed, completedReady, action, completedMember⟩
  · change event ∈ control'.execution.application.config.cut.completed ∨ _
    rw [same]
    exact clear
  · change event ∈ control'.execution.application.config.cut.completed ∨ _
    left
    rw [control.execution.application.config.step_cut completed completedReady action _
      completedMember, EventOrder.Cut.mem_complete]
    rcases clear with done | ⟨ready, _⟩
    · exact Or.inr done
    · exact Or.inl (setup.eventGraph.sequentialize_ready_unique _ ready completedReady)

open Classical in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The site shape of an installed late component, through the site.** Let a
predicate of states refine consistency with a site, and let the activation of
the site key's turn events be recalled at the predicate's states past the site.
Suppose a profile plays, at the site, the late component of an option, and
elsewhere a strategy of the owner that, at the predicate's forced states where
such a turn event is ready and activated, plays the late component of its keyed
weights while the event is unrecorded, and a component whose main part is the
as-if-honest choice or a mixture of late options once it is recorded. Then the
profile has the site shape on the predicate, with the installed option at the
site's key and the keyed weights at every other key. -/
theorem siteComponentShape_of_installed_within
    (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat} {who : Player}
    (site : (onePacketN).InformationSite who)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (weights : LateKey setup leaks → PMF (LateOption slots))
    (profile : ∀ player, (onePacketN).BehavioralPolicy player)
    (strategy : (onePacketN).BehavioralPolicy who)
    (allowed : (application setup leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent who site.1 state)
    (installed : profile who site.1 =
      slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who site.1
        ((PMF.pure option).bind (lateChoice setup leaks bounds (initialLaw setup) horizon
          scheduler assessment who site.1))
        (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          site.1))
        (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
          site.1))
    (away : ∀ info, info ≠ site.1 → profile who info = strategy info)
    (activated : ∀ event, (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
      ∀ (remaining : Nat) (execution : (application setup leaks).Execution),
        allowed (some ⟨remaining, some who, execution⟩) →
        (∃ entry rest, execution.recall who = infoRecall site.1 ++ entry :: rest) →
          ∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry)
    (strategyShape : ∀ (history : (onePacketProtocol setup leaks bounds horizon
        scheduler).History) (remaining : Nat) (execution : (application setup leaks).Execution)
        (event : (graph setup).EventId),
      (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
      history.state = some ⟨remaining, some who, execution⟩ →
      allowed history.state →
      ForcedState setup leaks who history.state →
      execution.application.config.cut.Ready event →
      (∃ entry ∈ execution.recall who, ActivatedAt setup leaks who event entry) →
      ((runtime setup).eventRecorded leaks (execution.recall who) event = false →
        strategy (some (execution.recall who, execution.observe (application setup leaks) who)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one who (some (execution.recall who,
              execution.observe (application setup leaks) who))
            ((weights (LateKey.ofView setup leaks who (execution.recall who)
                (execution.observe (application setup leaks) who))).bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who, execution.observe (application setup leaks) who))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
              (some (execution.recall who, execution.observe (application setup leaks) who))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
              (some (execution.recall who, execution.observe (application setup leaks) who)))) ∧
      ((runtime setup).eventRecorded leaks (execution.recall who) event = true →
        ∃ main : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
            scheduler).Choice who (some (execution.recall who,
              execution.observe (application setup leaks) who))),
          (main = honestChoice setup leaks bounds (initialLaw setup) horizon scheduler
              assessment who (some (execution.recall who,
                execution.observe (application setup leaks) who)) ∨
            ∃ others : PMF (LateOption slots), main = others.bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who)))) ∧
          strategy (some (execution.recall who,
              execution.observe (application setup leaks) who)) =
            slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
              nonnegative le_one who (some (execution.recall who,
                execution.observe (application setup leaks) who)) main
              (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
                who (some (execution.recall who,
                  execution.observe (application setup leaks) who))))
              (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
                (some (execution.recall who,
                  execution.observe (application setup leaks) who))))) :
    SiteComponentShape assessment scale nonnegative le_one
      (fun other => if other = key then PMF.pure option else weights other) key profile
      allowed := by
  have ownerEq : key.owner = who := owner_of_lateKey siteKey
  subst ownerEq
  intro event turn history remaining execution current allowedState forced ready
  have consistent := within _ allowedState
  rw [current] at consistent
  by_cases atSite : (application setup leaks).observe key.owner
      (some ⟨remaining, some key.owner, execution⟩) = site.1
  · have infoEq : site.1 = some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) := by
      rw [← atSite]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyEq : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) = key := by
      rw [infoEq] at siteKey
      exact Option.some.inj siteKey
    rw [infoEq] at installed
    constructor
    · intro _
      rw [installed]
      beta_reduce
      rw [keyEq]
      simp only [↓reduceIte]
    · intro _
      exact ⟨_, Or.inr ⟨PMF.pure option, rfl⟩, installed⟩
  · have notSite : some (execution.recall key.owner,
        execution.observe (application setup leaks) key.owner) ≠ site.1 := by
      intro same
      apply atSite
      rw [← same]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyNe : LateKey.ofView setup leaks key.owner (execution.recall key.owner)
        (execution.observe (application setup leaks) key.owner) ≠ key := fun same =>
      atSite (siteConsistent_key siteKey consistent same)
    have longer : ∃ entry rest, execution.recall key.owner =
        infoRecall site.1 ++ entry :: rest := by
      rcases consistent with ⟨_, sameInfo⟩ | longer
      · exact (atSite sameInfo).elim
      · exact longer
    have recalledActivation := activated event turn remaining execution
      (current ▸ allowedState) longer
    have shapes := strategyShape history remaining execution event turn current allowedState
      forced ready recalledActivation
    rw [away _ notSite]
    beta_reduce
    simp only [keyNe, ↓reduceIte]
    exact shapes

omit [Finite setup.intendedProtocol.History] in
/-- **The site shape of the certificate at a pending site.** At a late delivery
or first activation of `who`, the profile installing a late option at the site
and otherwise following a profile assembled from the certificate's components
has the site shape over a predicate of states consistent with the site that
tracks the activation of its pending event, with the installed option at the
site's key and the key weights elsewhere. -/
theorem certificate_siteComponentShape_of_pending
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (option : LateOption slots) (allowed : (application setup leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent who site.1 state)
    (tracked : ∀ state, allowed state → ActivationTracked setup leaks who site.1 state) :
    SiteComponentShape (sequence n) (scale n) (scale_pos n).le (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      allowed := by
  obtain ⟨past, view, pendingEvent', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  have turn : view.application.publicView.ownTurn? who = some pendingEvent' := by
    have pendingHere := pending
    rw [atSite] at pendingHere
    exact (pendingEvent_spec pendingHere).1
  refine siteComponentShape_of_installed_within setup leaks bounds horizon scheduler (sequence n)
    (scale n) (scale_pos n).le (scale_le_one n) site siteKey option
    (fun other => keyWeights setup leaks bounds horizon scheduler (weights n) (some other))
    _ ((targetSequence n).strategy who) allowed within ?_ ?_ ?_ ?_
  · rw [Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_bind]
    rfl
  · intro info different
    rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ different]
  · intro event decided remaining execution allowedState longer
    have keyTurn : key.current.1.ownTurn? key.owner = some event := by
      rcases decided with publication | ⟨payload, binding⟩
      · exact publication.1
      · exact binding.1
    have sameEvent : event = pendingEvent' := by
      rw [atSite] at siteKey
      simp only [lateKey, Option.some.injEq] at siteKey
      subst siteKey
      exact Option.some.inj (keyTurn.symm.trans turn)
    subst sameEvent
    obtain ⟨entry, rest, recallEq⟩ := longer
    rcases tracked _ allowedState with late | activated
    · obtain ⟨past', view', event', atSite', pending', earlier, member, activatedAt⟩ := late
      have sameEvent : event' = event := Option.some.inj (pending'.symm.trans pending)
      subst sameEvent
      refine ⟨earlier, ?_, activatedAt⟩
      rw [recallEq]
      exact List.mem_append_left _ (by rw [atSite']; exact member)
    · refine ⟨entry, ?_, activated _ rfl entry rest recallEq event pending⟩
      rw [recallEq]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
  · intro history remaining execution event _ current _ forcedState ready activated
    exact certificate_strategyShape setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence assembled n who history remaining execution event
      current forcedState ready activated

/-- The gain of a deviation at a site of the intended game under the exclusion
payoff: the expected exclusion payoff of the deviation minus that of the
assessment. -/
def intendedSiteGain (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (deviation : setup.intendedModel.AssessmentDeviation who) : ℝ :=
  let comparison := setup.intendedModel.assessmentComparisonWith
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff) assessment who deviation
  expect comparison.alternative ((payoffComponent setup) · who) -
    expect comparison.prescribed ((payoffComponent setup) · who)

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free pending site pass through it.** At a late
delivery or first activation whose owner owes no failure, every history of the
site's belief is at a state consistent with the site at which the owner's debt
is clear at the site's turn event. -/
theorem siteThrough_of_pendingHistory {who : Player} {site : (onePacketN).InformationSite who}
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup leaks who site.1 history.1.state := by
  refine ⟨siteConsistent_of_history siteKey history, fun event siteTurn => ?_⟩
  obtain ⟨past, view, pending', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  rw [atSite] at pending
  obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec (setup := setup) pending
  have sameEvent : pending' = event := by
    rw [atSite] at siteTurn
    exact Option.some.inj (turn.symm.trans siteTurn)
  subst sameEvent
  have notOwed := debtFree history
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup leaks bounds horizon scheduler).infoOf who trace = site.1
    at seen
  rw [onePacket_infoOf, atSite] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  exact Or.inr ⟨(State.publicView_eventReady _ pending').mp readyView, notOwed⟩


omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free late delivery pass through it**
(`Vegas.siteThrough_of_pendingHistory`). -/
theorem siteThrough_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup leaks who site.1 history.1.state :=
  siteThrough_of_pendingHistory setup leaks bounds horizon scheduler (Or.inl late) debtFree
    siteKey history

/-- **The certificate's lumping at debt-free pending sites.** For an assembled
sequence, at every stage and for every owner, the native kernel of the profiles
installing the late options lumps onto the decision image at late deliveries
and first activations at which the owner owes no failure, with drift twice the
cube of the scale. At a first activation the installed wait option is silence up
to the scale's trembles. Play from such a site stays at states consistent with
it at which the owner's debt is clear at the site's turn event
(`Vegas.debtClear_step`) and the activation of its pending event is recalled
(`Vegas.activationTracked_step`), and the installed profiles have the site shape
there (`Vegas.certificate_siteComponentShape_of_pending`). -/
def certificateLumping (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player) :
    PendingLumpingOn (targetSequence n) who
      (fun site => (LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1) ∧
        SiteDebtFree setup leaks bounds horizon scheduler site)
      (fun site option => Profile.update (sig := (onePacketN).behavioralSignature)
        (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      DecisionFailed (scale n ^ 3 + scale n ^ 3)
      (DecisionImage (setup := setup) (leaks := leaks)) :=
  have nonnegative := (scale_pos n).le
  onePacketLateLumpingOn (targetSequence n) who
    (fun site => (LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1) ∧
      SiteDebtFree setup leaks bounds horizon scheduler site) _
    (by have := pow_nonneg nonnegative 3; linarith) (pow_nonneg nonnegative 3)
    (by linarith) (openingKernel bounds horizon scheduler
      (fun key option => lateOpeningSilence bounds horizon scheduler (sequence n) (scale n)
        nonnegative (scale_le_one n)
        (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key))
    (fun key option => lateBindingMoves bounds horizon scheduler (scale n) nonnegative
      (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n) key option) key)
    (fun site state => SiteThrough setup leaks who site.1 state ∧
      ActivationTracked setup leaks who site.1 state)
    (fun _ relevant _ siteKey history _ _ =>
      ⟨siteThrough_of_pendingHistory setup leaks bounds horizon scheduler relevant.1 relevant.2
        siteKey history, Or.inr (siteActivated_of_history setup leaks bounds horizon scheduler
          history)⟩)
    (fun site _ _ state through next member => by
      refine ⟨?_, activationTracked_step setup leaks horizon scheduler _ who site.1 through.1.1
        through.2 member⟩
      cases state with
      | none => exact through.1.1.elim
      | some control =>
          exact ⟨siteConsistent_step _ who site.1 through.1.1 member, fun event siteTurn =>
            debtClear_step setup leaks horizon scheduler _ who event
              (through.1.2 event siteTurn) member⟩)
    (fun site relevant key siteKey option => ownerStepClose_of_openingLaw bounds _ key option _
      (ownerOpeningLaw_of_siteComponents (sequence n) covers (scale n) nonnegative
        (scale_le_one n) (certificateOptions setup leaks bounds horizon scheduler (weights n))
        key option _ _ (certificate_siteComponentShape_of_pending setup leaks bounds horizon
          scheduler sequence scale scale_pos scale_le_one weights targetSequence assembled n site
          relevant.1 siteKey option _ (fun _ through => through.1.1) fun _ through => through.2)))
    (fun site relevant key siteKey option => ownerBindingLaw_of_siteComponents (sequence n)
      covers capacity slotsLe (scale n) nonnegative (scale_le_one n)
      (certificateOptions setup leaks bounds horizon scheduler (weights n)) key option _ _
      (certificate_siteComponentShape_of_pending setup leaks bounds horizon scheduler sequence
        scale scale_pos scale_le_one weights targetSequence assembled n site relevant.1 siteKey
        option _ (fun _ through => through.1.1) fun _ through => through.2))

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- A late delivery is a decision input showing the player's own turn. -/
theorem lateDelivery_input {who : Player} {info : (application setup leaks).Info}
    (late : LateDelivery setup leaks who info) :
    ∃ input : List (application setup leaks).PlayerEntry × (application setup leaks).PlayerView,
      info = some input ∧ ∃ event, input.2.application.publicView.ownTurn? who = some event := by
  obtain ⟨past, view, event, atSite, pending, _⟩ := late
  rw [atSite] at pending
  exact ⟨(past, view), atSite, event, (pendingEvent_spec (setup := setup) pending).1⟩

open Classical in
/-- **The base inputs of the one-packet certificate** for one source sequence:
the tremble scales and the obligations not yet discharged other than the value
decompositions and late commitments, each a statement along every fully mixed
Bayes sequence of profiles assembled from the certificate's components, at the
forced sites. -/
structure OnePacketBaseInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) where
  /-- The tremble scale at each index. -/
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_le_one : ∀ n, scale n ≤ 1
  scale_vanishing : Tendsto scale atTop (nhds 0)
  /-- A bound on the gap between a continuation value and the exclusion payoff. -/
  gapBound : ℝ
  gapBound_nonneg : 0 ≤ gapBound
  /-- Every binding and publication value is a bounded value. -/
  covers : bounds.CoversOutputValues
  /-- Every value of an initial binding input is a bounded value. -/
  coversInputs : bounds.CoversInputValues
  /-- Every player's binding events fit in the prepared slots. -/
  capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount
  /-- The late options use bounded slots. -/
  slotsLe : slots ≤ bounds.candidateCount
  /-- **The honest counterparts** at every forced decision input at the player's
  own turn at which the player owes no failure, along every fully mixed Bayes
  sequence of assembled profiles. -/
  counterpartInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup leaks).PlayerEntry}
        {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
      ∀ {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence site
  /-- **The own and replay inputs** at every forced decision input at the
  player's own turn at which the player owes no failure, along every fully mixed
  Bayes sequence of assembled profiles. These are the sites with a projected
  decision (`Vegas.projectedDecision_of_forcedAgent`), late deliveries
  included. -/
  ownInputs : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∀ who (site : (onePacketN).InformationSite who),
      ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
      ∀ {past : List (application setup leaks).PlayerEntry}
        {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
        {event : (graph setup).EventId},
      view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
      OnePacketOwnInputs setup leaks bounds horizon scheduler sequence targetSequence site
        (projectedSite setup leaks decision) atSite rfl
  /-- Some late option sends at a slot. -/
  slots_pos : 0 < slots

omit [Finite setup.intendedProtocol.History] in
/-- Some prepared slot is bounded, once there is a player. -/
theorem OnePacketBaseInputs.one_le_candidateCount
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (who : Player) : 1 ≤ bounds.candidateCount :=
  Nat.zero_lt_of_lt (inputs.capacity who)

/-- **The forced-belief inputs** at a forced decision input at the player's own
turn at which the player owes no failure: the honest counterparts and the own
and replay inputs there. -/
def OnePacketBaseInputs.beliefInputs {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (who : Player) (site : (onePacketN).InformationSite who)
    (forced : ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1)) :
    OnePacketBeliefInputs setup leaks bounds horizon scheduler sequence targetSequence site
      (projectedSite setup leaks decision) atSite rfl where
  toOnePacketCounterpartInputs := inputs.counterpartInputs weights targetSequence assembled mixed
    bayes who site forced notOwing atSite turn
  toOnePacketOwnInputs := inputs.ownInputs weights targetSequence assembled mixed bayes who site
    forced notOwing atSite turn decision

omit [Finite setup.intendedProtocol.History] in
open Classical in
/-- **Histories outside the forced region vanish at late deliveries.** For a
well-formed setup, along every fully mixed Bayes sequence of assembled profiles,
the belief mass outside the forced region at late deliveries of agents that are
not free and owe no failure vanishes uniformly: such a site is forced, debt free and at the
owner's turn, where the honest counterparts and the intended own completions
make it vanish (`Vegas.onePacket_unforcedVanishes`). -/
theorem OnePacketBaseInputs.lateUnforced {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {slots : Nat}
    (inputs : OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots)
    (wellFormed : setup.WellFormed)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence inputs.scale
      inputs.scale_pos inputs.scale_le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) :
    ∃ unforcedDrift : ℕ → ℝ, Tendsto unforcedDrift atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        expect ((targetSequence n).belief who site) (fun history =>
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
          unforcedDrift n := by
  let LateSite := fun {who : Player} (site : (onePacketN).InformationSite who) =>
    ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) ∧
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
        ((onePacketN).agentAt site)
  let mass := fun (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who) =>
    expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1)
  let agentMass := fun (n : ℕ)
      (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) =>
    if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        LateSite (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1) then
      mass n ⟨agent.2.1, present.1⟩ else 0
  have massNonneg : ∀ n agent, 0 ≤ agentMass n agent := fun n agent => by
    simp only [agentMass]
    split
    · exact expect_nonneg _ _ fun history _ => by split <;> norm_num
    · exact le_rfl
  refine ⟨fun n => ∑ agent, agentMass n agent, ?_,
    fun n who site notFree notOwing keyed => ?_⟩
  · rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun agent _ => ?_
    by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        LateSite (⟨agent.2.1, decision⟩ : (onePacketN).InformationSite agent.1)
    · simp only [agentMass, present, ↓reduceDIte]
      obtain ⟨input, atSite, event, turn⟩ := lateDelivery_input setup leaks present.2.2.2.1
      have notFree := present.2.1
      have notOwing := present.2.2.1
      have forced := forcedAgent_of_not_free setup leaks bounds horizon scheduler notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon scheduler notOwing
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      exact onePacket_unforcedVanishes setup leaks bounds horizon scheduler wellFormed mixed bayes
        atSite forced
        (inputs.counterpartInputs weights targetSequence assembled mixed bayes agent.1
          ⟨agent.2.1, present.1⟩ notFree notOwing atSite turn)
        (inputs.ownInputs weights targetSequence assembled mixed bayes agent.1
          ⟨agent.2.1, present.1⟩ notFree notOwing atSite turn decision).ownIntended
    · simp only [agentMass, present, ↓reduceDIte]
      exact tendsto_const_nhds
  · have single := Finset.single_le_sum (fun agent _ => massNonneg n agent)
      (Finset.mem_univ ((onePacketN).agentAt site))
    refine le_trans (le_of_eq ?_) single
    have present : ∃ decision : (onePacketN).IsDecisionInfo who site.1,
        LateSite (⟨site.1, decision⟩ : (onePacketN).InformationSite who) :=
      ⟨site.2, notFree, notOwing, keyed⟩
    simp only [agentMass, present, ↓reduceDIte]
    rfl

open Classical in
/-- **The open inputs of the one-packet certificate other than the value
decompositions** for one source sequence: the base inputs and late commitments
of intended values. -/
structure OnePacketCoreInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketBaseInputs setup leaks bounds horizon scheduler sequence
      slots where
  /-- **Late records.** At late deliveries of agents that are not free and owe
  no failure, the belief's operational records give the certificate's lumped
  failure within a vanishing drift of its expectation under a law of records at
  the key. -/
  lateRecords : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence),
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ beliefDrift : ℕ → ℝ, Tendsto beliefDrift atTop (nhds 0) ∧
      ∀ n who, ∃ recordLaw : LateKey setup leaks →
          PMF (List (Option (OperationalState setup leaks))),
        ∀ (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
          |expect (((targetSequence n).belief who site).map fun history =>
              operationalRecord setup leaks bounds horizon scheduler history.1.trace)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one covers (Nat.zero_lt_of_lt (capacity who)) slotsLe weights
                  targetSequence assembled n who)
                (2 * horizon + 1) key option) -
            expect (recordLaw key)
              (lumpedFailure setup leaks bounds horizon scheduler
                (certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one covers (Nat.zero_lt_of_lt (capacity who)) slotsLe weights
                  targetSequence assembled n who)
                (2 * horizon + 1) key option)| ≤ beliefDrift n
  /-- **The gain transport.** Away from late deliveries, at a site where the
  player owes no failure, every choice committing an intended value at the
  player's own turn has an intended policy at the projected site whose gain at
  the projected belief bounds the choice's gain, up to a vanishing error and the
  belief mass of histories at which another player responded irregularly, times
  a bound on the intended history gains. -/
  valueTransport : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (valueError : ℕ → ℝ) (bound : ℝ), Tendsto valueError atTop (nhds 0) ∧ 0 ≤ bound ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup leaks bounds horizon scheduler site →
        IntendedCommitment setup leaks bounds horizon scheduler site choice →
        ∀ (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
          {past : List (application setup leaks).PlayerEntry}
          {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view)),
        ∃ policy : setup.intendedModel.BehavioralPolicy who,
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            expect (((targetSequence n).belief who site).map
                (replayProjection setup leaks bounds horizon scheduler
                  (projectedSite setup leaks decision) site atSite rfl))
                (setup.intendedModel.historyGain
                  (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                  (intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (payoffComponent setup) (sequence n)
                  (projectedSite setup leaks decision, policy)) +
              valueError n +
              bound * expect ((targetSequence n).belief who site) (fun history =>
                if RegularTrace setup leaks bounds horizon scheduler (sequence n) who
                  history.1.trace then 0 else 1) ∧
          ∀ point, |setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n) (projectedSite setup leaks decision, policy)
              point| ≤ bound
  /-- **Late commitments of intended values.** At every forced late delivery at
  which the player owes no failure, every choice committing an intended value at
  the player's own turn gains at most what some late option gains plus a weight
  in [0, 1] times the gain of a source deviation at the projected site, up to a
  vanishing error. Sending now at a slot fails as the late option sending at
  that slot does whatever the committed value, and on success the committed
  value is worth its source continuation: the weight is the success probability
  and the deviation commits that value. -/
  lateCommitments : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ lateError : ℕ → ℝ, Tendsto lateError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup leaks bounds horizon scheduler site →
        IntendedCommitment setup leaks bounds horizon scheduler site choice →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
        ∃ (option : LateOption slots) (policy : setup.intendedModel.BehavioralPolicy who)
          (weight : ℝ), 0 ≤ weight ∧ weight ≤ 1 ∧
          onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            onePacketSiteGain setup leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) +
              weight * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
                (projectedSite setup leaks decision, policy) +
              lateError n

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the other open inputs and the value decompositions. -/
structure OnePacketOpenInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketCoreInputs setup leaks bounds horizon scheduler parameter
      utility excludedPayoff sequence slots where
  /-- **The value decomposition at late deliveries.** At every forced late
  delivery, the exclusion payoff is at most the agent's continuation value up to
  a vanishing error, with gap at most the gap bound, and the successful part of
  every marked choice and of every late option is its success probability times
  that continuation value up to the error. -/
  lateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        ∀ option,
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site
              (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              continuation n ((onePacketN).agentAt site)| ≤ error n
  /-- **The value decomposition away from late deliveries.** At every forced site
  of an agent owing no failure that is not a late delivery, the exclusion payoff
  is at most the agent's continuation value up to a vanishing error, with gap at
  most the gap bound, or the site has no pending event; and the successful part
  of every marked choice and of the prescribed component is its success
  probability times that
  continuation value up to the error. -/
  nonLateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ((excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
            continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound) ∨
          pendingEvent setup leaks who site.1 = none) ∧
        (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        |onePacketSiteSuccess setup leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
            (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
              scale_le_one n ((onePacketN).agentAt site))) *
            continuation n ((onePacketN).agentAt site)| ≤ error n


end Open

end Vegas
