/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotLaw
import Vegas.Game.OnePacketCertificateLumping
import Vegas.Game.IntendedChoiceReach
import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.RecoveryNonLateChoices
import Vegas.Game.OnePacketSequentialPreservation
import Vegas.Game.OnePacketHonestDecision
import Vegas.Compile.EventGraphBacktranslation
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



section Open

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

/-- The local failure probability of a law at a site of the one-packet game:
the probability of the event-level failure of the site's pending event. -/
def onePacketSiteFailure (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localFailure (2 * horizon + 1) assessment site
    (onePacketFailed setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- The successful part of the local exclusion payoff of a law at a site of the
one-packet game: its value on histories outside the event-level failure of the
site's pending event. -/
def onePacketSiteSuccess (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) :
    ℝ :=
  localSuccessValue (2 * horizon + 1)
    (readoutExclusion setup runtime leaks bounds (initialLaw setup) horizon scheduler parameter
      utility
      excludedPayoff) (payoffComponent setup) assessment site
    (onePacketFailed setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site)) law

/-- A response commits no value: it transmits no commitment packet. -/
def CommitsNoValue (response : (application setup runtime leaks).Action) : Prop :=
  ∀ material, response.transmission = some material →
    ∀ event handle, material.call.packet ≠ .commitment event handle

/-- **The marked choices of the one-packet certificate**: silence at a late
delivery, and elsewhere the choices that commit no value and send only for the
event at the player's own turn. Their success continuation is the agent's
continuation value; every other choice is compared with a late option, a
source deviation, the prescribed component, or has no gain. -/
def onePacketCompared (who : Player) (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1) : Prop :=
  (LateDelivery setup runtime leaks who site.1 → choice.1 = some ⟨none⟩) ∧
    ∀ response, choice.1 = some response → CommitsNoValue setup runtime leaks response ∧
      ∀ event, runtime.submittedEvent? leaks response = some event →
        ∃ past view, site.1 = some (past, view) ∧
          view.application.publicView.ownTurn? who = some event

variable {setup runtime leaks bounds horizon scheduler} in
omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **One packet per event.** At every history of the supplied runtime, a
response of the one-packet menu transmitting for an event is sent before the
recall has submitted for that event. -/
theorem onePacket_unrecorded_of_member {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) (response : (application setup runtime
      leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    (submitted : runtime.submittedEvent? leaks response = some event) :
    runtime.eventRecorded leaks (control.execution.recall who) event = false := by
  let app := application setup runtime leaks
  cases recorded : runtime.eventRecorded leaks (control.execution.recall who) event with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨_, sent⟩ := (bounds.mem_onePacketActions runtime leaks who _ _ _).mp member
      rcases sent with silent | ⟨material, transmits, permitted⟩
      · unfold EventGraphRuntime.submittedEvent? at submitted
        rw [silent] at submitted
        cases submitted
      · have named : material.call.packet.event? (graph setup) = some event := by
          unfold EventGraphRuntime.submittedEvent? at submitted
          rw [transmits] at submitted
          exact submitted
        have recalled := runtime.countRecall_history leaks trace
        rw [runtime.localEnvelope_eq_of_recall leaks control.execution recalled.1
          recalled.2.1 who material, countPermits_eq_true_iff] at permitted
        obtain ⟨entry, entryMember, entrySubmitted⟩ :=
          (runtime.eventRecorded_iff leaks _ event).mp recorded
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
          ((transmissionsEmitted_serviceInvariant (runtime := runtime) scheduler).history
            (initialLaw setup) horizon
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

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **A submission for the turn's event leaves it pending.** At a site whose
view has `event` as the player's turn, if some choice submits for `event`, then
`event` is pending: the one-packet menu sends for an event only before the
recall has submitted for it. -/
theorem pendingEvent_of_turnSubmission {who : Player} (site : (onePacketN).InformationSite who)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (choice : (onePacketN).Choice who site.1) {response : (application setup runtime leaks).Action}
    (selected : choice.1 = some response)
    (submitted : runtime.submittedEvent? leaks response = some event) :
    pendingEvent setup runtime leaks who site.1 = some event := by
  let menu := bounds.onePacketMenu runtime leaks
  obtain ⟨offered, offeredEq, member⟩ := choice_response setup runtime leaks bounds horizon
    scheduler
    site atSite choice
  rw [selected, Option.some.injEq] at offeredEq
  rw [← offeredEq] at member
  obtain ⟨⟨start, observed⟩, _⟩ := site.2
  have observedState : (application setup runtime leaks).observe who start.state =
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
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (startState ▸ start.trace)
  rw [atSite]
  exact pendingEvent_of_spec (runtime := runtime) turn
    (onePacket_unrecorded_of_member (runtime := runtime) rawTrace who event response member
      submitted)

/-- The local gain at a site of the one-packet game of installing a law: the
expected exclusion payoff of the deviation minus that of the assessment. -/
def onePacketSiteGain (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) (law : PMF ((onePacketN).Choice who site.1)) : ℝ :=
  let comparison := (onePacketN).assessmentComparisonWith
    ((onePacketN).truncatedRunner (2 * horizon + 1))
    (readoutExclusion setup runtime leaks bounds (initialLaw setup) horizon scheduler parameter
      utility
      excludedPayoff) assessment who (site, (assessment.strategy who).withLaw site.1 law)
  expect comparison.alternative ((payoffComponent setup) · who) -
    expect comparison.prescribed ((payoffComponent setup) · who)

open Classical in
/-- **The open inputs of the one-packet certificate other than the value
decompositions** for one source sequence: the base inputs and late commitments
of intended values. -/
structure OnePacketCoreInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketBaseInputs setup runtime leaks bounds horizon scheduler sequence
      slots where
  /-- **Late records.** At late deliveries of agents that are not free and owe
  no failure, the belief's operational records give the certificate's lumped
  failure within a vanishing drift of its expectation under a law of records at
  the key. -/
  lateRecords : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence),
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ beliefDrift : ℕ → ℝ, Tendsto beliefDrift atTop (nhds 0) ∧
      ∀ n who, ∃ recordLaw : LateKey setup runtime leaks →
          PMF (List (Option (OperationalState setup runtime leaks))),
        ∀ (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
            (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          ∀ key, lateKey setup runtime leaks who site.1 = some key → ∀ option,
          |expect (((targetSequence n).belief who site).map fun history =>
              operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace)
              (lumpedFailure setup runtime leaks bounds horizon scheduler
                (certificateLumping setup runtime leaks bounds horizon scheduler sequence scale
                  scale_pos
                  scale_le_one covers (Nat.zero_lt_of_lt (capacity who)) slotsLe weights
                  targetSequence assembled n who)
                (2 * horizon + 1) key option) -
            expect (recordLaw key)
              (lumpedFailure setup runtime leaks bounds horizon scheduler
                (certificateLumping setup runtime leaks bounds horizon scheduler sequence scale
                  scale_pos
                  scale_le_one covers (Nat.zero_lt_of_lt (capacity who)) slotsLe weights
                  targetSequence assembled n who)
                (2 * horizon + 1) key option)| ≤ beliefDrift n
  /-- **The gain transport.** Away from late deliveries, at a site where the
  player owes no failure, every choice committing an intended value at the
  player's own turn has an intended policy at the projected site whose gain at
  the projected belief bounds the choice's gain, up to a vanishing error and the
  belief mass of histories at which another player responded irregularly, times
  a bound on the intended history gains. -/
  valueTransport : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (valueError : ℕ → ℝ) (bound : ℝ), Tendsto valueError atTop (nhds 0) ∧ 0 ≤ bound ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup runtime leaks bounds horizon scheduler site →
        IntendedCommitment setup runtime leaks bounds horizon scheduler site choice →
        ∀ (decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
          site.1))
          {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past,
            view)),
        ∃ policy : setup.intendedModel.BehavioralPolicy who,
          onePacketSiteGain setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            expect (((targetSequence n).belief who site).map
                (replayProjection setup runtime leaks bounds horizon scheduler
                  (projectedSite setup runtime leaks decision) site atSite rfl))
                (setup.intendedModel.historyGain
                  (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
                  (intendedReadoutExclusion setup parameter utility excludedPayoff)
                  (payoffComponent setup) (sequence n)
                  (projectedSite setup runtime leaks decision, policy)) +
              valueError n +
              bound * expect ((targetSequence n).belief who site) (fun history =>
                if RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
                  history.1.trace then 0 else 1) ∧
          ∀ point, |setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n) (projectedSite setup runtime leaks decision,
                policy)
              point| ≤ bound
  /-- **Late commitments of intended values.** At every forced late delivery at
  which the player owes no failure, every choice committing an intended value at
  the player's own turn gains at most what some late option gains plus a weight
  in [0, 1] times the gain of a source deviation at the projected site, up to a
  vanishing error. Sending now at a slot fails as the late option sending at
  that slot does whatever the committed value, and on success the committed
  value is worth its source continuation: the weight is the success probability
  and the deviation commits that value. -/
  lateCommitments : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ lateError : ℕ → ℝ, Tendsto lateError atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who) choice,
        ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice →
        SiteDebtFree setup runtime leaks bounds horizon scheduler site →
        IntendedCommitment setup runtime leaks bounds horizon scheduler site choice →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
          site.1),
        ∃ (option : LateOption slots) (policy : setup.intendedModel.BehavioralPolicy who)
          (weight : ℝ), 0 ≤ weight ∧ weight ≤ 1 ∧
          onePacketSiteGain setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff
              (targetSequence n) site (PMF.pure choice) ≤
            onePacketSiteGain setup runtime leaks bounds horizon scheduler parameter utility
                excludedPayoff (targetSequence n) site
                (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) +
              weight * intendedSiteGain setup parameter utility excludedPayoff (sequence n)
                (projectedSite setup runtime leaks decision, policy) +
              lateError n

open Classical in
/-- **The open inputs of the one-packet certificate** for one source sequence:
the other open inputs and the value decompositions. -/
structure OnePacketOpenInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (slots : Nat) extends OnePacketCoreInputs setup runtime leaks bounds horizon scheduler parameter
      utility excludedPayoff sequence slots where
  /-- **The value decomposition at late deliveries.** At every forced late
  delivery, the exclusion payoff is at most the agent's continuation value up to
  a vanishing error, with gap at most the gap bound, and the successful part of
  every marked choice and of every late option is its success probability times
  that continuation value up to the error. -/
  lateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
        continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound ∧
        (∀ choice, onePacketCompared setup runtime leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup runtime leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler (targetSequence
              n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        ∀ option,
          |onePacketSiteSuccess setup runtime leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site
              (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
            (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler (targetSequence
              n)
              site (onePacketLate setup runtime leaks bounds horizon scheduler sequence scale
                scale_pos
                scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              continuation n ((onePacketN).agentAt site)| ≤ error n
  /-- **The value decomposition away from late deliveries.** At every forced site
  of an agent owing no failure that is not a late delivery, the exclusion payoff
  is at most the agent's continuation value up to a vanishing error, with gap at
  most the gap bound, or the site has no pending event; and the successful part
  of every marked choice and of the prescribed component is its success
  probability times that
  continuation value up to the error. -/
  nonLateDecomposition : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon
      scheduler slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
    OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one
      weights targetSequence →
    (∀ n, (targetSequence n).IsFullyMixed) →
    (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu runtime leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
    ∃ (continuation : ℕ → (onePacketN).InformationAgent (onePacketN).playedInformation → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
          (LateDeliveryAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler)
          ((onePacketN).agentAt site) →
        ((excludedPayoff who ≤ continuation n ((onePacketN).agentAt site) + error n ∧
            continuation n ((onePacketN).agentAt site) - excludedPayoff who ≤ gapBound) ∨
          pendingEvent setup runtime leaks who site.1 = none) ∧
        (∀ choice, onePacketCompared setup runtime leaks bounds horizon scheduler who site choice →
          |onePacketSiteSuccess setup runtime leaks bounds horizon scheduler parameter utility
              excludedPayoff (targetSequence n) site (PMF.pure choice) -
            (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler (targetSequence
              n)
              site (PMF.pure choice)) * continuation n ((onePacketN).agentAt site)| ≤
            error n) ∧
        |onePacketSiteSuccess setup runtime leaks bounds horizon scheduler parameter utility
            excludedPayoff (targetSequence n) site
            (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale
              scale_pos
              scale_le_one n ((onePacketN).agentAt site)) -
          (1 - onePacketSiteFailure setup runtime leaks bounds horizon scheduler (targetSequence
            n) site
            (onePacketPrescribed setup runtime leaks bounds horizon scheduler sequence scale
              scale_pos
              scale_le_one n ((onePacketN).agentAt site))) *
            continuation n ((onePacketN).agentAt site)| ≤ error n


end Open

end Vegas
