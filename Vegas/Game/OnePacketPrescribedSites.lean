/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSureCompletion
import Vegas.Game.OnePacketDisclosureCompletion
import Vegas.Game.OnePacketOwnDisclosure
import Vegas.Game.OnePacketHonestForced
import Vegas.Game.OnePacketValueTransport

/-! # The prescribed component at a first activation

**Resolving disclosures transmit canonically.** When the canonical disclosure
at the player's pending reveal transmits, as it does at a debt-free forced
state, so do the canonical decisions of every encoded source action there other
than a refusal (`Vegas.canonicalTransmitsAt_of_disclosureResolves`).

**A forced debt-free first activation.** At a history of a first activation of
a forced player, where no player owes a failure at the decoded point, the
configuration is the completed prefix of the site's rank and decodes there to a
point of the intended game reached by the intended game
(`Vegas.firstActivation_history_facts`).

**Sure completion of the prescribed component.** At a history of a first
activation of a forced player, where no player owes a failure at the decoded
point, installing the slot-trembled prescribed component of an intended
assessment has the completion-point law of the step of the intended effective
opening at the decoded point, with success one up to six times the scale, and
that step keeps the history's continuation value
(`Vegas.firstActivation_prescribed_sureCompletion`). So the site's completion
value of the prescribed component is one less its failure probability times
the site's continuation value up to thirty times the scale times the payoff
bound (`Vegas.abs_siteStopValue_prescribed_sub_le`).

**Compared transmissions name the pending reveal.** At a site with a pending
event, every compared choice that transmits sends a packet naming that event,
which is a reveal of the site's player
(`Vegas.compared_transmission_names`); at a pending binding the only compared
choice is silence.

**A submission for the turn's event leaves it pending.** A choice of the
one-packet menu submitting for the event of the player's turn is offered only
while the recall has not submitted for it, so the event is pending there
(`Vegas.pendingEvent_of_turnSubmission`).

**Sure completion of a disclosure.** At a pending reveal there, every packet the
one-packet menu offers naming the reveal is the canonical disclosure, which has
the completion-point law of the source step of the disclosure with success one
and no error; that step keeps the continuation value, since the as-if-honest
law there plays the disclosure alone
(`Vegas.firstActivation_disclosure_sureCompletion`). So the site's completion
value of such a choice is exactly one less its failure probability times the
site's continuation value (`Vegas.siteStopValue_disclosure_eq`).

**Off the irregular histories.** At a forced site whose player's own
completions along regular histories decode to intended actions, the regular
histories of the belief are forced states at which no player owes a failure.
So both bounds hold at a site with the belief mass of the irregular histories
added, times four times the payoff bound
(`Vegas.abs_siteStopValue_prescribed_sub_le_off`,
`Vegas.abs_siteStopValue_disclosure_sub_le_off`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

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

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Resolving disclosures transmit canonically.** When the canonical
disclosure of `who` at its pending reveal transmits, so do the canonical
decisions of every encoded source action at it other than a refusal. -/
theorem canonicalTransmitsAt_of_disclosureResolves {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (resolves : DisclosureResolves setup leaks who
      past view) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event) {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq) :
    CanonicalTransmitsAt setup leaks who past view event := by
  intro action graphAction encoded _ discloses
  have disclose := encodeEventAction?_discloses setup.program event action discloses
    graphAction encoded payload outputEq
  have graphEq : graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
    rw [← disclose]
    simp
  rw [graphEq]
  exact resolves event pending who payload binding checks outputEq codeEq node

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **A forced debt-free first activation.** At a history of a first activation
of `who` for its pending event, forced for `who` with no player owing a failure
at the decoded point, `who` is deciding at an execution whose recall has never
activated the event, whose configuration is the completed prefix of the site's
rank and decodes there to a point of the intended game reached by the intended
game. -/
theorem firstActivation_history_facts (wellFormed : setup.WellFormed) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (regular : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) :
    ∃ (remaining : Nat) (execution : (application setup leaks).Execution)
      (point : ProtocolState setup.program),
      history.1.state = some ⟨remaining, some who, execution⟩ ∧
      site.1 = some (execution.recall who, execution.observe (application setup leaks) who) ∧
      (∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry) ∧
      execution.application.config.cut.IsPrefix (siteRank site.1) ∧
      sourceServicePrefix? setup (siteRank site.1) execution.application.config = some point ∧
      ProtocolState.Intended setup.program point ∧ IntendedReached setup point := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨start, observed⟩ := history
  change ForcedState setup leaks who start.state at forced
  change ∀ point, nativeDecodedState setup leaks start.state = some point → _ at regular
  have observedState : (application setup leaks).observe who start.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans observed
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at forced
    exact forced.elim
  rw [startState] at observedState regular forced
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    rw [← observedState] at pending
    cases pending
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := startState ▸ start.trace
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event := by
    rw [observedState]
    exact pending
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec pendingAt
  have never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry :=
    fun entry member activated => first
      ⟨_, _, event, observedState.symm, pending, entry, member, activated⟩
  -- The decoded point is intended and reached by the intended game.
  obtain ⟨point, pointDecoded, forcedPoint⟩ := (forcedState_iff_decodedPoint _).mp forced
  obtain ⟨found, ordered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = found := by
    rw [← observedState]
    change (execution.application.config.history.map EventGraph.Completion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ ordered
  have decoded : sourceServicePrefix? setup found execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).symm.trans pointDecoded
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have residualDecoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = residualPoint
    at residualDecoded
  rw [decoded, Option.some.injEq] at residualDecoded
  subst residualDecoded
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (regular point pointDecoded player owed).elim
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace _ rfl
    (fun found foundDecoded player => regular found foundDecoded player)
  have reached : IntendedReached setup point :=
    ⟨replay, (intendedHistory?_state trace replayed).trans pointDecoded⟩
  have freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store
      event → siteFresh who site.1 control := fun control notFailed => by
    simpa only [siteFresh, pending] using notFailed
  rw [rankEq]
  exact ⟨remaining, execution, point, rfl, observedState.symm, never, ordered, decoded,
    intendedPoint, reached⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Compared transmissions name the pending reveal.** At a site with a pending
event, a compared choice that transmits sends a packet naming that event, and
the event is a reveal of the site's player: the one-packet menu sends no
malformed packet, a compared choice commits no value, and it submits only for
the event of the player's turn. -/
theorem compared_transmission_names {who : Player} (site : (onePacketN).InformationSite who)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (choice : (onePacketN).Choice who site.1)
    (marked : onePacketCompared setup leaks bounds horizon scheduler who site choice)
    {response : (application setup leaks).Action} (selected : choice.1 = some response)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) :
    material.call.packet.event? (graph setup) = some event ∧
      ∃ (payload : L.Ty) (binding : EventGraph.FieldRef (graph setup).layout
        (.binding who payload)) (checks : List (EventGraph.GuardCheck (graph setup).layout
          payload)) (outputEq : (graph setup).outputLayout event = .publication payload)
        (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .resolve who payload binding checks),
        nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq := by
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases info : site.1 with
    | none =>
        rw [info] at pending
        cases pending
    | some input => exact ⟨input.1, input.2, rfl⟩
  obtain ⟨offered, offeredEq, member⟩ := choice_response setup leaks bounds horizon scheduler
    site atSite choice
  rw [selected, Option.some.injEq] at offeredEq
  rw [← offeredEq] at member
  obtain ⟨noValue, own⟩ := marked.2 response selected
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, _, _, _⟩ := pendingEvent_spec pendingAt
  cases packet : material.call.packet with
  | commitment named handle => exact (noValue material sends named handle packet).elim
  | malformed raw => exact (onePacket_not_malformed (bounds := bounds) member sends raw packet).elim
  | opening named handle raw =>
      have submitted : (runtime setup).submittedEvent? leaks response = some named := by
        unfold EventGraphRuntime.submittedEvent?
        rw [sends]
        dsimp only
        rw [packet]
        rfl
      obtain ⟨past', view', atSite', turn'⟩ := own named submitted
      rw [atSite, Option.some.injEq, Prod.mk.injEq] at atSite'
      obtain ⟨_, rfl⟩ := atSite'
      have sameEvent : named = event := Option.some.inj (turn'.symm.trans turn)
      subst sameEvent
      exact ⟨rfl, onePacket_opening_node member sends packet⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
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

section Values

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **Sure completion of the prescribed component.** Under the asynchronous
contract, the timeliness margin and retention of covered canonical packets, at
a history of a first activation of `who` for its pending event, forced for
`who` with no player owing a failure at the decoded point, installing the
slot-trembled prescribed component of an intended assessment source has the
completion-point law of the step of the intended effective opening of source
at the decoded point, with success one up to six times the scale; that step
keeps the history's continuation value. -/
theorem firstActivation_prescribed_sureCompletion (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (regular : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound) :
    ∃ stepLaw : PMF (ProtocolState setup.program),
      CompletionPointLaw setup leaks bounds horizon scheduler
          (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1
              (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler
                source scale nonnegative le_one who site.1)))
          (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw (6 * scale) ∧
        expect stepLaw (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile source.strategy) who) =
          decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (setup.intendedOpeningProfile source.strategy) who (siteRank site.1) history.1 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨remaining, execution, point, startState, observedState, never, ordered, decoded,
    intendedPoint, reached⟩ := firstActivation_history_facts setup leaks bounds horizon scheduler
      wellFormed site pending first history forced regular
  obtain ⟨start, observed⟩ := history
  change start.state = _ at startState
  change ForcedState setup leaks who start.state at forced
  change ∀ point, nativeDecodedState setup leaks start.state = some point → _ at regular
  rw [startState] at regular forced
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := startState ▸ start.trace
  have pendingAt : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event := by
    rw [← observedState]
    exact pending
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec pendingAt
  have freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store
      event → siteFresh who site.1 control := fun control notFailed => by
    simpa only [siteFresh, pending] using notFailed
  have observedInfo : (onePacketN).infoOf who start.trace = site.1 := observed
  refine ⟨ProtocolState.behavioralStateStep setup.program
    (setup.intendedOpeningProfile source.strategy) point, ?_, ?_⟩
  · cases node : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
        have none := nodeView_sample_actor outputEq codeEq
        rw [owned] at none
        cases none
    | bind owner payload outputEq codeEq =>
        have ownerEq : owner = who :=
          Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
        subst ownerEq
        exact firstActivation_prescribed_completionPointLaw contract timely retains source
          nonnegative le_one assessment.strategy start startState event pendingAt never node
          ordered decoded intendedPoint freshOf site.1 observedInfo
    | resolve owner payload binding checks outputEq codeEq =>
        have ownerEq : owner = who :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
        subst ownerEq
        have resolves := disclosureResolves_of_debtFree wellFormed trace owner forced
          fun found foundDecoded => regular found foundDecoded owner
        exact firstActivation_prescribed_disclose_completionPointLaw contract timely retains
          source nonnegative le_one assessment.strategy start startState event pendingAt never
          node (canonicalTransmitsAt_of_disclosureResolves setup leaks resolves pendingAt node)
          ordered decoded intendedPoint freshOf site.1 observedInfo
  · rw [expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff _ who
      readoutBounded point]
    unfold decodedPointValue
    rw [startState]
    simp only [decoded, reached, ↓reduceIte]

open Classical in
/-- **The prescribed component at a first-activation site.** Under the
hypotheses of `Vegas.firstActivation_prescribed_sureCompletion` at every
history of the site's belief, the site's completion value of the slot-trembled
prescribed component of an intended assessment source is one less its failure
probability times the site's continuation value up to thirty times the scale
times the payoff bound. -/
theorem abs_siteStopValue_prescribed_sub_le
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    (forced : ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state)
    (regular : ∀ history ∈ (assessment.belief who site).support,
      ∀ point, nativeDecodedState setup leaks history.1.state = some point →
        ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment (setup.intendedOpeningProfile source.strategy) site
        (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
          scale nonnegative le_one who site.1) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
          (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
            scale nonnegative le_one who site.1)) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment (setup.intendedOpeningProfile source.strategy) site| ≤
      5 * (6 * scale) * payoffBound :=
  abs_siteStopValue_sub_le_of_sureCompletion setup leaks bounds horizon scheduler parameter
    utility excludedPayoff assessment _ site _ pending readoutBounded fun history member =>
      firstActivation_prescribed_sureCompletion setup leaks bounds horizon scheduler parameter
        utility excludedPayoff wellFormed contract timely retains source nonnegative le_one
        assessment site pending first history (forced history member) (regular history member)
        readoutBounded

/-- **Sure completion of a disclosure.** Under the asynchronous contract and
the timeliness margin, at a history of a first activation of `who` for its
pending reveal, forced for `who` with no player owing a failure at the decoded
point, a choice transmitting a packet naming the reveal has the completion-point
law of the source step of the disclosure at the decoded point, with success one
and no error; that step keeps the history's continuation value under the
intended effective opening of every intended assessment source. -/
theorem firstActivation_disclosure_sureCompletion (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (regular : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (graph setup) = some event) :
    ∃ stepLaw : PMF (ProtocolState setup.program),
      CompletionPointLaw setup leaks bounds horizon scheduler
          (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 (PMF.pure choice)))
          (siteRank site.1) (siteFresh who site.1) history.1 1 stepLaw 0 ∧
        expect stepLaw (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile source.strategy) who) =
          decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            (setup.intendedOpeningProfile source.strategy) who (siteRank site.1) history.1 := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨remaining, execution, point, startState, observedState, never, ordered, decoded,
    intendedPoint, reached⟩ := firstActivation_history_facts setup leaks bounds horizon scheduler
      wellFormed site pending first history forced regular
  obtain ⟨start, observed⟩ := history
  change start.state = _ at startState
  change ForcedState setup leaks who start.state at forced
  change ∀ point, nativeDecodedState setup leaks start.state = some point → _ at regular
  rw [startState] at regular forced
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := startState ▸ start.trace
  have pendingAt : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event := by
    rw [← observedState]
    exact pending
  obtain ⟨turn, _, _, _⟩ := pendingEvent_spec pendingAt
  have freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store
      event → siteFresh who site.1 control := fun control notFailed => by
    simpa only [siteFresh, pending] using notFailed
  -- The transmitted response is the canonical disclosure.
  have resolves := disclosureResolves_of_debtFree wellFormed trace who forced
    fun found foundDecoded => regular found foundDecoded who
  obtain ⟨disclosed, sendsDisclosure⟩ := Option.ne_none_iff_exists'.mp
    (resolves event pendingAt who payload binding checks outputEq codeEq node)
  obtain ⟨offered, offeredEq, member⟩ := choice_response setup leaks bounds horizon scheduler
    site observedState choice
  rw [selected, Option.some.injEq] at offeredEq
  rw [← offeredEq] at member
  have canonical := onePacket_opening_eq_disclosure trace who event node disclosed
    sendsDisclosure response member material sends named
  -- The disclosure decodes to the one intended choice of the as-if-honest law.
  have supportAction : ∀ honest ∈ (asIfHonestProfile setup leaks source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).support,
      ∃ action, honest = some action ∧
        decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) = some action ∧
        action ∈ ProtocolView.intendedAvailable who setup.program
          (ProtocolState.observe who setup.program point) := by
    intro honest supported
    have encodes := asIfHonestProfile_encodes source who execution _ ordered point decoded
      (execution.recall who) event turn honest supported
    rcases honest with _ | action
    · simp at encodes
    cases encoded : encodeEventAction? setup.program event action with
    | none => simp [encoded] at encodes
    | some graphAction =>
        have success := asIfHonestProfile_success source who execution _ ordered point decoded
          (execution.recall who) action supported
        have disclose := encodeEventAction?_discloses setup.program event action success.2
          graphAction encoded payload outputEq
        have graphEq : graphAction =
            cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
          rw [← disclose]
          simp
        obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup leaks source
          who execution _ ordered point decoded (execution.recall who) _).mp supported
        have legal := intended.2
        change ProtocolView.intendedMenu who setup.program
          (ProtocolState.observe who setup.program point) intended.1 at legal
        rw [same] at legal
        refine ⟨action, rfl, ?_, legal.2⟩
        rw [← graphEq]
        exact decodeEventAction_encodeEventAction?_eq_some setup.program event action
          graphAction encoded
  obtain ⟨honest, honestSupported⟩ := (asIfHonestProfile setup leaks source who
    (some (execution.recall who, execution.observe (application setup leaks) who))).support_nonempty
  obtain ⟨action, _, decodes, intendedAction⟩ := supportAction honest honestSupported
  refine ⟨ProtocolState.step setup.program point (fun _ => some action), ?_, ?_⟩
  · exact firstActivation_disclose_completionPointLaw contract timely assessment.strategy start
      startState event turn never node _ disclosed sendsDisclosure site.1 observed choice
      (selected.trans (congrArg some canonical)) ordered decoded intendedPoint decodes
      intendedAction freshOf
  · have stepEq : (asIfHonestProfile setup leaks source who
        (some (execution.recall who, execution.observe (application setup leaks) who))).bind
          (fun honest => ProtocolState.step setup.program point (fun _ => honest)) =
        ProtocolState.step setup.program point (fun _ => some action) := by
      refine (bind_congr_on_support _ fun honest supported => ?_).trans
        (PMF.bind_const _ _)
      obtain ⟨other, rfl, otherDecodes, _⟩ := supportAction honest supported
      rw [decodes, Option.some.injEq] at otherDecodes
      rw [otherDecodes]
    rw [← stepEq, asIfHonest_bind_step_eq_behavioralStateStep source who execution ordered
      decoded intendedPoint turn (execution.recall who),
      expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff _ who
        readoutBounded point]
    unfold decodedPointValue
    rw [startState]
    simp only [decoded, reached, ↓reduceIte]

open Classical in
/-- **A disclosure at a first-activation site.** Under the hypotheses of
`Vegas.firstActivation_disclosure_sureCompletion` at every history of the
site's belief, the site's completion value of a choice transmitting a packet
naming the pending reveal is one less its failure probability times the site's
continuation value. -/
theorem siteStopValue_disclosure_eq
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (forced : ∀ history ∈ (assessment.belief who site).support,
      ForcedState setup leaks who history.1.state)
    (regular : ∀ history ∈ (assessment.belief who site).support,
      ∀ point, nativeDecodedState setup leaks history.1.state = some point →
        ∀ player, ¬ ProtocolState.OwesFailure player setup.program point)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (graph setup) = some event) :
    siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment (setup.intendedOpeningProfile source.strategy) site (PMF.pure choice) =
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
          (PMF.pure choice)) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment (setup.intendedOpeningProfile source.strategy) site := by
  have near := abs_siteStopValue_sub_le_of_sureCompletion setup leaks bounds horizon scheduler
    parameter utility excludedPayoff assessment _ site _ pending readoutBounded
    fun history member => firstActivation_disclosure_sureCompletion setup leaks bounds horizon
      scheduler parameter utility excludedPayoff wellFormed contract timely source assessment
      site pending first node history (forced history member) (regular history member)
      readoutBounded choice selected sends named
  rw [mul_zero, zero_mul] at near
  exact sub_eq_zero.mp (abs_nonpos_iff.mp near)

open Classical in
/-- **The prescribed component at a forced first-activation site, off the
irregular histories.** At a forced, non-late site of `who` with a pending
event, where `who`'s own completions along regular histories decode to intended
actions, the site's completion value of the slot-trembled prescribed component
of an intended assessment source is one less its failure probability times the
site's continuation value up to thirty times the scale times the payoff bound,
plus four times the bound times the belief mass of the histories irregular for
source. -/
theorem abs_siteStopValue_prescribed_sub_le_off
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (forcedSite : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who site.1)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    (ownIntended : ∀ history : (onePacketN).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon scheduler source who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound) (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment (setup.intendedOpeningProfile source.strategy) site
        (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
          scale nonnegative le_one who site.1) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
          (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
            scale nonnegative le_one who site.1)) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment (setup.intendedOpeningProfile source.strategy) site| ≤
      5 * (6 * scale) * payoffBound +
        4 * payoffBound * expect (assessment.belief who site) (fun history =>
          if RegularTrace setup leaks bounds horizon scheduler source who history.1.trace
          then (0 : ℝ) else 1) :=
  abs_siteStopValue_sub_le_of_sureCompletion_off setup leaks bounds horizon scheduler parameter
    utility excludedPayoff assessment _ site _ pending _ (by positivity) readoutBounded
    excludedBounded fun history _ regular =>
      firstActivation_prescribed_sureCompletion setup leaks bounds horizon scheduler parameter
        utility excludedPayoff wellFormed contract timely retains source nonnegative le_one
        assessment site pending first history
        (forcedState_of_regular wellFormed source atSite forcedSite history regular
          (ownIntended history regular))
        (not_owesFailure_of_regular wellFormed source atSite
          forcedSite history regular (ownIntended history regular))
        readoutBounded

open Classical in
/-- **A disclosure at a forced first-activation site, off the irregular
histories.** At a forced, non-late site of `who` with a pending reveal, where
`who`'s own completions along regular histories decode to intended actions, the
site's completion value of a choice transmitting a packet naming the reveal is
one less its failure probability times the site's continuation value up to four
times the payoff bound times the belief mass of the histories irregular for
source. -/
theorem abs_siteStopValue_disclosure_sub_le_off
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (source : setup.intendedModel.BehavioralAssessment)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (forcedSite : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler who site.1)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (ownIntended : ∀ history : (onePacketN).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon scheduler source who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace)
    {payoffBound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        payoffBound) (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (choice : (onePacketN).Choice who site.1) {response : (application setup leaks).Action}
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material)
    (named : material.call.packet.event? (graph setup) = some event) :
    |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment (setup.intendedOpeningProfile source.strategy) site (PMF.pure choice) -
      (1 - onePacketSiteFailure setup leaks bounds horizon scheduler assessment site
          (PMF.pure choice)) *
        siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          assessment (setup.intendedOpeningProfile source.strategy) site| ≤
      4 * payoffBound * expect (assessment.belief who site) (fun history =>
        if RegularTrace setup leaks bounds horizon scheduler source who history.1.trace
        then (0 : ℝ) else 1) := by
  have near := abs_siteStopValue_sub_le_of_sureCompletion_off setup leaks bounds horizon
    scheduler parameter utility excludedPayoff assessment _ site _ pending _ le_rfl
    readoutBounded excludedBounded fun history _ regular =>
      firstActivation_disclosure_sureCompletion setup leaks bounds horizon scheduler parameter
        utility excludedPayoff wellFormed contract timely source assessment site pending first
        node history
        (forcedState_of_regular wellFormed source atSite forcedSite history regular
          (ownIntended history regular))
        (not_owesFailure_of_regular wellFormed source atSite
          forcedSite history regular (ownIntended history regular))
        readoutBounded choice selected sends named
  simpa using near

end Values

end Vegas
