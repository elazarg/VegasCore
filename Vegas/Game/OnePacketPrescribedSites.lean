/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSureCompletion
import Vegas.Game.OnePacketDisclosureCompletion
import Vegas.Game.OnePacketOwnDisclosure
import Vegas.Game.OnePacketHonestForced

/-! # The prescribed component at a first activation

**Resolving disclosures transmit canonically.** When the canonical disclosure
at the player's pending reveal transmits, as it does at a debt-free forced
state, so do the canonical decisions of every encoded source action there other
than a refusal (`Vegas.canonicalTransmitsAt_of_disclosureResolves`).

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
  have observedInfo : (onePacketN).infoOf who start.trace = site.1 := observed
  refine ⟨ProtocolState.behavioralStateStep setup.program
    (setup.intendedOpeningProfile source.strategy) point, ?_, ?_⟩
  · rw [rankEq]
    cases node : nodeView (graph setup) event with
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
    rw [startState, rankEq]
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

end Values

end Vegas
