module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCertificateCounterpart
public import Vegas.Game.OnePacketRepairedResponderForced
public import Vegas.Game.OnePacketPairedLikelihoodWeight
public import Vegas.Game.OnePacketCounterpartBound
public import Vegas.Game.OnePacketDisclosureAlong
public import Vegas.Game.OnePacketOwnIntended
public import Vegas.Game.OnePacketStepPositive
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Certificate reach comparisons from actual binding repairs -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

variable {Public : Type*} {signal : State L setup.context → Public}

private theorem repair_operationalState_eq_of_record_eq
    {first second : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).State}
    (left : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace first)
    (right : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace second)
    (records : operationalRecord setup timeouts leaks bounds horizon scheduler left =
      operationalRecord setup timeouts leaks bounds horizon scheduler right) :
    operationalState setup timeouts leaks first = operationalState setup timeouts leaks second := by
  obtain ⟨rest, firstEq⟩ := operationalRecord_head (timeouts := timeouts) left
  obtain ⟨otherRest, secondEq⟩ := operationalRecord_head (timeouts := timeouts) right
  rw [firstEq, secondEq] at records
  exact (List.cons.inj records).1

variable
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

/-- Actual repairs yield the certificate reach comparison at a forced decision. -/
theorem reach_le_counterpart_certificate_of_repairs (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) (covered : BindingFieldsCovered bounds)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup timeouts leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup timeouts leaks bounds horizon scheduler (sequence
      n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0))
    (n : ℕ) (mixed : (sequence n).IsFullyMixed)
    {who : Player} {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    {site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup)
      horizon scheduler who site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (history witness : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationHistory who (some (past, view)))
    {current witnessControl : (application setup timeouts leaks).Control}
    (historyState : history.1.state = some current)
    (witnessState : witness.1.state = some witnessControl)
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    (decodedW : decodedPoint setup witnessControl.execution.application.config = some w)
    (freeW : ∀ player, ¬ ProtocolState.OwesFailure player setup.program w)
    (irregularHistory : ¬ RegularTrace setup timeouts leaks bounds horizon scheduler (sequence
      n) who
      history.1.trace) :
    ∃ counterpart : (onePacketInformation setup timeouts leaks bounds horizon
        scheduler).InformationHistory who (some (past, view)),
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        counterpart.1.trace ∧
      ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
          (2 * horizon + 1) - 1 < 1 →
      ((onePacketInformation setup timeouts leaks bounds horizon scheduler).historyReachWeight
          (certificateProfile setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) history.1).toReal ≤
        (1 + ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
            (2 * horizon + 1) - 1)) /
          (1 - ((1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) ^
            (2 * horizon + 1) - 1)) *
          (slotError (scale n) (floor n) (trembleSlots setup bounds).card *
            (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
            counterpartFactor setup timeouts leaks bounds horizon scheduler sequence scale floor n ^
              (2 * horizon + 1)) *
        ((onePacketInformation setup timeouts leaks bounds horizon scheduler).historyReachWeight
          (certificateProfile setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) counterpart.1).toReal) := by
  classical
  set steps := certificateOperationalSteps (timeouts := timeouts) wellFormed sequence scale
    scale_pos scale_le_one small
    floor floor_pos floored covers capacity weights who error_tendsto
  have positive := certificate_mass_pos (timeouts := timeouts) wellFormed sequence scale scale_pos
    scale_le_one small
    floor floor_pos floored covers capacity weights who error_tendsto
  have errorNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card :=
    slotError_nonneg (scale_pos n).le (floor_pos n) _
  have K₁Nonneg : 0 ≤ 1 / floor n + slotError (scale n) (floor n)
      (trembleSlots setup bounds).card :=
    add_nonneg (div_nonneg zero_le_one (floor_pos n).le) errorNonneg
  obtain ⟨counterpart, regular, record⟩ := counterpart_of_intended_witness_repairs (timeouts :=
    timeouts)
    wellFormed covers mixed decision forced turn history witness historyState witnessState
    decodedW freeW covered
  obtain ⟨found, foundState, currentView⟩ := state_of_decision (timeouts := timeouts)
    (site := site) ⟨history.1, history.2.trans decision.symm⟩ decision
  rw [historyState, Option.some.injEq] at foundState
  subst found
  obtain ⟨found, foundState, witnessView⟩ := state_of_decision (timeouts := timeouts)
    (site := site) ⟨witness.1, witness.2.trans decision.symm⟩ decision
  rw [witnessState, Option.some.injEq] at foundState
  subst found
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change state = some current at historyState
  subst historyState
  let history : (onePacketInformation setup timeouts leaks bounds horizon
    scheduler).InformationHistory
      who (some (past, view)) := ⟨⟨some current, trace⟩, seen⟩
  have historyState : history.1.state = some current := rfl
  obtain ⟨⟨state, witnessTrace⟩, witnessSeen⟩ := witness
  change state = some witnessControl at witnessState
  subst witnessState
  let witness : (onePacketInformation setup timeouts leaks bounds horizon
    scheduler).InformationHistory
      who (some (past, view)) := ⟨⟨some witnessControl, witnessTrace⟩, witnessSeen⟩
  have witnessState : witness.1.state = some witnessControl := rfl
  have sameSource := (sourceViewOf_eq_decodedPoint (timeouts := timeouts) who
    history.1.trace).symm.trans
    ((congrArg (sourceViewOf setup timeouts leaks who) (currentView.trans witnessView.symm)).trans
      (sourceViewOf_eq_decodedPoint (timeouts := timeouts) who witness.1.trace))
  rw [decodedP, decodedW] at sameSource
  have sameView := Option.some.inj sameSource
  have freeWitness : ∀ point, decodedPoint setup witnessControl.execution.application.config =
      some point → ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
    intro point decoded player
    rw [decodedW, Option.some.injEq] at decoded
    subst decoded
    exact freeW player
  obtain ⟨second, secondReplay⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts)
    wellFormed witness.1.trace
    witnessControl witnessState freeWitness
  have secondState : second.state = some w :=
    (intendedHistory?_state (timeouts := timeouts) witness.1.trace secondReplay).trans decodedW
  have currentTurn : current.execution.application.publicView.ownTurn? who = some event := by
    rw [← currentView] at turn
    exact turn
  have readyOwn := readyOwn_of_ownTurn current.execution.application currentTurn
  have publicRecord := publicRecord_of_forced_information (timeouts := timeouts) decision forced
    ⟨history.1, history.2.trans decision.symm⟩ historyState
  have notOwed : ∀ point, decodedPoint setup current.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure who setup.program point := by
    intro point decoded owes
    rw [decodedP, Option.some.injEq] at decoded
    subst decoded
    exact freeW who ((owesFailure_iff_of_infoOf (timeouts := timeouts)
      (menu := bounds.onePacketMenu timeouts leaks) (horizon := horizon)
      (scheduler := scheduler) history witness decodedP decodedW).mp owes)
  have ownIntended := ownCompletionsIntended_of_notOwes (timeouts := timeouts) (bounds := bounds)
    wellFormed who
    history.1.trace current historyState notOwed
  have weight := upperSourceWeight_le_of_paired_responses (timeouts := timeouts) (steps := steps)
    positive n
    (initialFloor_pos setup timeouts leaks bounds horizon scheduler)
    (fun _ supported => initialFloor_le setup timeouts leaks bounds horizon scheduler supported)
    K₁Nonneg errorNonneg history.1.trace counterpart.1.trace record.symm regular
    (by
      intro control next imageControl imageNext prior joint legal realized imagePrior imageJoint
        imageLegal imageRealized isPrefix imagePrefix lengths actor acting other imageStep
      have endpoints := operationalRecord_eq_of_paired_prefixes (timeouts := timeouts) isPrefix
        imagePrefix record.symm
        (congrArg Nat.succ lengths)
      have beforeEq := (repair_operationalState_eq_of_record_eq (timeouts := timeouts) prior
        imagePrior
        (List.cons.inj endpoints).2).symm
      have afterEq := (List.cons.inj endpoints).1.symm
      have imageActing : imageControl.actor = some actor :=
        (congrArg (fun state : OperationalState setup timeouts leaks => state.actor)
          (Option.some.inj beforeEq)).trans acting
      have priorPrefix : TracePrefix prior history.1.trace :=
        (TracePrefix.extend .refl joint legal realized).trans isPrefix
      have forcedActor := forcedAgent_of_intended_witness_repairs (timeouts := timeouts) wellFormed
        independent
        observable covers
        covered other decision forced turn history witness historyState witnessState decodedW freeW
        prior joint legal realized isPrefix acting
      have canonical := disclosureCanonical_of_resolves (timeouts := timeouts) prior actor
        (disclosureResolves_along (timeouts := timeouts) wellFormed history.1.trace decodedP
          secondState sameView readyOwn
          prior priorPrefix other)
      apply certificate_responseMass_le_of_operationally_equal (timeouts := timeouts) wellFormed
        sequence scale scale_pos
        scale_le_one small floor floor_pos floored covers capacity weights who n prior joint legal
        realized imagePrior imageJoint imageLegal imageRealized acting imageActing other forcedActor
        canonical ?_ beforeEq afterEq imageStep
      intro response named responseEq submitted
      have moved := realized
      change some next ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
        scheduler
        (some control) joint).support at moved
      rw [transition_respond (timeouts := timeouts) control acting joint, PMF.mem_support_pure_iff]
        at moved
      have nextEq : next = ⟨control.remaining, none,
          control.execution.respond (application setup timeouts leaks) actor response⟩ := by
        simpa only [responseEq, Option.getD_some] using Option.some.inj moved
      subst next
      exact response_atTurn_of_forced_prefix (timeouts := timeouts) forced decision
        ⟨history.1, history.2.trans decision.symm⟩ historyState control.remaining actor other
        control.execution response (prior.extend joint legal realized) isPrefix named submitted)
    (by
      intro control next imageControl imageNext prior joint legal realized imagePrior imageJoint
        imageLegal imageRealized isPrefix imagePrefix lengths actor acting other imageStep
        regularPrior irregularStep
      have endpoints := operationalRecord_eq_of_paired_prefixes (timeouts := timeouts) isPrefix
        imagePrefix record.symm
        (congrArg Nat.succ lengths)
      have beforeEq := (repair_operationalState_eq_of_record_eq (timeouts := timeouts) prior
        imagePrior
        (List.cons.inj endpoints).2).symm
      have afterEq := (List.cons.inj endpoints).1.symm
      have imageActing : imageControl.actor = some actor :=
        (congrArg (fun state : OperationalState setup timeouts leaks => state.actor)
          (Option.some.inj beforeEq)).trans acting
      obtain ⟨ownPrior, recordPrior⟩ := ownCompletionsIntended_and_publicRecord_of_tracePrefix
        (timeouts := timeouts) prior
        ((TracePrefix.extend .refl joint legal realized).trans isPrefix) ownIntended
        (fun control same => by
          have sameControl := Option.some.inj (historyState.symm.trans same)
          cases sameControl
          exact publicRecord)
      obtain ⟨point, decodedBefore, intended⟩ := intended_of_regular (timeouts := timeouts)
        wellFormed (sequence n) who
        prior control rfl (recordPrior control rfl) regularPrior ownPrior
      have forcedAll : ∀ player, ForcedState setup timeouts leaks player (some control) := fun
        player =>
        (forcedState_iff_decodedPoint (timeouts := timeouts) control).mpr
          ⟨point, decodedBefore, forcedPoint_of_intended player intended⟩
      exact certificate_irregularResponseMass_le_of_operationally_equal (timeouts := timeouts)
        wellFormed sequence scale
        scale_pos scale_le_one small floor floor_pos floored covers capacity weights who n prior
        joint legal realized imagePrior imageJoint imageLegal imageRealized acting imageActing other
        (forcedAll who)
        ⟨⟨some control, prior⟩, (bounds.onePacketMenu timeouts leaks).info (initialLaw setup)
          horizon scheduler actor prior, forcedAll actor⟩
        irregularStep beforeEq afterEq imageStep)
  have upper := weight.2 irregularHistory
  have one_le : 1 ≤ counterpartFactor setup timeouts leaks bounds horizon scheduler sequence scale
      floor n := le_max_left _ _
  have length : history.1.trace.length ≤ 2 * horizon + 1 :=
    le_trans (Nat.le_add_left _ _) (trace_length_le (timeouts := timeouts) history.1.trace)
  have powerLe := pow_le_pow_right₀ one_le length
  have imageNonneg := othersSourceWeight_nonneg (timeouts := timeouts) (sequence n) who
    counterpart.1.trace
  have front : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
      (1 + steps.error n) := mul_nonneg errorNonneg (by
        linarith [steps.error_nonneg n])
  have upperBound := upper.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left powerLe front) imageNonneg)
  have sameRecall : ownerRecall setup timeouts leaks who counterpart.1.state =
      ownerRecall setup timeouts leaks who history.1.state := by
    rw [ownerRecall_eq_of_infoOf setup timeouts leaks
        ((onePacket_infoOf (timeouts := timeouts) who counterpart.1.trace).symm.trans
          counterpart.2),
      ownerRecall_eq_of_infoOf setup timeouts leaks ((onePacket_infoOf (timeouts := timeouts) who
        history.1.trace).symm.trans
        history.2)]
  have ratioNonneg : 0 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
      (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
      counterpartFactor setup timeouts leaks bounds horizon scheduler sequence scale floor n ^
        (2 * horizon + 1) :=
    mul_nonneg (mul_nonneg errorNonneg (by linarith))
      (pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _)
  refine ⟨counterpart, regular, fun errorSmall => ?_⟩
  exact reach_le_of_counterpart (timeouts := timeouts) (IrregularStepBound.ofResponseMass (timeouts
    := timeouts) steps positive) n
    history.1.trace counterpart.1.trace regular record sameRecall ratioNonneg upperBound
    errorSmall

end Vegas
