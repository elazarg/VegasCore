/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestDecision
import Vegas.Game.OnePacketLawApproximation

/-! # As-if-honest play agrees with the first-turn clients where they play

The as-if-honest profile of the one-packet game, read as native policies,
sends the as-if-honest response when the one-packet menu offers it and is
silent otherwise (`Vegas.decodeProfile_honestProfile`).

Suppose the canonical menu retains every first canonical packet sent within its
deadline (`Vegas.RetainsFirstCanonical`). Then, for a well-formed setup under
the asynchronous contract with timely delays, at every input the scheduler
queries along a run of the first-turn clients of the intended effective
opening, as-if-honest play responds exactly as those clients do
(`Vegas.honestPolicy_eq_openingClients`): without an own turn both are silent;
after an earlier turn at the event both are silent, the clients by their turn
count and as-if-honest play because its packet repeats an own submission; and
at the first turn both make the compiled decision of the effective opening,
which the one-packet menu offers whenever it transmits.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Decoded

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

open Classical in
/-- A response the one-packet menu offers, and silence otherwise. -/
def onePacketFilter (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    (application setup leaks).Action :=
  if response ∈ bounds.onePacketActions (runtime setup) leaks who past view then response
  else ⟨none⟩

/-- **As-if-honest play as native policies.** -/
theorem decodeProfile_honestProfile (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (bounds.onePacketMenu (runtime setup) leaks).decodeProfile initial horizon scheduler
        (honestProfile setup leaks bounds initial horizon scheduler assessment) who past view =
      (honestResponse setup leaks assessment who past view).map
        (onePacketFilter bounds who past view) := by
  classical
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, honestProfile, honestChoice, PMF.map_comp]
  congr 1
  funext response
  simp only [Function.comp_apply, responseChoice, onePacketFilter]
  split <;> rfl

end Decoded

section Static

/-- Every execution reached by rounds from initialization decodes to a point
carrying the program's registry and publication status. -/
theorem roundsFrom_static (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (profile : BehavioralProfile setup.program)
    (count : Nat) (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    DecodedExecution setup leaks profile
      (ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)) execution := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateMem
  refine DecodedExecution.runRounds (fun state joint target holds reached =>
    ProtocolState.staticAt_step setup.program [] (Revelations.initial setup.context) state joint
      target holds reached) scheduler players count _ ?_ execution reached
  let residual := SourceResidual.initial setup profile initial
  refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
  change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial (graph := graph setup)
    (setup.eventInputs initial)).config = some point at decoded
  rw [residual.decode, Option.some.injEq] at decoded
  subst decoded
  exact ProtocolState.staticAt_entry setup.program _ rfl rfl

end Static

section Agreement

variable (setup leaks) in
/-- **Retention of first canonical packets.** At an owner's turn at an event
its recall has not submitted for, while a fresh call still fits the deadline,
every transmitting canonical decision is retained by the canonical menu. -/
def RetainsFirstCanonical [Fintype Player] (bounds : MessageBounds (graph setup))
    (bound : (graph setup).EventId → Nat) : Prop :=
  ∀ who (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (action : (graph setup).Action event),
    view.application.publicView.ownTurn? who = some event →
    (runtime setup).eventRecorded leaks past event = false →
    view.application.publicView.InclusionFitsDeadline (runtime setup) bound event →
    ((runtime setup).canonicalServiceDecision leaks who past view event action).transmission ≠
      none →
    (runtime setup).canonicalServiceDecision leaks who past view event action ∈
      bounds.canonicalActions (runtime setup) leaks who past view

/-- **As-if-honest play agrees with the first-turn clients.** For a
well-formed setup, under the asynchronous contract with timely delays and
retention of first canonical packets, at every input the scheduler queries
within the horizon along a run of the first-turn clients of the intended
effective opening, as-if-honest play read as native policies responds exactly
as those clients do. -/
theorem honestPolicy_eq_openingClients [Fintype Player] (bounds : MessageBounds (graph setup))
    (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsFirstCanonical setup leaks bounds bound) {count : Nat}
    (within : count < horizon) {execution : (application setup leaks).Execution}
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (openingClients setup leaks bound turns assessment.strategy) count).support)
    {command : (application setup leaks).Command}
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support)
    {middle : (application setup leaks).Execution}
    (moved : middle ∈ (execution.environmentStep (application setup leaks) command).support)
    {who : Player} (active : command.actor? (application setup leaks) = some who) :
    (bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon scheduler
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) who
        (middle.recall who) (middle.observe (application setup leaks) who) =
      openingClients setup leaks bound turns assessment.strategy who (middle.recall who)
        (middle.observe (application setup leaks) who) := by
  classical
  let app := application setup leaks
  let players := openingClients setup leaks bound turns assessment.strategy
  have commandEq : command = .activate who := by
    cases command with
    | activate actor =>
        exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
    | wait | «include» _ | application _ => cases active
  subst commandEq
  have appEq := activation_application setup leaks execution middle who moved
  have recallEq := app.environmentStep_recall execution middle (.activate who) moved
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
    within.le execution supported
  rw [show horizon - count = (horizon - count - 1) + 1 by omega] at trace
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    (horizon - count - 1) execution middle (.activate who) trace selected moved
  change app.protocol (initialLaw setup) horizon scheduler |>.Trace
    (some ⟨horizon - count - 1, some who, middle⟩) at middleTrace
  have answered := roundsFrom_activationsAnswered count execution supported
  have atTurn : OwnSubmissionsAtTurn setup leaks middle who := by
    have facts := (roundsFrom_turnFacts setup leaks (fun player =>
      sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns
        (firstTurnTiming setup turns .sequential)
        (setup.intendedOpeningProfile assessment.strategy) player) count execution
        supported).1.own who
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact facts
  rw [decodeProfile_honestProfile]
  cases turnCase : middle.application.publicView.ownTurn? who with
  | none =>
      have view : (middle.observe app who).application.publicView.ownTurn? who = none := turnCase
      rw [honestResponse_of_no_turn setup leaks assessment who _ _ view, PMF.pure_map]
      have silenceKept : onePacketFilter bounds who (middle.recall who) (middle.observe app who)
          ⟨none⟩ = ⟨none⟩ := by
        unfold onePacketFilter
        split <;> rfl
      rw [silenceKept]
      unfold openingClients serviceTurnPolicy
      rw [view]
      rfl
  | some event =>
      have view : (middle.observe app who).application.publicView.ownTurn? who = some event :=
        turnCase
      have owned := (PublicView.ownTurn?_spec _ who event turnCase).2
      have silenceKept : onePacketFilter bounds who (middle.recall who) (middle.observe app who)
          ⟨none⟩ = ⟨none⟩ := by
        unfold onePacketFilter
        split <;> rfl
      by_cases seen : SeenTurn who event (middle.recall who)
      · rw [openingClients_later_silent bound turns assessment.strategy who _ _ event view seen]
        have recorded : (runtime setup).eventRecorded leaks (middle.recall who) event = true := by
          rw [recallEq]
          exact openingClients_recorded_of_seen wellFormed contract timely turns
            assessment.strategy within.le supported who event owned (by rw [← recallEq]; exact seen)
        refine (map_congr_on_support _ (g := fun _ => (⟨none⟩ : app.Action)) ?_).trans
          (PMF.map_const _ _)
        intro response chosen
        rcases mem_support_honestResponse setup leaks assessment who _ _ event view response
            chosen with rfl | ⟨action, graphAction, _, _, rfl⟩
        · exact silenceKept
        · unfold onePacketFilter
          split
          · rename_i member
            cases transmits : ((runtime setup).canonicalServiceDecision leaks who
                (middle.recall who) (middle.observe app who) event graphAction).transmission with
            | none =>
                generalize (runtime setup).canonicalServiceDecision leaks who (middle.recall who)
                  (middle.observe app who) event graphAction = response at transmits ⊢
                rcases response with ⟨transmission⟩
                change transmission = none at transmits
                rw [transmits]
            | some material =>
                exact (canonical_not_onePacket_of_recorded bounds middleTrace who event recorded
                  graphAction material transmits member).elim
          · rfl
      · have first : serviceTurn setup .sequential (rankDeadline setup .sequential) leaks who event
            (middle.recall who) (middle.observe app who) = some 0 := by
          change (if (middle.observe app who).application.publicView.ownTurn? who = some event
            then some ((middle.recall who).countP fun entry =>
              decide (entry.beforeView.application.publicView.ownTurn? who = some event))
            else none) = some 0
          rw [ite_eq_left view ..]
          apply congrArg some
          exact List.countP_eq_zero.mpr fun entry member earlier =>
            seen ⟨entry, member, of_decide_eq_true earlier⟩
        have unrecorded := sourceServiceFirstTurn_unrecorded atTurn first
        have ready : execution.application.config.cut.Ready event := by
          rw [← appEq]
          exact (middle.application.publicView_eventReady event).mp
            (PublicView.ownTurn?_spec _ who event turnCase).1
        have firstBefore : serviceTurn setup .sequential (rankDeadline setup .sequential) leaks who
            event (execution.recall who) (middle.observe app who) = some 0 := by
          rw [← recallEq]
          exact first
        have fits := firstTurn_inclusionFits contract timely trace answered owned ready firstBefore
        have fitsMiddle : (middle.observe app who).application.publicView.InclusionFitsDeadline
            (runtime setup) bound event := by
          change middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event
          rw [appEq]
          exact fits
        let opening := setup.intendedOpeningProfile assessment.strategy
        have opportunity : openingClients setup leaks bound turns assessment.strategy who
            (middle.recall who) (middle.observe app who) =
            (serviceCanonicalPolicy setup .sequential (rankDeadline setup .sequential) leaks
              opening who (middle.recall who) (middle.observe app who)).bind fun response =>
                if response.transmission = none then app.silentPolicy (middle.recall who)
                  (middle.observe app who)
                else PMF.pure response := by
          rw [openingClients, sourceServiceTurnPolicy_firstTurn owned first]
          unfold serviceCanonicalOpportunity
          simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsMiddle]
          rfl
        rw [opportunity]
        obtain ⟨rank, ⟨residual⟩, intendedHolds⟩ := openingClients_intended (profile := opening)
          wellFormed contract timely turns assessment.strategy count within.le execution supported
        obtain ⟨staticRank, ⟨staticResidual⟩, staticHolds⟩ :=
          roundsFrom_static scheduler players opening count execution supported
        have sameRank := isPrefix_unique staticResidual.checkpoint.ordered
          residual.checkpoint.ordered
        subst sameRank
        have decodedMiddle : sourceServicePrefix? setup staticRank middle.application.config =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
          rw [appEq]
          exact residual.decode
        have orderedMiddle : middle.application.config.cut.IsPrefix staticRank := by
          rw [appEq]
          exact residual.checkpoint.ordered
        rw [honestResponse_eq_openingCanonical assessment middle staticRank orderedMiddle _
          decodedMiddle (staticHolds _ residual.decode) (intendedHolds _ residual.decode) who event
          turnCase]
        rw [show sourceServiceCanonicalPolicy setup leaks opening = serviceCanonicalPolicy setup
          .sequential (rankDeadline setup .sequential) leaks opening from rfl,
          ← PMF.bind_pure_comp]
        apply bind_congr_on_support _
        intro response chosen
        rw [sourceServiceCanonicalPolicy_at_event setup leaks opening who middle event turnCase
          owned, PMF.mem_support_map_iff] at chosen
        obtain ⟨graphAction, _, rfl⟩ := chosen
        cases transmits : ((runtime setup).canonicalServiceDecision leaks who (middle.recall who)
            (middle.observe app who) event graphAction).transmission with
        | none =>
            simp only [↓reduceIte]
            generalize (runtime setup).canonicalServiceDecision leaks who (middle.recall who)
              (middle.observe app who) event graphAction = response at transmits ⊢
            rcases response with ⟨transmission⟩
            change transmission = none at transmits
            subst transmits
            exact congrArg PMF.pure silenceKept
        | some material =>
            simp only [reduceCtorEq, ↓reduceIte]
            have member := canonical_mem_onePacket setup leaks bounds who (middle.recall who)
              (middle.observe app who) _
              (retains who (middle.recall who) (middle.observe app who) event graphAction view
                unrecorded fitsMiddle (by rw [transmits]; exact Option.some_ne_none material))
              (fun chosenMaterial sends => canonicalServiceDecision_countPermits middleTrace who
                event turnCase unrecorded graphAction chosenMaterial sends)
            simp only [Function.comp_apply, onePacketFilter]
            split
            · rfl
            · rename_i absent
              exact (absent member).elim

end Agreement

end Vegas
