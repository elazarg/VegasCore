/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterDeparture
import Interaction.ReactiveTrafficState
import Interaction.ReactiveLocalContinuation

/-! # One-step roster-rule breach at every additional roster response

The certificate covers every effective response outside the retained menu at
any retained information history. It uses the actual native behavioral step;
subsequent strategy choices do not affect the already recorded transmission.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (reveals : setup.program.RevealOnly)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

local notation "Native" => ReactiveApplication.ResponseMenu.information
  (MessageBounds.menu bounds (runtime setup) leaks) (initialLaw setup)
  (List.length (rosterPlan setup rosters)) (rosterScheduler setup leaks rosters network)

include reveals openable in
open Classical in
/-- Committing any additional effective response at a retained site records an
attributable violation after the actual first behavioral step. Later profile
choices play no role in the certificate. -/
theorem roster_extra_choice_traffic [setup.FiniteInitialLaw]
    (profile : Profile (Native).behavioralSignature)
    (who : Player) (site : ((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationSite
        who)
    (action : (Native).Choice who
      (((rosterMenu_in_effective setup leaks bounds rosters).actionRestriction (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).site who
          site).1)
    (extra : action ∉ Set.range
      (((rosterMenu_in_effective setup leaks bounds rosters).actionRestriction (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).choice
          who site.1))
    (history : ((rosterMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).InformationHistory
        who site.1)
    (next : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (supported : next ∈ ((Native).runBehavioralFrom
      (Profile.update (sig := (Native).behavioralSignature)
        profile who ((profile who).commit
          (((rosterMenu_in_effective setup leaks bounds rosters).actionRestriction (initialLaw
        setup)
            (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).site who site).1
          action))
      1 (((rosterMenu_in_effective setup leaks bounds rosters).actionRestriction (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).history
          history.1)).support) :
    ∃ record ∈ (application setup leaks).stateTraffic next.state,
      record.input.envelope.sender = who ∧
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  classical
  let sourceMenu := rosterMenu setup leaks bounds rosters
  let targetMenu := bounds.menu (runtime setup) leaks
  let included := rosterMenu_in_effective setup leaks bounds rosters
  let initial := initialLaw setup
  let horizon := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  let restriction := included.actionRestriction initial horizon scheduler
  rcases site with ⟨info, occurs⟩
  have active := InformationModel.InformationSite.active
    (sourceMenu.information initial horizon scheduler) ⟨info, occurs⟩ history
  cases current : history.1.state with
  | none => simp only [current, ReactiveApplication.ResponseMenu.protocol,
      ReactiveApplication.actor, Option.bind_none, reduceCtorEq] at active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      have actorEq : actor = some who := by
        simpa only [current, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          Option.bind_some] using active
      subst actor
      have observed : info = some (execution.recall who,
          execution.observe (application setup leaks) who) := by
        have seen := history.2
        change (sourceMenu.signals initial horizon scheduler).infoOf who history.1.trace = info
          at seen
        rw [sourceMenu.info, current] at seen
        simpa only [ReactiveApplication.observe, ↓reduceIte] using seen.symm
      subst info
      change (Native).Choice who
        (some (execution.recall who, execution.observe (application setup leaks) who)) at action
      obtain ⟨response, selected, effective, excluded⟩ :=
        included.extra_choice_response initial horizon scheduler who _ _ action extra
      obtain ⟨record, recorded, attributed, forbidden⟩ :
          ∃ record, (application setup leaks).trafficStep
              (some ⟨remaining, some who, execution⟩)
              (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) =
                [record] ∧ record.input.envelope.sender = who ∧
            permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
        have actualTrace := history.1.trace
        rw [current] at actualTrace
        exact roster_extra_traffic setup leaks bounds rosters network reveals openable
          who _ actualTrace rfl response effective excluded
      let native := restriction.history history.1
      have nativeState : native.state = some ⟨remaining, some who, execution⟩ := current
      have nativeInfo : (Native).infoOf who native.trace =
          some (execution.recall who, execution.observe (application setup leaks) who) :=
        (included.observed initial horizon scheduler who history.1).trans history.2
      let chosen : (Native).Choice who
          ((Native).infoOf who native.trace) :=
        ⟨action.1, by simpa only [nativeInfo] using action.2⟩
      have one := targetMenu.run_commit_response initial horizon scheduler profile native who
        remaining execution nativeState chosen response selected
      change (targetMenu.information initial horizon scheduler).infoOf who native.trace = _
        at nativeInfo
      have stateLaw : ((Native).runBehavioralFrom
          (Profile.update (sig :=
            (Native).behavioralSignature)
            profile who ((profile who).commit
              (some (execution.recall who,
                execution.observe (application setup leaks) who)) action))
          1 native).map History.state =
            PMF.pure (some ⟨remaining, none,
              execution.respond (application setup leaks) who response⟩) := by
        have transport
            (first last : (Native).InfoState who)
            (same : first = last)
            (left : (Native).Choice who first)
            (right : (Native).Choice who last)
            (value : left.1 = right.1) :
            (profile who).commit first left = (profile who).commit last right := by
          subst last
          have equal : left = right := Subtype.ext value
          subst right
          rfl
        have installed := transport _ _ nativeInfo chosen action rfl
        rw [installed] at one
        exact one
      have nextState : next.state = some ⟨remaining, none,
          execution.respond (application setup leaks) who response⟩ := by
        have inMap : next.state ∈ (PMF.pure (some ⟨remaining, none,
            execution.respond (application setup leaks) who response⟩)).support := by
          rw [← stateLaw, PMF.support_map]
          exact ⟨next, supported, rfl⟩
        exact (PMF.mem_support_pure_iff _ _).mp inMap
      let original := sourceMenu.toRawHistory initial horizon scheduler history.1
      have transition : some ⟨remaining, none,
          execution.respond (application setup leaks) who response⟩ ∈
            ((application setup leaks).transition initial horizon scheduler original.state
              (fun _ => some response)).support := by
        change _ ∈ ((application setup leaks).transition initial horizon scheduler history.1.state
          (fun _ => some response)).support
        simp only [current, ReactiveApplication.transition, Option.getD_some,
          PMF.mem_support_pure_iff _ _]
      have audit := (application setup leaks).stateTraffic_transition initial horizon scheduler
        original (fun _ => some response) _ transition
      refine ⟨record, ?_, attributed, forbidden⟩
      rw [nextState, audit]
      change record ∈ _ ++ (application setup leaks).trafficStep history.1.state _
      rw [current, recorded]
      exact List.mem_append_right _ (List.mem_singleton_self _)

end Vegas
