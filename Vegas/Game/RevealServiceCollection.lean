/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceEnforcement
import Vegas.Game.RevealServiceWatcher
import Vegas.Game.RevealServiceCompletion
import Interaction.ReactiveRoundReachability

/-! # Monitoring bounds at behavioral continuation histories

The existing finite-menu evaluator connects focal response deviations to the
actual reserved inclusion and passive reporting block. The conclusion concerns
the standard behavioral continuation law. Clean execution and sampling
hypotheses remain operational premises; no posterior or incentive premise is introduced.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Evaluation from an owner activation, including its immediate response. -/
theorem finish_owner_response (watcher owner : Player)
    (players : Player → (application setup leaks).Policy)
    (before rest : List (ServiceInstruction (graph setup)))
    (split : plan setup watcher = before ++ .player owner :: rest)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length + 1) :
    (application setup leaks).finish (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) players (some ⟨rest.length, some owner, execution⟩) =
      (players owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind
        (fun response => ((runtime setup).runInteractionPlan leaks players
          ((runtime setup).reportNetwork leaks watcher) rest
          (execution.respond (application setup leaks) owner response)).map
            (application setup leaks).finished) := by
  simp only [ReactiveApplication.finish, ReactiveApplication.resume,
    ReactiveApplication.invoke, PMF.bind_map, PMF.map_bind]
  apply bind_congr_on_support _
  intro response _
  congr 1
  apply suffix_rounds setup leaks watcher players (before ++ [.player owner]) rest
  · simpa only [List.append_assoc, List.singleton_append] using split
  · simpa only [ReactiveApplication.respond_environmentRecall,
      List.length_append, List.length_singleton] using position

/-- The first three remaining instructions are exactly the reserved inclusion
and ordinary-view report block. The remainder uses the unchanged scheduler. -/
theorem finish_owner_report (watcher owner : Player)
    (players : Player → (application setup leaks).Policy)
    (before rest : List (ServiceInstruction (graph setup))) (event : (graph setup).EventId)
    (split : plan setup watcher = before ++ .player owner :: .includeLatest event owner ::
      .player watcher :: .wire :: rest)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length + 1) :
    (application setup leaks).finish (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) players (some ⟨rest.length + 3, some owner, execution⟩) =
      (players owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind
        (fun response => ((((runtime setup).interactionStep leaks players
          ((runtime setup).reportNetwork leaks watcher) (.includeLatest event owner)
          (execution.respond (application setup leaks) owner response)).bind
          ((application setup leaks).reportInclusion players watcher)).bind
          ((application setup leaks).runRounds (scheduler setup leaks watcher) players
            rest.length)).map (application setup leaks).finished) := by
  have finish := finish_owner_response setup leaks watcher owner players before
    (.includeLatest event owner :: .player watcher :: .wire :: rest) split execution position
  simp only [List.length_cons] at finish
  rw [show rest.length + 3 = rest.length + 1 + 1 + 1 by omega, finish]
  apply bind_congr_on_support _
  intro response _
  congr 1
  let segment : List (ServiceInstruction (graph setup)) :=
    [.includeLatest event owner, .player watcher, .wire]
  change (runtime setup).runInteractionPlan leaks players _ (segment ++ rest) _ = _
  rw [(runtime setup).runInteractionPlan_append]
  have report : (runtime setup).runInteractionPlan leaks players
      ((runtime setup).reportNetwork leaks watcher) segment
      (execution.respond (application setup leaks) owner response) =
      ((runtime setup).interactionStep leaks players ((runtime setup).reportNetwork leaks watcher)
        (.includeLatest event owner)
        (execution.respond (application setup leaks) owner response)).bind
          ((application setup leaks).reportInclusion players watcher) := by
    rw [show segment = .includeLatest event owner :: [.player watcher, .wire] from rfl,
      runInteractionPlan]
    apply bind_congr_on_support _
    intro next _
    exact (runtime setup).run_report_plan leaks players watcher next
  rw [← report]
  apply bind_congr_on_support _
  intro next reached
  symm
  apply suffix_rounds setup leaks watcher players (before ++ [.player owner] ++ segment) rest
  · simpa only [segment, List.append_assoc, List.cons_append, List.nil_append,
      List.singleton_append] using split
  · have advanced := (runtime setup).runInteractionPlan_recall leaks players
      ((runtime setup).reportNetwork leaks watcher) segment
      (execution.respond (application setup leaks) owner response) next reached
    rw [advanced, ReactiveApplication.respond_environmentRecall]
    simp only [List.length_append, List.length_singleton, position]

/-- Every ordinary-player decision in any menu has the reporting suffix and
remaining horizon used above. The position is recovered from legal history. -/
theorem owner_continuation_layout (responses : (application setup leaks).ResponseMenu)
    (watcher owner : Player) (different : owner ≠ watcher)
    (reveals : setup.program.RevealOnly) (control : (application setup leaks).Control)
    (trace : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).Trace (some control))
    (active : control.actor = some owner) :
    ∃ (event : (graph setup).EventId) (before rest : List (ServiceInstruction (graph setup))),
      (graph setup).actor? event = some owner ∧
      plan setup watcher = before ++ .player owner :: .includeLatest event owner ::
        .player watcher :: .wire :: rest ∧
      control.execution.environmentRecall.length = before.length + 1 ∧
      control.remaining = rest.length + 3 := by
  obtain ⟨event, located⟩ := raw_decision_calendar setup leaks watcher owner reveals control
    (responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) trace) active
  rcases located with ⟨position, owned⟩ | ⟨_, same⟩
  swap
  · exact (different same).elim
  obtain ⟨suffix, split⟩ := plan_split_at setup watcher event
  rw [block_of_owner setup watcher owner event owned] at split
  let before := planPrefix setup watcher event.val
  let rest := List.replicate (event.val + 1) (.tick : ServiceInstruction (graph setup)) ++
    .expire event :: suffix
  have split' : plan setup watcher = before ++ .player owner :: .includeLatest event owner ::
      .player watcher :: .wire :: rest := by
    simpa only [before, rest, List.append_assoc, List.cons_append, List.nil_append] using split
  have position' : control.execution.environmentRecall.length = before.length + 1 := by
    simp only [before,
      planPrefix_length setup watcher reveals event.val event.isLt.le]
    omega
  have accounted := (responses.roundSupported_uniform (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) trace).1
  change control.execution.environmentRecall.length + control.remaining =
    (plan setup watcher).length at accounted
  rw [split', List.length_append] at accounted
  simp only [List.length_cons] at accounted
  exact ⟨event, before, rest, owned, split', position', by omega⟩

/-- The generic theorem's remaining-depth fuel suffices for complete native
evaluation at every legal menu history. -/
theorem menu_remaining_fuel (responses : (application setup leaks).ResponseMenu)
    (watcher : Player)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History) :
    (application setup leaks).rank (horizon setup watcher) history.state ≤
      2 * horizon setup watcher + 1 - history.trace.length := by
  have bounded := (application setup leaks).trace_bound (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
    (responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) history.trace)
  rw [responses.toRawTrace_length] at bounded
  omega

/-- Evidence read from the actual native control state; no private monitor
observation or submission request is used in this settlement predicate. -/
def departureAtState (owner : Player) : (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => departureEvidence setup leaks owner control.execution

variable [Fintype Player]

open Classical in
/-- A focal behavioral submission at any legal watched information history
inherits the actual monitor's collection bound. Every later behavioral choice
is arbitrary within W; the reporter equation follows from its fixed menu.
The clean checkpoint hypotheses are exactly those used by packet monitoring. -/
theorem watched_commit_collection (bounds : MessageBounds (graph setup))
    (watcher owner : Player) (different : owner ≠ watcher)
    (reveals : setup.program.RevealOnly)
    (profile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature)
    (site : (watchedInformation setup leaks bounds watcher).InformationSite owner)
    (history : (watchedInformation setup leaks bounds watcher).InformationHistory owner site.1)
    (control : (application setup leaks).Control) (state : history.1.state = some control)
    (submission : WitnessedSubmission (graph setup))
    (action : (watchedInformation setup leaks bounds watcher).Choice owner site.1)
    (chosen : action.1 = some ⟨some (.submit submission)⟩)
    (serials : control.execution.network.SerialsBeforeNext)
    (pendingPublished : ∀ message ∈ control.execution.network.pending,
      message.id ∈ control.execution.network.ledger.map Message.id)
    (knownPublished : ∀ message ∈ control.execution.network.known watcher,
      message.id ∈ control.execution.network.ledger.map Message.id)
    (departure :
      let execution := control.execution
      let next := (application setup leaks).submit execution.application owner submission
      let packet := submission.emit next owner (execution.network.known owner)
      (application setup leaks).handle next
          ⟨(owner, execution.network.nextSerial owner), packet⟩ = none ∨
        certifiedOpening packet = false)
    (fuel : Nat)
    (enough : 2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    let submitted := control.execution.respond (application setup leaks) owner
      ⟨some (.submit submission)⟩
    ((leaks watcher submitted.network.pending).toOuterMeasure
        {selected | (owner, control.execution.network.nextSerial owner) ∈ selected}).toReal ≤
      (((watchedInformation setup leaks bounds watcher).runBehavioralFrom
        (Profile.update (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
          profile owner ((profile owner).commit site.1 action)) fuel history.1).toOuterMeasure
              {final | departureAtState setup leaks owner final.state}).toReal := by
  classical
  let app := application setup leaks
  let responses := watchedMenu setup leaks bounds watcher
  let changed := Profile.update
    (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
    profile owner ((profile owner).commit site.1 action)
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) changed
  have active := InformationModel.InformationSite.active
    (watchedInformation setup leaks bounds watcher) site history
  change app.actor history.1.state = some owner at active
  rw [state] at active
  change control.actor = some owner at active
  have trace : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).Trace (some control) := state ▸ history.1.trace
  obtain ⟨event, before, rest, _owned, split, position, remaining⟩ :=
    owner_continuation_layout setup leaks responses watcher owner different reveals control trace
      active
  have observed : site.1 = some (control.execution.recall owner,
      control.execution.observe app owner) := by
    calc
      site.1 = (watchedInformation setup leaks bounds watcher).infoOf owner history.1.trace :=
        history.2.symm
      _ = app.observe owner history.1.state :=
        responses.info (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) owner history.1.trace
      _ = _ := by rw [state]; simp only [ReactiveApplication.observe, active, ↓reduceIte]
  have response : players owner (control.execution.recall owner)
      (control.execution.observe app owner) = PMF.pure ⟨some (.submit submission)⟩ := by
    simp only [players, changed, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      Profile.update_same, PMF.map_comp, ReactiveApplication.ResponseMenu.rawChoice,
      Function.comp_def]
    change (((profile owner).commit site.1 action)
      (some (control.execution.recall owner, control.execution.observe app owner))).map
        (fun selected => selected.1.getD ⟨none⟩) = _
    rw [← observed, InformationModel.BehavioralPolicy.commit_self, PMF.pure_map, chosen]
    rfl
  have reporter : players watcher = app.reportFirstUnpublished :=
    watched_decode_reports setup leaks bounds watcher changed
  have exactLaw := responses.run_eq_finish (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) changed fuel history.1
    ((menu_remaining_fuel setup leaks responses watcher history.1).trans enough)
  have finish := finish_owner_report setup leaks watcher owner players before rest event split
    control.execution position
  have controlEq : control = ⟨rest.length + 3, some owner, control.execution⟩ := by
    cases control
    exact congrArg₂ (fun time who => ReactiveApplication.Control.mk time who _)
      remaining active
  rw [state, controlEq, finish, response, PMF.pure_bind] at exactLaw
  have monitored := reserved_report_departure_lower setup leaks owner watcher different players
    reporter control.execution event submission serials pendingPublished knownPublished departure
    (scheduler setup leaks watcher) rest.length
  have mapped := congrArg
    (fun law : PMF app.ProtocolState =>
        (law.toOuterMeasure {s | departureAtState setup leaks owner s}).toReal)
    exactLaw
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at mapped
  exact monitored.trans_eq mapped.symm

end Vegas
