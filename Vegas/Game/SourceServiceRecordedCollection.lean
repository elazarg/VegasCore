/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDuplicatePackets

/-! # Collection after a locally recorded extra response

The player's own recall identifies an earlier submission for the named event.
Committing a further response creates a different actual identifier. Both traffic
records persist, and authentic final-record coverage applies to whichever one
the final settlement forbids. The bound concerns total one-time charge from a
clear risk-menu prefix, not renewed collection after an already collected fine.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The response names an event already submitted in the player's own recall.
This reads only recalled actions and the chosen response, with no hidden state. -/
def recordedServiceResponse (past : List (application setup leaks).PlayerEntry)
    (response : (application setup leaks).Action) : Prop :=
  ∃ event, (runtime setup).eventRecorded leaks past event = true ∧
    (runtime setup).submittedEvent? leaks response = some event

/-- A local recorded response is excluded by the risk menu at a clear input.
No receipt, final verdict or anticipated monitoring is used in this check. -/
theorem recordedServiceResponse_not_risk [Fintype Player]
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (clear : (runtime setup).serviceRisk leaks bound who past view = false)
    (recorded : recordedServiceResponse setup leaks past response) :
    response ∉ bounds.riskActions (runtime setup) leaks bound who past view := by
  intro member
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who past view clear] at member
  have first := bounds.canonicalActions_firstSubmission (runtime setup) leaks who past view
    response member
  obtain ⟨event, earlier, submitted⟩ := recorded
  rw [(runtime setup).firstSubmission_false_of_recorded leaks past event earlier response
    submitted] at first
  cases first

/-- An information-local recorded extra choice. The same recall and selected
response determine this predicate throughout the native information fiber. -/
def recordedServiceChoice (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) (who : Player)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info) : Prop :=
  ∃ past view response, info = some (past, view) ∧ choice.1 = some response ∧
    recordedServiceResponse setup leaks past response

variable {setup leaks} [Fintype Player]

open Classical in
/-- A committed locally recorded extra response has the backend's collection
bound under every later behavioral policy. The prefix is actually legal in the
risk menu and has clear owner risk; prior packet soundness is derived from it. -/
theorem recordedServiceChoice_collection_committed
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (menu : (application setup leaks).ResponseMenu)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    {delay : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (backend : EvidenceReportService (SettledEvidence setup))
    (profile : ∀ player,
      (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (riskTrace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).Trace history.state)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (info : (menu.information (initialLaw setup) horizon scheduler).InfoState who)
    (choice : (menu.information (initialLaw setup) horizon scheduler).Choice who info)
    (observed : (menu.information (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info)
    (classified : recordedServiceChoice setup leaks menu horizon scheduler who info choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
        (Profile.update
          (sig := (menu.information (initialLaw setup) horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks backend.sample) final.state who) := by
  obtain ⟨past, view, response, inputEq, selected, recorded⟩ := classified
  have observedInput : info = (application setup leaks).observe who history.state :=
    observed.symm.trans (menu.info (initialLaw setup) horizon scheduler who history.trace)
  rw [current] at observedInput
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedInput
  have same := Option.some.inj (inputEq.symm.trans observedInput)
  have pastEq := congrArg Prod.fst same
  dsimp only at pastEq
  rw [pastEq] at recorded
  subst info
  let app := application setup leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let protocol := menu.protocol (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let observe := fun final : protocol.History =>
    (runtime setup).serviceAuditObservation leaks final.state
  let audit := sourceServiceAudit setup leaks backend.sample
  change observationRate who * deliveryRate who ≤
    expect (model.runBehavioralTerminalFrom certificate updated history)
      (fun final => TerminalAudit.charge observe audit final who)
  obtain ⟨event, earlierRecorded, submitted⟩ := recorded
  obtain ⟨material, responseEq⟩ : ∃ material, response = ⟨some material⟩ := by
    cases response with
    | mk transmission =>
        cases transmission with
        | none => cases submitted
        | some material => exact ⟨material, rfl⟩
  subst response
  have persistentClear := ((runtime setup).serviceRisk_clear_iff leaks bound who
    (execution.recall who) (execution.observe app who)).mp clear |>.1
  let second : app.TrafficRecord :=
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who), app.packet
        (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩
  obtain ⟨first, firstPresent, secondPresent, firstOwner, different, firstNamed, secondNamed⟩ :=
    recordedResponse_duplicateTraffic bounds bound contract execution who (current ▸ riskTrace)
      persistentClear event earlierRecorded material submitted
  have committed := menu.run_commit_response (initialLaw setup) horizon scheduler profile history
    who remaining execution current choice ⟨some material⟩ selected
  change (model.runBehavioralFrom updated 1 history).map History.state = _ at committed
  rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate updated 1 history,
    expect_bind_tower _ _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _)]
  calc
    observationRate who * deliveryRate who = expect (model.runBehavioralFrom updated 1 history)
        (fun _ => observationRate who * deliveryRate who) := (expect_constant _ _).symm
    _ ≤ _ := by
      refine expect_mono ?_ (payoffIntegrable_constant _ _) ?_
      rotate_left
      · exact payoffIntegrable_of_bounded _ _ (C := 1) fun next => by
          rw [abs_of_nonneg (expect_nonneg _ _ fun _ _ =>
            (TerminalAudit.charge_mem_Icc _ _ _ _).1)]
          exact expect_le_const _ _ (TerminalAudit.payoffIntegrable_charge _ _ _ _) _
            fun _ _ => (TerminalAudit.charge_mem_Icc _ _ _ _).2
      intro next supported
      have nextState : next.state =
          some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ := by
        have member : next.state ∈
            ((model.runBehavioralFrom updated 1 history).map History.state).support := by
          rw [PMF.support_map]
          exact ⟨next, supported, rfl⟩
        rw [committed] at member
        exact (PMF.mem_support_pure_iff _ _).mp member
      exact duplicateTraffic_collection_continuation menu horizon scheduler completes backend
        observationRate deliveryRate delivery_nonnegative coverage updated next event who
        first second
        (by simpa only [nextState, ReactiveApplication.stateTraffic] using firstPresent)
        (by simpa only [nextState, ReactiveApplication.stateTraffic] using secondPresent)
        firstOwner rfl different firstNamed secondNamed

end Vegas
