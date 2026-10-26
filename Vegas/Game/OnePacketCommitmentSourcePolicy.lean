/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedCommitGain

/-! # One source policy for an intended native commitment -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketInformation setup runtime leaks bounds horizon scheduler

open Classical in
/-- An intended commitment determines a single source policy independently of
the history sampled by the belief. Its source gain has the usual exact one-step
continuation formula at every debt-free decoded history of the native site. -/
theorem intendedCommitment_sourcePolicy_gain
    (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (atTurn : CommitsAtTurn setup runtime leaks bounds horizon scheduler who site choice)
    (intended : IntendedCommitment setup runtime leaks bounds horizon scheduler site choice)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who site.1))
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    ∃ (sourceChoice : setup.intendedModel.Choice who (projectView setup runtime leaks who site.1))
      (event : (graph setup).EventId) (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload),
      sourceChoice.1 = sourceOfValue setup event outputEq value ∧
      (∃ (response : (application setup runtime leaks).Action)
        (material : (application setup runtime leaks).Submission) (serial : Nat),
        choice.1 = some response ∧ response.transmission = some material ∧
        material.call.packet = .commitment event (who, .prepared serial) ∧
        material.call.candidateAfter who view.application.candidates (.prepared serial) =
          .openable ⟨payload, value⟩ ∧ view.application.publicView.ownTurn? who = some event) ∧
      ∀ (history : (N).InformationHistory who site.1) (point : ProtocolState setup.program),
        (∀ found, nativeDecodedState setup runtime leaks history.1.state = some found →
          ∀ player, ¬ ProtocolState.OwesFailure player setup.program found) →
        nativeDecodedState setup runtime leaks history.1.state = some point →
        setup.intendedModel.historyGain
            (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
            (intendedReadoutExclusion setup parameter utility excludedPayoff)
            (payoffComponent setup)
            assessment (projectedSite setup runtime leaks decision,
              (assessment.strategy who).commit (projectView setup runtime leaks who site.1)
                sourceChoice)
            (replayProjection setup runtime leaks bounds horizon scheduler
              (projectedSite setup runtime leaks decision) site atSite rfl history) =
          expect (ProtocolState.step setup.program point (fun _ => sourceChoice.1))
              (sourcePointValue setup parameter utility excludedPayoff
                (setup.intendedOpeningProfile assessment.strategy) who) -
            sourcePointValue setup parameter utility excludedPayoff
              (setup.intendedOpeningProfile assessment.strategy) who point := by
  classical
  obtain ⟨otherPast, otherView, response, material, event, serial, payload, outputEq, value,
    otherSite, selected, sends, packet, after, offered⟩ := intended
  rw [atSite, Option.some.injEq, Prod.mk.injEq] at otherSite
  obtain ⟨pastEq, viewEq⟩ := otherSite
  subst pastEq viewEq
  obtain ⟨turnPast, turnView, turnResponse, turnEvent, turnSite, chosen, submitted, turn⟩ := atTurn
  rw [atSite, Option.some.injEq, Prod.mk.injEq] at turnSite
  obtain ⟨pastEq, viewEq⟩ := turnSite
  subst pastEq viewEq
  rw [selected] at chosen
  cases Option.some.inj chosen
  have named : turnEvent = event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [sends] at submitted
    change material.call.packet.event? (graph setup) = some turnEvent at submitted
    rw [packet] at submitted
    exact (Option.some.inj submitted).symm
  subst turnEvent
  let sourceChoice : setup.intendedModel.Choice who (projectView setup runtime leaks who site.1) :=
    ⟨sourceOfValue setup event outputEq value, offered⟩
  refine ⟨sourceChoice, event, payload, outputEq, value, rfl,
    ⟨response, material, serial, selected, sends, packet, after, turn⟩, ?_⟩
  rintro ⟨start, observed⟩ point regular decoded
  have observedState : (application setup runtime leaks).observe who start.state = site.1 :=
    ((bounds.onePacketMenu runtime leaks).info (initialLaw setup) horizon scheduler who
      start.trace).symm.trans observed
  rcases state : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [state] at decoded
    cases decoded
  rw [state] at observedState regular decoded
  have acting : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    rw [atSite] at observedState
    cases observedState
  subst acting
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
  rw [atSite] at observedState
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj observedState)
  subst pastEq viewEq
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have pointDecoded : decodedPoint setup execution.application.config = some point := decoded
  have acts : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who := (decodedPoint_actor who ready pointDecoded).trans owned
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree (runtime := runtime) wellFormed
    start.trace _ state
    regular
  have projected := replayProjection_eq (runtime := runtime) (setup := setup) (leaks := leaks)
    (bounds := bounds)
    (horizon := horizon) (scheduler := scheduler)
    (sourceSite := projectedSite setup runtime leaks decision) atSite rfl ⟨start, observed⟩ replayed
  have replayState := intendedHistory?_state (runtime := runtime) start.trace replayed
  rw [state] at replayState
  have projectedState : (replayProjection setup runtime leaks bounds horizon scheduler
      (projectedSite setup runtime leaks decision) site atSite rfl ⟨start, observed⟩).1.state =
        some point := by
    rw [projected, replayState]
    exact pointDecoded
  exact intendedCommit_historyGain setup parameter utility excludedPayoff wellFormed assessment
    (projectedSite setup runtime leaks decision) sourceChoice _ projectedState acts readoutBounded

end Vegas
