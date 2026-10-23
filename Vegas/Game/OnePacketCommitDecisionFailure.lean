/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCommitFailure

/-! # Primitive failure comparison for commitments at one prepared slot -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- A legal prepared-slot commitment whose declared typed candidate succeeds
has primitive failure close to its actual certificate kernel on every forced row.
The candidate-success fact is derived from the actual one-packet response. -/
theorem certificate_lateCommit_historyDecisionFailure
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (choice : (onePacketN).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state) :
    |expect ((onePacketN).runBehavioralFrom
        (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)))
        (2 * horizon + 1) history.1)
        (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) -
      certificateCommitFailure setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
        serial history.1.state| ≤
      (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  obtain ⟨chosen, chosenEq, member⟩ := choice_response setup leaks bounds horizon scheduler site
    atSite choice
  rw [selected] at chosenEq
  cases Option.some.inj chosenEq
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup leaks bounds horizon scheduler atSite history
  subst recallEq
  subst observeEq
  have lookupAfter : ((application setup leaks).submit execution.application who
      material).candidates.lookup (who, .prepared serial) = .openable ⟨payload, value⟩ := by
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).candidates.lookup (who, .prepared serial) = _
    rw [Submission.candidateAfter_eq]
    exact after
  have succeeds : candidateSucceeds ((application setup leaks).submit execution.application who
      material) (who, .prepared serial) payload = true := by
    unfold candidateSucceeds
    simp only [EventGraphRuntime.State.bindingResult, lookupAfter]
    simp [Raw.as?]
  exact certificate_commit_decisionFailure sequence scale
    scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe
    site late debtFree siteKey pending node history current atSite forced choice response
    selected member sends packet succeeds

open Classical in
/-- An arbitrary legal successful commitment and its same-slot late option
have nearly the same primitive decision-failure probability. The estimate uses
actual forced-history certificate kernels and no global native completion service. -/
theorem certificate_lateCommit_siteDecisionFailure
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced : ℝ}
    (unforcedMass : expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (choice : (onePacketN).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (inRange : serial < slots) :
    |localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed key final.state}
        (PMF.pure choice) -
      localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed key final.state}
        (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n ((onePacketN).agentAt site) (some ⟨serial, inRange⟩))| ≤
      2 * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) + unforced + 3 * scale n := by
  classical
  obtain ⟨chosen, chosenEq, member⟩ := choice_response setup leaks bounds horizon scheduler site
    atSite choice
  rw [selected] at chosenEq
  cases Option.some.inj chosenEq
  have permitted := slotEnvelope_permitted_of_commitment member sends packet
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  let site : (onePacketN).InformationSite who := ⟨some (past, view), decision⟩
  let error : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  have errorNonneg : 0 ≤ error :=
    mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith)
  have pendingView := pending
  obtain ⟨turn, _, _, _⟩ := pendingEvent_spec pendingView
  let lumped := fun history : (onePacketN).InformationHistory who site.1 =>
    certificateCommitFailure setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
      serial history.1.state
  let rowFailure := fun (law : PMF ((onePacketN).Choice who site.1))
      (history : (onePacketN).InformationHistory who site.1) =>
    expect ((onePacketN).runBehavioralFrom
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 law)) (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
  let main := lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
    (some (past, view)) (some ⟨serial, inRange⟩ : LateOption slots)
  -- From every forced history, the choice fails like the lumped failure of its slot.
  have choiceNear : ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup leaks who history.1.state →
      |rowFailure
          (PMF.pure choice) history - lumped history| ≤ error := by
    intro history forced
    exact certificate_lateCommit_historyDecisionFailure setup leaks bounds horizon scheduler
      sequence scale scale_pos scale_le_one weights targetSequence assembled n covers capacity
      slotsLe site late debtFree siteKey pending node rfl choice response selected sends packet
      after history forced
  -- From every forced history, each slot commitment of the late option fails alike.
  have otherNear : ∀ other ∈ main.support, ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup leaks who history.1.state →
      |rowFailure
          (PMF.pure other) history - lumped history| ≤ error := by
    intro other otherMember history forced
    simp only [main, lateChoice, lateResponse, turn, PMF.support_map, Set.mem_image]
      at otherMember
    obtain ⟨slotted, ⟨source, sourceMember, rfl⟩, rfl⟩ := otherMember
    obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
      state_of_site setup leaks bounds horizon scheduler (site := site) rfl history
    subst recallEq
    subst observeEq
    have traceHere : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
      current ▸ history.1.trace
    have covered := onePacket_honest_covered (sequence n) covers traceHere who event turn source
      sourceMember
    have inMenu := (slotResponse_mem_onePacket_iff setup leaks bounds who (execution.recall who)
      (execution.observe (application setup leaks) who) event node serial
      (lt_of_lt_of_le inRange slotsLe) source covered).mpr permitted
    have otherSelected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
        who (some (execution.recall who, execution.observe (application setup leaks) who))
        (slotResponse setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event serial source)).1 =
        some (slotResponse setup leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event serial source) := by
      simp only [responseChoice, inMenu, ↓reduceDIte]
    obtain ⟨action, encoded, values⟩ := covered
    obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
    obtain ⟨slotMaterial, transmits, envelope⟩ := slotResponse_transmission setup leaks who
      (execution.recall who) (execution.observe (application setup leaks) who) event node serial
      source action encoded
    have call : slotMaterial.call.packet = .commitment event (who, .prepared serial) :=
      congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
        message.payload.call) envelope
    have fresh' : execution.application.candidates.lookup (who, .prepared serial) = .fresh :=
      onePacket_permitted_fresh (control := ⟨remaining, some who, execution⟩) traceHere who event
        serial permitted
    have succeeds : candidateSucceeds ((application setup leaks).submit execution.application who
        slotMaterial) (who, .prepared serial) payload = true := by
      have bound := slotResponse_of_bind setup leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event node serial source action encoded
      have boundTransmits := transmits
      rw [bound] at boundTransmits
      have materialEq := Option.some.inj boundTransmits.symm
      have submitted : (application setup leaks).submit execution.application who slotMaterial =
          (execution.respond (application setup leaks) who
            ⟨some ⟨⟨.commitment event (who, .prepared serial), some ⟨payload, committedValue⟩⟩,
              .none⟩⟩).application := by
        rw [materialEq]
        change (application setup leaks).submit execution.application who
          (((runtime setup).reactiveNormalization leaks).normalize who
            ((application setup leaks).observePlayer execution.application who)
            (ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
              (execution.observe (application setup leaks) who))
            ⟨⟨.commitment event (who, .prepared serial), match (cast (congrArg
              EventGraph.EventField.Action outputEq) action : PublicationResult (L.Val payload))
              with
              | .failure => none
              | .success value => some ⟨payload, value⟩⟩, .none⟩) = _
        rw [((runtime setup).reactiveNormalization leaks).submit, successful]
        rfl
      have result := submitted_bindingResult (runtime setup) leaks execution who event payload
        serial (some ⟨payload, committedValue⟩) fresh'
      unfold candidateSucceeds
      rw [submitted]
      change (match (execution.respond (application setup leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared serial), some ⟨payload, committedValue⟩⟩,
            .none⟩⟩).application.bindingResult (who, .prepared serial) payload with
        | .success _ => true
        | .failure => false) = true
      rw [result]
      simp [Raw.as?]
    exact certificate_commit_decisionFailure sequence scale
      scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe
      site late debtFree siteKey pending node history current rfl forced _ _ otherSelected inMenu
      transmits call succeeds
  -- Site failures average history failures over the belief.
  have siteEq : ∀ law, localFailure (2 * horizon + 1) (targetSequence n) site
      {final | DecisionFailed key final.state} law =
        expect ((targetSequence n).belief who site) (rowFailure law) := by
    intro law
    unfold localFailure
    rw [expect_localRun]
    rfl
  have historyUnit : ∀ law history,
      0 ≤ rowFailure law history ∧ rowFailure law history ≤ 1 := by
    intro law history
    unfold rowFailure
    exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
      expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
        split <;> norm_num⟩
  have unforcedNonneg : 0 ≤ unforced := le_trans (expect_nonneg _ _ fun history _ => by
    split <;> norm_num) unforcedMass
  -- Every slot commitment of the late option fails like the choice.
  have near : ∀ other ∈ main.support,
      |localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed key final.state}
          (PMF.pure choice) -
        localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed key final.state}
          (PMF.pure other)| ≤ 2 * error + unforced := by
    intro other otherMember
    rw [siteEq, siteEq]
    refine le_trans (abs_expect_sub_le_expect _ _ _
      (fun history => 2 * error +
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1)
      fun history _ => ?_) ?_
    · by_cases forced : ForcedState setup leaks who history.1.state
      · have first := choiceNear history forced
        have second := otherNear other otherMember history forced
        simp only [forced, ↓reduceIte, add_zero]
        calc _ ≤ |rowFailure (PMF.pure choice) history - lumped history| +
              |lumped history - rowFailure (PMF.pure other) history| := abs_sub_le _ _ _
          _ ≤ error + error := add_le_add first (by rw [abs_sub_comm]; exact second)
          _ = 2 * error := by ring
      · simp only [forced, ↓reduceIte]
        have := historyUnit (PMF.pure choice) history
        have := historyUnit (PMF.pure other) history
        rw [abs_le]
        constructor <;> linarith
    · rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
        expect_constant]
      linarith
  have mass : ∀ other, (1 - 3 * scale n) * (main other).toReal ≤
      ((onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n ((onePacketN).agentAt site)
        (some ⟨serial, inRange⟩)) other).toReal := fun other =>
    lateComponent_ge setup leaks bounds (initialLaw setup) horizon scheduler (sequence n)
      (scale_pos n).le (scale_le_one n) who (some (past, view)) (some ⟨serial, inRange⟩) other
  have mixed := abs_localFailure_pure_sub_le_of_mass (targetSequence n) site
    {final | DecisionFailed key final.state} choice
    _ main (by have := (scale_pos n).le; linarith)
    (by linarith) mass near
  exact le_of_le_of_eq mixed (by ring)

end Vegas
