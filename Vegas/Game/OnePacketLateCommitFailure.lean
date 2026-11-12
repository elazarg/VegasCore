module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCommitDecisionFailure

@[expose] public section

/-! # Mixture comparisons for commitments at prepared slots

Scalar averaging transfers the fixed-commitment history estimate to a late
slot-option law. The prepared-envelope lemma records the menu admission fact.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **A permitted commitment is the slot's envelope.** A transmitting response
of the one-packet menu committing an event to a prepared slot of its sender
makes the slot's envelope permitted. -/
theorem slotEnvelope_permitted_of_commitment {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {response : (application setup timeouts
      leaks).Action}
    (member : response ∈ bounds.onePacketActions timeouts leaks who past view)
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {serial : Nat} (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    countPermits ((application setup timeouts leaks).outputs past)
      (slotEnvelope setup timeouts leaks who past view event serial) = true := by
  rcases ((bounds.mem_onePacketActions timeouts leaks who past view response).mp
      member).2 with silent | ⟨other, transmits, permitted⟩
  · rw [sends] at silent
    cases silent
  rw [sends] at transmits
  cases Option.some.inj transmits
  have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
  have callEq : ((localEnvelope timeouts) leaks who past view material).payload.call =
      .commitment event (who, .prepared serial) := packet
  unfold CountCallCorrect at correct
  rw [callEq] at correct
  obtain ⟨_, evidence, _⟩ := correct
  have envelopeEq : (localEnvelope timeouts) leaks who past view material =
      slotEnvelope setup timeouts leaks who past view event serial := by
    unfold slotEnvelope
    unfold EventGraphRuntime.localEnvelope at evidence ⊢
    rw [← evidence, ← packet]
  rw [← envelopeEq]
  exact permitted

section Certificate

variable [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

/-- A choice's failure differs from a mixture's by at most `A + weight` when
the mixture keeps `1 - weight` of a main law on whose support every choice
fails within `A` of the choice. -/
theorem abs_localFailure_pure_sub_le_of_mass
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (failed : Set ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (choice : (onePacketN).Choice who site.1) (law main : PMF ((onePacketN).Choice who site.1))
    {weight A : ℝ} (weightNonneg : 0 ≤ weight) (nonnegative : 0 ≤ A)
    (mass : ∀ other, (1 - weight) * (main other).toReal ≤ (law other).toReal)
    (near : ∀ other ∈ main.support,
      |localFailure (2 * horizon + 1) assessment site failed (PMF.pure choice) -
        localFailure (2 * horizon + 1) assessment site failed (PMF.pure other)| ≤ A) :
    |localFailure (2 * horizon + 1) assessment site failed (PMF.pure choice) -
      localFailure (2 * horizon + 1) assessment site failed law| ≤ A + weight := by
  have finiteChoice : Finite ((onePacketN).Choice who site.1) :=
    (onePacketN).finite_choice_of_played ((onePacketN).site_mem_playedInformation site)
  let := Fintype.ofFinite ((onePacketN).Choice who site.1)
  have bounded := (bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup)
    horizon scheduler
  have actsOnce := ((bounds.onePacketMenu timeouts leaks).decisionRecall
    (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  let failure := fun other : (onePacketN).Choice who site.1 =>
    localFailure (2 * horizon + 1) assessment site failed (PMF.pure other)
  have unit : ∀ other, 0 ≤ failure other ∧ failure other ≤ 1 := fun other =>
    ⟨localFailure_nonneg _ _ _ _ _, localFailure_le_one _ _ _ _ _⟩
  have lawEq : localFailure (2 * horizon + 1) assessment site failed law =
      ∑ other, (law other).toReal * failure other := by
    conv_lhs => rw [← PMF.bind_pure law]
    rw [localFailure_bind (2 * horizon + 1) assessment site bounded actsOnce, expect_eq_sum]
  have total : ∀ μ : PMF ((onePacketN).Choice who site.1), ∑ other, (μ other).toReal = 1 := by
    intro μ
    have sum := expect_eq_sum μ (fun _ => (1 : ℝ))
    rw [expect_constant] at sum
    simpa using sum.symm
  by_cases small : weight ≤ 1
  swap
  · have := unit choice
    have := localFailure_nonneg (2 * horizon + 1) assessment site failed law
    have := localFailure_le_one (2 * horizon + 1) assessment site failed law
    rw [abs_le]
    constructor <;> linarith
  have diffEq : failure choice - localFailure (2 * horizon + 1) assessment site failed law =
      ∑ other, (law other).toReal * (failure choice - failure other) := by
    rw [lawEq]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, total law, one_mul]
  change |failure choice - _| ≤ _
  rw [diffEq]
  calc _ ≤ ∑ other, |(law other).toReal * (failure choice - failure other)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ other, (((law other).toReal - (1 - weight) * (main other).toReal) +
        (1 - weight) * ((main other).toReal * A)) := by
        refine Finset.sum_le_sum fun other _ => ?_
        have gap := mass other
        have difference : |failure choice - failure other| ≤ 1 := by
          have := unit choice
          have := unit other
          rw [abs_le]
          constructor <;> linarith
        have mainNear : (main other).toReal * |failure choice - failure other| ≤
            (main other).toReal * A := by
          by_cases zero : main other = 0
          · simp [zero]
          · exact mul_le_mul_of_nonneg_left (near other ((PMF.mem_support_iff _ _).mpr zero))
              ENNReal.toReal_nonneg
        have first := mul_le_mul_of_nonneg_left difference (sub_nonneg.mpr gap)
        have second := mul_le_mul_of_nonneg_left mainNear (sub_nonneg.mpr small)
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        have split : (law other).toReal * |failure choice - failure other| =
            ((law other).toReal - (1 - weight) * (main other).toReal) *
              |failure choice - failure other| +
            (1 - weight) * ((main other).toReal * |failure choice - failure other|) := by ring
        rw [split]
        linarith
    _ = weight + (1 - weight) * A := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.sum_mul, total law, total main]
        ring
    _ ≤ A + weight := by nlinarith

omit [Fintype Player] in
/-- Pointwise bounds on the difference of two functions bound the difference of
their expectations by the expected bound. -/
theorem abs_expect_sub_le_expect {α : Type*} [Finite α] (law : PMF α)
    (first second bound : α → ℝ)
    (near : ∀ point ∈ law.support, |first point - second point| ≤ bound point) :
    |expect law first - expect law second| ≤ expect law bound := by
  rw [abs_le]
  constructor
  · have upper := expect_mono (μ := law) (f := fun point => second point - first point)
      (g := bound) (fun point supported => by
        have := abs_le.mp (near point supported)
        linarith) (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at upper
    linarith
  · have upper := expect_mono (μ := law) (f := fun point => first point - second point)
      (g := bound) (fun point supported => (abs_le.mp (near point supported)).2)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at upper
    exact upper

variable (setup timeouts leaks bounds horizon scheduler)

open Classical in
/-- An arbitrary legal successful commitment and its same-slot late option
have nearly the same primitive decision-failure probability. The estimate uses
actual forced-history certificate kernels and no global native completion service. -/
theorem certificate_lateCommit_siteDecisionFailure
    [Finite ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup timeouts leaks who site.1)
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup timeouts leaks who site.1 = some
      event)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced : ℝ}
    (unforcedMass : expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (choice : (onePacketN).Choice who site.1) (response : (application setup timeouts leaks).Action)
    (selected : choice.1 = some response) {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (inRange : serial < slots) :
    |localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed (timeouts := timeouts) key final.state}
        (PMF.pure choice) -
      localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed (timeouts := timeouts) key final.state}
        (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n ((onePacketN).agentAt site) (some ⟨serial, inRange⟩))| ≤
      2 * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) + unforced + 3 * scale n := by
  classical
  obtain ⟨chosen, chosenEq, member⟩ := choice_response setup timeouts leaks bounds horizon
    scheduler site
    atSite choice
  rw [selected] at chosenEq
  cases Option.some.inj chosenEq
  have permitted := slotEnvelope_permitted_of_commitment (timeouts := timeouts) member sends packet
  obtain ⟨info, decision⟩ := site
  change info = some (past, view) at atSite
  subst atSite
  let site : (onePacketN).InformationSite who := ⟨some (past, view), decision⟩
  let error : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  have errorNonneg : 0 ≤ error :=
    mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith)
  have pendingView := pending
  obtain ⟨turn, _, _, _⟩ := pendingEvent_spec (timeouts := timeouts) pendingView
  let lumped := fun history : (onePacketN).InformationHistory who site.1 =>
    certificateCommitFailure setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
      serial history.1.state
  let rowFailure := fun (law : PMF ((onePacketN).Choice who site.1))
      (history : (onePacketN).InformationHistory who site.1) =>
    expect ((onePacketN).runBehavioralFrom
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 law)) (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
  let main := lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence
    n) who
    (some (past, view)) (some ⟨serial, inRange⟩ : LateOption slots)
  -- From every forced history, the choice fails like the lumped failure of its slot.
  have choiceNear : ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup timeouts leaks who history.1.state →
      |rowFailure
          (PMF.pure choice) history - lumped history| ≤ error := by
    intro history forced
    exact certificate_lateCommit_historyDecisionFailure setup timeouts leaks bounds horizon
      scheduler
      sequence scale scale_pos scale_le_one weights targetSequence assembled n covers capacity
      slotsLe site late debtFree siteKey pending node rfl choice response selected sends packet
      after history forced
  -- From every forced history, each slot commitment of the late option fails alike.
  have otherNear : ∀ other ∈ main.support, ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup timeouts leaks who history.1.state →
      |rowFailure
          (PMF.pure other) history - lumped history| ≤ error := by
    intro other otherMember history forced
    simp only [main, lateChoice, lateResponse, turn, PMF.support_map, Set.mem_image]
      at otherMember
    obtain ⟨slotted, ⟨source, sourceMember, rfl⟩, rfl⟩ := otherMember
    obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
      state_of_site setup timeouts leaks bounds horizon scheduler (site := site) rfl history
    subst recallEq
    subst observeEq
    have traceHere : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
      current ▸ history.1.trace
    have covered := onePacket_honest_covered (timeouts := timeouts) (sequence n) covers traceHere
      who event turn source
      sourceMember
    have inMenu := (slotResponse_mem_onePacket_iff setup timeouts leaks bounds who
      (execution.logs who)
      (execution.observe (application setup timeouts leaks) who) event node serial
      (lt_of_lt_of_le inRange slotsLe) source covered).mpr permitted
    have otherSelected : (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler
        who (some (execution.logs who, execution.observe (application setup timeouts leaks) who))
        (slotResponse setup timeouts leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event serial source)).1 =
        some (slotResponse setup timeouts leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event serial source) := by
      simp only [responseChoice, inMenu, ↓reduceDIte]
    obtain ⟨action, encoded, values⟩ := covered
    obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
    obtain ⟨slotMaterial, transmits, envelope⟩ := slotResponse_transmission setup timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who) event node
        serial
      source action encoded (by simp [successful])
    have call : slotMaterial.call.packet = .commitment event (who, .prepared serial) :=
      congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
        message.payload.call) envelope
    have fresh' : execution.application.candidates.lookup (who, .prepared serial) = .fresh :=
      onePacket_permitted_fresh (timeouts := timeouts) (control := ⟨remaining, some who, execution⟩)
        traceHere who event
        serial permitted
    have succeeds : candidateSucceeds ((application setup timeouts leaks).submit
      execution.application who
        slotMaterial) (who, .prepared serial) payload = true := by
      have bound := slotResponse_of_bind setup timeouts leaks who (execution.logs who)
        (execution.observe (application setup timeouts leaks) who) event node serial source action
          encoded
      have boundTransmits := transmits
      rw [bound, successful] at boundTransmits
      have materialEq := Option.some.inj boundTransmits.symm
      have submitted : (application setup timeouts leaks).submit execution.application who
        slotMaterial =
          (execution.respond (application setup timeouts leaks) who
            ⟨some ⟨⟨.commitment event (who, .prepared serial), some ⟨payload, committedValue⟩⟩,
              .none⟩⟩).application := by
        rw [materialEq]
        exact ((reactiveNormalization timeouts) leaks).submit execution.application who
          (ReactiveApplication.ResponseMenu.knownPackets (execution.logs who)
            (execution.observe (application setup timeouts leaks) who))
          (⟨⟨.commitment event (who, .prepared serial), some ⟨payload, committedValue⟩⟩, .none⟩ :
            ((reactiveApplication timeouts) leaks).Submission)
      have result := submitted_bindingResult timeouts leaks execution who event payload
        serial (some ⟨payload, committedValue⟩) fresh'
      unfold candidateSucceeds
      rw [submitted]
      change (match (execution.respond (application setup timeouts leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared serial), some ⟨payload, committedValue⟩⟩,
            .none⟩⟩).application.bindingResult (who, .prepared serial) payload with
        | .success _ => true
        | .failure => false) = true
      rw [result]
      simp [Raw.as?]
    exact certificate_commit_decisionFailure (timeouts := timeouts) sequence scale
      scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe
      site late debtFree siteKey pending node history current rfl forced _ _ otherSelected inMenu
      transmits call succeeds
  -- Site failures average history failures over the belief.
  have siteEq : ∀ law, localFailure (2 * horizon + 1) (targetSequence n) site
      {final | DecisionFailed (timeouts := timeouts) key final.state} law =
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
          {final | DecisionFailed (timeouts := timeouts) key final.state}
          (PMF.pure choice) -
        localFailure (2 * horizon + 1) (targetSequence n) site
          {final | DecisionFailed (timeouts := timeouts) key final.state}
          (PMF.pure other)| ≤ 2 * error + unforced := by
    intro other otherMember
    rw [siteEq, siteEq]
    refine le_trans (abs_expect_sub_le_expect _ _ _
      (fun history => 2 * error +
        if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1)
      fun history _ => ?_) ?_
    · by_cases forced : ForcedState setup timeouts leaks who history.1.state
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
      ((onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n ((onePacketN).agentAt site)
        (some ⟨serial, inRange⟩)) other).toReal := fun other =>
    lateComponent_ge setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence n)
      (scale_pos n).le (scale_le_one n) who (some (past, view)) (some ⟨serial, inRange⟩) other
  have mixed := abs_localFailure_pure_sub_le_of_mass (timeouts := timeouts) (targetSequence n) site
    {final | DecisionFailed (timeouts := timeouts) key final.state} choice
    _ main (by have := (scale_pos n).le; linarith)
    (by linarith) mass near
  exact le_of_le_of_eq mixed (by ring)

end Certificate

end Vegas
