/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCertificate

/-! # Failure after a late commitment

A permitted commitment of the one-packet menu to a prepared slot carries no
evidence, so its envelope is the slot's envelope
(`Vegas.slotEnvelope_permitted_of_commitment`). Under a one-step lumping of
the profiles of options at a late binding, the failure probability after any
such commitment whose candidate succeeds is, up to the horizon times `δ`, the
lumped failure of the committed image, which reads the slot alone
(`Vegas.lateCommit_failure_next`). So from a history at which the installed
profile commits surely, play fails within that error of the lumped failure of
the committed image (`Vegas.lateCommit_historyFailure`).

For the certificate, at a debt-free late delivery of a binding, a choice
committing at a prepared slot fails, from every forced history, within the
horizon times twice the cube of the scale of the certificate's lumped failure of
the slot (`Vegas.certificate_commit_historyFailure`,
`Vegas.certificateCommitFailure`), in particular a choice committing a value
its candidate opens to (`Vegas.certificate_lateCommit_historyFailure`). So a
choice committing a value at a slot of
the late options fails, at the site, within twice that error plus the belief
mass outside the forced region plus three times the scale of the late option
sending at the slot (`Vegas.certificate_lateCommit_siteFailure`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **A permitted commitment is the slot's envelope.** A transmitting response
of the one-packet menu committing an event to a prepared slot of its sender
makes the slot's envelope permitted. -/
theorem slotEnvelope_permitted_of_commitment {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {serial : Nat} (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    countPermits ((application setup leaks).outputs past)
      (slotEnvelope setup leaks who past view event serial) = true := by
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks who past view response).mp
      member).2 with silent | ⟨other, transmits, permitted⟩
  · rw [sends] at silent
    cases silent
  rw [sends] at transmits
  cases Option.some.inj transmits
  have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
  have callEq : ((runtime setup).localEnvelope leaks who past view material).payload.call =
      .commitment event (who, .prepared serial) := packet
  unfold CountCallCorrect at correct
  rw [callEq] at correct
  obtain ⟨_, evidence, _⟩ := correct
  have envelopeEq : (runtime setup).localEnvelope leaks who past view material =
      slotEnvelope setup leaks who past view event serial := by
    unfold slotEnvelope
    unfold EventGraphRuntime.localEnvelope at evidence ⊢
    rw [← evidence, ← packet]
  rw [← envelopeEq]
  exact permitted

/-- A law whose supported values are each within `error` of `target` has
expectation within `error` of it. -/
private theorem abs_expect_sub_le_of_forall {α : Type*} (law : PMF α) (value : α → ℝ)
    {target error bound : ℝ} (bounded : ∀ point, |value point| ≤ bound)
    (near : ∀ point ∈ law.support, |value point - target| ≤ error) :
    |expect law value - target| ≤ error := by
  have integrable := payoffIntegrable_of_bounded law value bounded
  have upper := expect_le_const law value integrable (target + error) fun point supported => by
    linarith [(abs_le.mp (near point supported)).2]
  have lower := expect_mono (μ := law) (f := fun _ => target - error) (g := value)
    (fun point supported => by linarith [(abs_le.mp (near point supported)).1])
    (payoffIntegrable_constant _ _) integrable
  rw [expect_constant] at lower
  refine abs_le.mpr ⟨by linarith, by linarith⟩

open Classical in
/-- **Failure after a late commitment.** Let a one-step lumping of the profiles
`profileOf` fail where the decided binding `event` of `who` fails in the store,
with its image at the key read off the binding image, and keep every state
with the configuration of `start` at which the recall of `who` strictly extends
the one at `start`. From a decision of `who` at `start` with nothing pending for
the event, after a response of the menu committing the event to a prepared slot
whose candidate succeeds, play of every option's profile fails within the
horizon times `δ` of the lumped failure of the committed image. -/
theorem lateCommit_failure_next
    {target : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn target who relevant profileOf DecisionFailed δ Y)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (isRelevant : relevant site) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who site.1 = some key) (option : LateOption')
    {event : (graph setup).EventId} {payload : L.Ty}
    (imageOfBinding : BindingImage (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage event who payload state))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup leaks).Control),
      history.state = some control →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.recall who = execution.recall who ++ entry :: rest) →
      history.state ∈ lumping.keep site key)
    (ready : execution.application.config.cut.Ready event)
    (empty : commitStatuses event who payload execution.application execution.network.pending =
      [])
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup leaks).submit execution.application who
      material) (who, .prepared serial) payload = true)
    (next : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (nextState : next.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who response⟩) :
    |expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) (2 * horizon + 1) next)
        (fun final => if DecisionFailed key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[2 * horizon + 1]
        (PMF.pure (imageOfBinding (committedImage event who (who, .prepared serial)
          (operationalState setup leaks (some ⟨remaining, some who, execution⟩))))))
        (lumping.failure key)| ≤ (2 * horizon + 1 : ℕ) * δ := by
  have configEq := ((runtime setup).reactive_respond_application leaks execution who response).1
  have keptNext : next.state ∈ lumping.keep site key := by
    refine keptOf next _ nextState configEq ?_
    have respondRecall : ∃ emitted, (execution.respond (application setup leaks) who
        response).recall who = execution.recall who ++
          [⟨execution.observe (application setup leaks) who, response, emitted⟩] := by
      rcases response with ⟨transmission⟩
      cases transmission <;>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩
    obtain ⟨emitted, recallEq⟩ := respondRecall
    exact ⟨_, [], recallEq⟩
  have imageNext : lumping.image key next.state = imageOfBinding (committedImage event who
      (who, .prepared serial) (operationalState setup leaks
        (some ⟨remaining, some who, execution⟩))) := by
    rw [imageBinding, nextState, committed_bindingImage bounds start current ready.1 empty
      response member sends packet succeeds]
  have lumped := lumping.abs_failure_sub_le_of_keep (2 * horizon + 1) site isRelevant key
    siteKey option next keptNext
  rw [imageNext] at lumped
  exact_mod_cast lumped

open Classical in
/-- **Failure from a sure late commitment.** Under the lumping of
`Vegas.lateCommit_failure_next`, let the profile `installed` commit surely, at
the decision of `who` at `start`, by a response of the menu committing the
event to a prepared slot whose candidate succeeds, and agree with the profile
of an option wherever the recall of `who` is longer than at `start`. Then play
of `installed` from `start` fails within the horizon times `δ` of the lumped
failure of the committed image. -/
theorem lateCommit_historyFailure
    {target : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn target who relevant profileOf DecisionFailed δ Y)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (isRelevant : relevant site) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who site.1 = some key) (option : LateOption')
    {event : (graph setup).EventId} {payload : L.Ty}
    (imageOfBinding : BindingImage (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage event who payload state))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup leaks).Control),
      history.state = some control →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.recall who = execution.recall who ++ entry :: rest) →
      history.state ∈ lumping.keep site key)
    (ready : execution.application.config.cut.Ready event)
    (empty : commitStatuses event who payload execution.application execution.network.pending =
      [])
    (installed : ∀ player, (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralPolicy player)
    (agreeLonger : ∀ history : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History,
      (∀ control, history.state = some control →
        (execution.recall who).length < (control.execution.recall who).length) →
      ∀ player, installed player
          ((onePacketInformation setup leaks bounds horizon scheduler).infoOf player
            history.trace) =
        profileOf site option player
          ((onePacketInformation setup leaks bounds horizon scheduler).infoOf player
            history.trace))
    (response : (application setup leaks).Action)
    (responseLaw : (installed who (some (execution.recall who,
      execution.observe (application setup leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup leaks).submit execution.application who
      material) (who, .prepared serial) payload = true) :
    |expect ((onePacketInformation setup leaks bounds horizon scheduler).runBehavioralFrom
        installed (2 * horizon + 1) start)
        (fun final => if DecisionFailed key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[2 * horizon + 1]
        (PMF.pure (imageOfBinding (committedImage event who (who, .prepared serial)
          (operationalState setup leaks (some ⟨remaining, some who, execution⟩))))))
        (lumping.failure key)| ≤ (2 * horizon + 1 : ℕ) * δ := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketInformation setup leaks bounds horizon scheduler
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed start
    who remaining execution current
  rw [decodeProfile_eq_map, responseLaw, PMF.pure_map] at stepStates
  have nextState : ∀ next ∈ (model.runBehavioralFrom installed 1 start).support,
      next.state = some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩ := by
    intro next nextMember
    have inStates : next.state ∈ ((model.runBehavioralFrom installed 1 start).map
        History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nextMember, rfl⟩
    rw [stepStates, PMF.mem_support_pure_iff] at inStates
    exact inStates
  have nextRecall : (execution.recall who).length <
      ((execution.respond (application setup leaks) who response).recall who).length := by
    have longer := (application setup leaks).respond_recall_length execution who who response
    simp only [↓reduceIte] at longer
    omega
  have split : model.runBehavioralFrom installed (2 * horizon + 1) start =
      (model.runBehavioralFrom installed 1 start).bind
        (model.runBehavioralFrom (profileOf site option) (2 * horizon + 1)) := by
    rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded,
      model.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom certificate installed 1 start]
    apply bind_congr_on_support
    intro next nextMember
    rw [model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
    apply model.runBehavioralFrom_congr (2 * horizon + 1) next
    intro later path _ player
    apply agreeLonger later
    intro control laterState
    have rawPath := menu.reaches_raw (initialLaw setup) horizon scheduler path
    have grown := (application setup leaks).reaches_recall_prefix (initialLaw setup) horizon
      scheduler rawPath _ control (nextState next nextMember) laterState who
    exact lt_of_lt_of_le nextRecall grown.length_le
  rw [split, expect_bind_tower_bounded _ _ _ (C := 1) (fun final => by
    split <;> norm_num)]
  refine abs_expect_sub_le_of_forall _ _ (bound := 1) (fun next => ?_) (fun next nextMember =>
    lateCommit_failure_next lumping site isRelevant siteKey option imageOfBinding imageBinding
      start current keptOf ready empty response member sends packet succeeds next
      (nextState next nextMember))
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := expect_nonneg (model.runBehavioralFrom (profileOf site option)
      (2 * horizon + 1) next)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
      (fun final _ => by split <;> norm_num)
    linarith
  · exact expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) (fun final => by
      split <;> norm_num)) 1 (fun final _ => by split <;> norm_num)

section Certificate

variable [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

/-- A choice's failure differs from a mixture's by at most `A + weight` when
the mixture keeps `1 - weight` of a main law on whose support every choice
fails within `A` of the choice. -/
private theorem abs_localFailure_pure_sub_le_of_mass
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (failed : Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
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
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  have actsOnce := ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
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

variable (setup leaks bounds horizon scheduler) in
/-- **The lumped failure of a late commitment** at a slot: the certificate's
lumped failure, at a key, of the committed image of the slot at a state. -/
def certificateCommitFailure (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player) (key : LateKey setup leaks)
    (event : (graph setup).EventId) (serial : Nat)
    (state : (application setup leaks).ProtocolState) : ℝ :=
  expect ((fun law => law.bind ((certificateLumping setup leaks bounds horizon scheduler
      sequence scale scale_pos scale_le_one covers capacity slotsLe weights targetSequence
      assembled n who).kernel key (none : LateOption slots)))^[2 * horizon + 1]
    (PMF.pure (Sum.inr (committedImage event who (who, .prepared serial)
      (operationalState setup leaks state)))))
    ((certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one covers capacity slotsLe weights targetSequence assembled n who).failure key)

variable (setup leaks bounds horizon scheduler) in
/-- **The certificate's failure after a late commitment.** At a late delivery of
the binding `event` of `who`, from a forced history of the site, a choice
committing the event to a prepared slot by a response of the menu whose
candidate succeeds fails within the horizon times twice the cube of the scale of
the certificate's lumped failure of the slot at the history. -/
theorem certificate_commit_historyFailure
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
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
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state)
    (choice : (onePacketN).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response)
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup leaks).submit execution.application who
      material) (who, .prepared serial) payload = true) :
    |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
        (PMF.pure choice) history -
      certificateCommitFailure setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
        serial history.1.state| ≤
      (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketN
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨ownerEq, noPublication, binding, decided⟩ := lateKey_decides_binding setup leaks
    horizon scheduler rawTrace rfl siteKeyHere turn unrecorded node
  have unsent := (unsentFor_iff_unrecorded setup leaks horizon scheduler rawTrace rfl
    siteKeyHere event).mpr unrecorded
  have empty := commitStatuses_nil_of_unsent siteKey history current unsent payload
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  let lumping := certificateLumping setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have imageBinding : ∀ state, lumping.image key state =
      Sum.inr (bindingImage event who payload state) := by
    intro state
    change decisionImage key state = _
    unfold decisionImage
    rw [noPublication, binding, ownerEq]
  let installed := Profile.update (sig := (onePacketN).behavioralSignature)
    (targetSequence n).strategy who
    (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
  have responseLaw : (installed who (some (execution.recall who,
      execution.observe (application setup leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response := by
    rw [← atSite]
    simp only [installed, Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_map,
      selected, Option.getD_some]
  have through := siteThrough_of_history setup leaks bounds horizon scheduler late debtFree
    siteKey history
  rw [current] at through forced
  have core := lateCommit_historyFailure lumping site ⟨Or.inl late, debtFree⟩ siteKey
    (none : LateOption slots) Sum.inr imageBinding history.1 current
    (fun later control laterState sameConfig longer => by
      refine ⟨?_, ?_⟩
      · unfold decisionKept
        rw [decided]
        obtain ⟨rank, point, ordered, decoded, holds⟩ := forced
        exact ⟨⟨later, laterState.symm ▸ rfl⟩, control, laterState,
          Or.inr ⟨ownerEq ▸ ⟨rank, point, by rw [sameConfig]; exact ordered,
            by rw [sameConfig]; exact decoded, holds⟩, by rw [sameConfig]; exact ready⟩⟩
      · rw [laterState]
        refine ⟨⟨?_, fun turnEvent siteTurn => ?_⟩, Or.inl late⟩
        · right
          obtain ⟨entry, rest, recallEq⟩ := longer
          refine ⟨entry, rest, ?_⟩
          rw [recallEq, atSite]
          rfl
        · have clear := through.2 turnEvent siteTurn
          simp only [DebtClear] at clear ⊢
          rw [sameConfig]
          exact clear)
    ready empty installed
    (fun later longer player => by
      by_cases same : player = who
      · subst same
        simp only [installed, Profile.update_same]
        have different : (onePacketN).infoOf player later.trace ≠ site.1 := by
          rw [atSite]
          change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
            scheduler).infoOf player later.trace ≠ _
          rw [(bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
            scheduler player later.trace]
          cases laterState : later.state with
          | none => simp [ReactiveApplication.observe]
          | some control =>
              have lengthLt := longer control laterState
              simp only [ReactiveApplication.observe]
              split_ifs
              · intro infoEq
                have recallEq := congrArg (fun info : (application setup leaks).Info =>
                  (info.map Prod.fst).map List.length) infoEq
                simp only [Option.map_some] at recallEq
                have := Option.some.inj recallEq
                omega
              · simp
        rw [BehavioralPolicy.withLaw_of_ne _ _ _ different,
          BehavioralPolicy.withLaw_of_ne _ _ _ different]
      · simp only [installed, Profile.update_of_ne _ _ same])
    response responseLaw member sends packet succeeds
  have sameFailure : siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n)
      site (PMF.pure choice) history =
      expect (model.runBehavioralFrom installed (2 * horizon + 1) history.1)
        (fun final => if DecisionFailed key final.state then 1 else 0) := by
    unfold siteHistoryFailure
    change expect (model.runBehavioralFrom installed (2 * horizon + 1) history.1) _ = _
    apply expect_congr_on_support
    intro final reached
    have iff := onePacketFailed_iff_decisionFailed setup leaks bounds horizon scheduler completes
      (failureProfile setup.program) site late siteKey history installed final reached
    by_cases failed : DecisionFailed key final.state
    · simp only [iff.mpr failed, failed, ↓reduceIte]
    · simp only [mt iff.mp failed, failed, ↓reduceIte]
  rw [sameFailure]
  unfold certificateCommitFailure
  rw [current]
  exact core

variable (setup leaks bounds horizon scheduler) in
/-- **The certificate's failure after committing a value late.** At a
debt-free late delivery of the binding `event` of `who`, from a forced history
of the site, a choice committing the event at a prepared slot to a value its
candidate opens to fails within the horizon times twice the cube of the scale of
the certificate's lumped failure of the slot at the history. -/
theorem certificate_lateCommit_historyFailure
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
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
    |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
        (PMF.pure choice) history -
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
  exact certificate_commit_historyFailure setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one weights targetSequence assembled n completes covers capacity slotsLe
    site late debtFree siteKey pending node history current atSite forced choice response
    selected member sends packet succeeds

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

variable (setup leaks bounds horizon scheduler) in
open Classical in
/-- **A late commitment fails like the late option at its slot.** At a late
delivery of the binding `event` of `who`, let a choice commit the event, at a
prepared slot within the late options' slots, to a value its candidate opens
to. Then, up to the belief mass `unforced` outside the forced region, it fails
within twice the horizon times twice the cube of the scale, plus three times
the scale, of the late option sending at that slot: from every forced history
both fail within the horizon times twice the cube of the scale of the
certificate's lumped failure of the slot, and the late option keeps all but
three times the scale of the mass of its slot commitments. -/
theorem certificate_lateCommit_siteFailure
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
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
    |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
        (PMF.pure choice) -
      onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
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
  let main := lateChoice setup leaks bounds (initialLaw setup) horizon scheduler (sequence n) who
    (some (past, view)) (some ⟨serial, inRange⟩ : LateOption slots)
  -- From every forced history, the choice fails like the lumped failure of its slot.
  have choiceNear : ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup leaks who history.1.state →
      |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice) history - lumped history| ≤ error := by
    intro history forced
    exact certificate_lateCommit_historyFailure setup leaks bounds horizon scheduler sequence
      scale scale_pos scale_le_one weights targetSequence assembled n completes covers capacity
      slotsLe site late debtFree siteKey pending node rfl choice response selected sends packet
      after history forced
  -- From every forced history, each slot commitment of the late option fails alike.
  have otherNear : ∀ other ∈ main.support, ∀ history : (onePacketN).InformationHistory who site.1,
      ForcedState setup leaks who history.1.state →
      |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site
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
    exact certificate_commit_historyFailure setup leaks bounds horizon scheduler sequence scale
      scale_pos scale_le_one weights targetSequence assembled n completes covers capacity slotsLe
      site late debtFree siteKey pending node history current rfl forced _ _ otherSelected inMenu
      transmits call succeeds
  -- Site failures average history failures over the belief.
  have siteEq : ∀ law, onePacketSiteFailure setup leaks bounds horizon scheduler
      (targetSequence n) site law = expect ((targetSequence n).belief who site) fun history =>
        siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site law
          history := by
    intro law
    unfold onePacketSiteFailure localFailure
    rw [expect_localRun]
    rfl
  have historyUnit : ∀ law history, 0 ≤ siteHistoryFailure setup leaks bounds horizon scheduler
      (targetSequence n) site law history ∧ siteHistoryFailure setup leaks bounds horizon
        scheduler (targetSequence n) site law history ≤ 1 := by
    intro law history
    unfold siteHistoryFailure
    exact ⟨expect_nonneg _ _ fun final _ => by split <;> norm_num,
      expect_le_const _ _ (payoffIntegrable_of_finite _ _) 1 fun final _ => by
        split <;> norm_num⟩
  have unforcedNonneg : 0 ≤ unforced := le_trans (expect_nonneg _ _ fun history _ => by
    split <;> norm_num) unforcedMass
  -- Every slot commitment of the late option fails like the choice.
  have near : ∀ other ∈ main.support,
      |onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
          (PMF.pure choice) -
        onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n) site
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
        calc _ ≤ |siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice) history - lumped history| +
              |lumped history - siteHistoryFailure setup leaks bounds horizon scheduler
                (targetSequence n) site (PMF.pure other) history| := abs_sub_le _ _ _
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
    (onePacketFailed setup leaks bounds horizon scheduler ((onePacketN).agentAt site)) choice
    _ main (by have := (scale_pos n).le; linarith)
    (by linarith) mass near
  exact le_of_le_of_eq mixed (by ring)

end Certificate

end Vegas
