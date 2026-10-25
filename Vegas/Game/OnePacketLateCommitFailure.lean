/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCertificate
import Vegas.Game.AsyncDeviationForeign

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
committing at a prepared slot, by a response of the menu whose candidate
succeeds, fails from every forced history within the horizon times twice the
cube of the scale of the certificate's lumped failure of the slot
(`Vegas.certificate_commit_decisionFailure`, `Vegas.certificateCommitFailure`).
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
profileOf fail where the decided binding `event` of `who` fails in the store,
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
theorem abs_localFailure_pure_sub_le_of_mass
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

open Classical in
theorem certificate_commit_decisionFailure
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
    |expect ((onePacketN).runBehavioralFrom
        (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)))
        (2 * horizon + 1) history.1)
        (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) -
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
  unfold certificateCommitFailure
  rw [current]
  exact core

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

end Certificate

end Vegas
