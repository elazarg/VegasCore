module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketLateCertificate
public import Vegas.Game.OnePacketCertificateLumping
public import Vegas.Game.OnePacketNonLateChoices
public import Vegas.Game.AsyncDeviationForeign

@[expose] public section

/-! # Primitive failure after a prepared-slot commitment

The actual supplied assessment and its certificate kernel compare fixed
commitments from every forced history. Generic pending-lumping estimates
provide the finite-horizon comparison; successful typed candidates are
derived from the actual menu response.
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
    {target : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy
          player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn (timeouts := timeouts) target who relevant profileOf
      (DecisionFailed (timeouts := timeouts)) δ Y)
    (site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who)
    (isRelevant : relevant site) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who site.1 = some key) (option : LateOption')
    {event : (graph setup).EventId} {payload : L.Ty}
    (imageOfBinding : BindingImage (timeouts := timeouts) (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage (timeouts := timeouts) event who payload state))
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup timeouts leaks).Control),
      history.state = some control →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.logs who = execution.logs who ++ entry :: rest) →
      history.state ∈ lumping.keep site key)
    (ready : execution.application.config.cut.Ready event)
    (empty : commitStatuses (timeouts := timeouts) event who payload execution.application
      execution.network.pending =
      [])
    (response : (application setup timeouts leaks).Action)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who))
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup timeouts leaks).submit execution.application
      who
      material) (who, .prepared serial) payload = true)
    (next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (nextState : next.state = some ⟨remaining, none,
      execution.respond (application setup timeouts leaks) who response⟩) :
    |expect ((onePacketInformation setup timeouts leaks bounds horizon scheduler).runBehavioralFrom
        (profileOf site option) (2 * horizon + 1) next)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[2 * horizon
        + 1]
        (PMF.pure (imageOfBinding (committedImage (timeouts := timeouts) event who (who, .prepared
          serial)
          (operationalState setup timeouts leaks (some ⟨remaining, some who, execution⟩))))))
        (lumping.failure key)| ≤ (2 * horizon + 1 : ℕ) * δ := by
  have configEq := ((reactive_respond_application timeouts) leaks execution who response).1
  have keptNext : next.state ∈ lumping.keep site key := by
    refine keptOf next _ nextState configEq ?_
    have respondRecall : ∃ emitted, (execution.respond (application setup timeouts leaks) who
        response).logs who = execution.logs who ++
          [⟨execution.observe (application setup timeouts leaks) who, response, emitted⟩] := by
      rcases response with ⟨transmission⟩
      cases transmission <;>
        simp only [ReactiveApplication.Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩
    obtain ⟨emitted, recallEq⟩ := respondRecall
    exact ⟨_, [], recallEq⟩
  have imageNext : lumping.image key next.state = imageOfBinding
    (committedImage (timeouts := timeouts) event who
      (who, .prepared serial) (operationalState setup timeouts leaks
        (some ⟨remaining, some who, execution⟩))) := by
    rw [imageBinding, nextState, committed_bindingImage (timeouts := timeouts) bounds start current
      ready.1 empty
      response member sends packet succeeds]
  have lumped := lumping.abs_failure_sub_le_of_keep (2 * horizon + 1) site
    isRelevant key
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
    {target : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy
          player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn (timeouts := timeouts) target who relevant profileOf
      (DecisionFailed (timeouts := timeouts)) δ Y)
    (site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who)
    (isRelevant : relevant site) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who site.1 = some key) (option : LateOption')
    {event : (graph setup).EventId} {payload : L.Ty}
    (imageOfBinding : BindingImage (timeouts := timeouts) (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage (timeouts := timeouts) event who payload state))
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup timeouts leaks).Control),
      history.state = some control →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.logs who = execution.logs who ++ entry :: rest) →
      history.state ∈ lumping.keep site key)
    (ready : execution.application.config.cut.Ready event)
    (empty : commitStatuses (timeouts := timeouts) event who payload execution.application
      execution.network.pending =
      [])
    (installed : ∀ player, (onePacketInformation setup timeouts leaks bounds horizon
      scheduler).BehavioralPolicy player)
    (agreeLonger : ∀ history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History,
      (∀ control, history.state = some control →
        (execution.logs who).length < (control.execution.logs who).length) →
      ∀ player, installed player
          ((onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf player
            history.trace) =
        profileOf site option player
          ((onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf player
            history.trace))
    (response : (application setup timeouts leaks).Action)
    (responseLaw : (installed who (some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who))
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup timeouts leaks).submit execution.application
      who
      material) (who, .prepared serial) payload = true) :
    |expect ((onePacketInformation setup timeouts leaks bounds horizon scheduler).runBehavioralFrom
        installed (2 * horizon + 1) start)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then 1 else 0) -
      expect ((fun law => law.bind (lumping.kernel key option))^[2 * horizon
        + 1]
        (PMF.pure (imageOfBinding (committedImage (timeouts := timeouts) event who (who, .prepared
          serial)
          (operationalState setup timeouts leaks (some ⟨remaining, some who, execution⟩))))))
        (lumping.failure key)| ≤ (2 * horizon + 1 : ℕ) * δ := by
  classical
  let menu := bounds.onePacketMenu timeouts leaks
  let model := onePacketInformation setup timeouts leaks bounds horizon scheduler
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed start
    who remaining execution current
  rw [decodeProfile_eq_map, responseLaw, PMF.pure_map] at stepStates
  have nextState : ∀ next ∈ (model.runBehavioralFrom installed 1 start).support,
      next.state = some ⟨remaining, none,
        execution.respond (application setup timeouts leaks) who response⟩ := by
    intro next nextMember
    have inStates : next.state ∈ ((model.runBehavioralFrom installed 1 start).map
        History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nextMember, rfl⟩
    rw [stepStates, PMF.mem_support_pure_iff] at inStates
    exact inStates
  have nextRecall : (execution.logs who).length <
      ((execution.respond (application setup timeouts leaks) who response).logs who).length := by
    have longer := (application setup timeouts leaks).respond_recall_length execution who who
      response
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
    have grown := (application setup timeouts leaks).reaches_recall_prefix (initialLaw setup)
      horizon
      scheduler rawPath _ control (nextState next nextMember) laterState who
    exact lt_of_lt_of_le nextRecall grown.length_le
  rw [split, expect_bind_tower_bounded _ _ _ (C := 1) (fun final => by
    split <;> norm_num)]
  refine abs_expect_sub_le_of_forall _ _ (bound := 1) (fun next => ?_) (fun next nextMember =>
    lateCommit_failure_next (timeouts := timeouts) lumping site isRelevant siteKey option
      imageOfBinding imageBinding
      start current keptOf ready empty response member sends packet succeeds next
      (nextState next nextMember))
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := expect_nonneg (model.runBehavioralFrom (profileOf site option)
      (2 * horizon + 1) next)
      (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else 0)
      (fun final _ => by split <;> norm_num)
    linarith
  · exact expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 1) (fun final => by
      split <;> norm_num)) 1 (fun final _ => by split <;> norm_num)

section Certificate

variable [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

variable (setup timeouts leaks bounds horizon scheduler) in
/-- **The lumped failure of a late commitment** at a slot: the certificate's
lumped failure, at a key, of the committed image of the slot at a state. -/
def certificateCommitFailure (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player) (key : LateKey setup timeouts
        leaks)
    (event : (graph setup).EventId) (serial : Nat)
    (state : (application setup timeouts leaks).ProtocolState) : ℝ :=
  expect ((fun law => law.bind ((certificateLumping setup timeouts leaks bounds horizon scheduler
      sequence scale scale_pos scale_le_one covers capacity slotsLe weights targetSequence
      assembled n who).kernel key (none : LateOption slots)))^[2 * horizon + 1]
    (PMF.pure (Sum.inr (committedImage (timeouts := timeouts) event who (who, .prepared serial)
      (operationalState setup timeouts leaks state)))))
    ((certificateLumping setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one covers capacity slotsLe weights targetSequence assembled n who).failure key)

open Classical in
theorem certificate_commit_decisionFailure
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
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))
    (forced : ForcedState setup timeouts leaks who history.1.state)
    (choice : (onePacketN).Choice who site.1) (response : (application setup timeouts leaks).Action)
    (selected : choice.1 = some response)
    (member : response ∈ bounds.onePacketActions timeouts leaks who
      (execution.logs who) (execution.observe (application setup timeouts leaks) who))
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (succeeds : candidateSucceeds ((application setup timeouts leaks).submit execution.application
      who
      material) (who, .prepared serial) payload = true) :
    |expect ((onePacketN).runBehavioralFrom
        (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)))
        (2 * horizon + 1) history.1)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else
          0) -
      certificateCommitFailure setup timeouts leaks bounds horizon scheduler sequence scale
        scale_pos
        scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
        serial history.1.state| ≤
      (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  classical
  let menu := bounds.onePacketMenu timeouts leaks
  let model := onePacketN
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec (timeouts := timeouts) pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨ownerEq, noPublication, binding, decided⟩ := lateKey_decides_binding setup timeouts leaks
    horizon scheduler rawTrace rfl siteKeyHere turn unrecorded node
  have unsent := (unsentFor_iff_unrecorded setup timeouts leaks horizon scheduler rawTrace rfl
    siteKeyHere event).mpr unrecorded
  have empty := commitStatuses_nil_of_unsent (timeouts := timeouts) siteKey history current unsent
    payload
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  let lumping := certificateLumping setup timeouts leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have imageBinding : ∀ state, lumping.image key state =
      Sum.inr (bindingImage (timeouts := timeouts) event who payload state) := by
    intro state
    change decisionImage (timeouts := timeouts) key state = _
    unfold decisionImage
    rw [noPublication, binding, ownerEq]
  let installed := Profile.update (sig := (onePacketN).behavioralSignature)
    (targetSequence n).strategy who
    (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
  have responseLaw : (installed who (some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response := by
    rw [← atSite]
    simp only [installed, Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_map,
      selected, Option.getD_some]
  have through := siteThrough_of_history setup timeouts leaks bounds horizon scheduler late debtFree
    siteKey history
  rw [current] at through forced
  have core := lateCommit_historyFailure (timeouts := timeouts) lumping site ⟨Or.inl late, debtFree⟩
    siteKey
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
          change ((bounds.onePacketMenu timeouts leaks).signals (initialLaw setup) horizon
            scheduler).infoOf player later.trace ≠ _
          rw [(bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon
            scheduler player later.trace]
          cases laterState : later.state with
          | none => simp [ReactiveApplication.observe]
          | some control =>
              have lengthLt := longer control laterState
              simp only [ReactiveApplication.observe]
              split_ifs
              · intro infoEq
                have recallEq := congrArg (fun info : (application setup timeouts leaks).Info =>
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

variable (setup timeouts leaks bounds horizon scheduler)

open Classical in
/-- A legal prepared-slot commitment whose declared typed candidate succeeds
has primitive failure close to its actual certificate kernel on every forced row.
The candidate-success fact is derived from the actual one-packet response. -/
theorem certificate_lateCommit_historyDecisionFailure
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
    (choice : (onePacketN).Choice who site.1) (response : (application setup timeouts leaks).Action)
    (selected : choice.1 = some response) {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {value : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, value⟩)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup timeouts leaks who history.1.state) :
    |expect ((onePacketN).runBehavioralFrom
        (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice)))
        (2 * horizon + 1) history.1)
        (fun final => if DecisionFailed (timeouts := timeouts) key final.state then (1 : ℝ) else
          0) -
      certificateCommitFailure setup timeouts leaks bounds horizon scheduler sequence scale
        scale_pos
        scale_le_one covers capacity slotsLe weights targetSequence assembled n who key event
        serial history.1.state| ≤
      (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  obtain ⟨chosen, chosenEq, member⟩ := choice_response setup timeouts leaks bounds horizon
    scheduler site
    atSite choice
  rw [selected] at chosenEq
  cases Option.some.inj chosenEq
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup timeouts leaks bounds horizon scheduler atSite history
  subst recallEq
  subst observeEq
  have lookupAfter : ((application setup timeouts leaks).submit execution.application who
      material).candidates.lookup (who, .prepared serial) = .openable ⟨payload, value⟩ := by
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).candidates.lookup (who, .prepared serial) = _
    rw [Submission.candidateAfter_eq]
    exact after
  have succeeds : candidateSucceeds ((application setup timeouts leaks).submit
    execution.application who
      material) (who, .prepared serial) payload = true := by
    unfold candidateSucceeds
    simp only [EventGraphRuntime.State.bindingResult, lookupAfter]
    simp [Raw.as?]
  exact certificate_commit_decisionFailure (timeouts := timeouts) sequence scale
    scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe
    site late debtFree siteKey pending node history current atSite forced choice response
    selected member sends packet succeeds

end Certificate

end Vegas
