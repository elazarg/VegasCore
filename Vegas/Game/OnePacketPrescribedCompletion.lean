/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivationCompletion

/-! # The completion point of the prescribed component at a first activation

**Trembles move an expectation by the scale.** A slot-trembled mixture whose
main law has expectation `target` of a function bounded by `bound` has
expectation within six times the scale times `bound` of `target`
(`Vegas.abs_expect_slotTrembledChoice_sub_le`).

**The prescribed component at a first activation.** Under the asynchronous
contract, the timeliness margin and retention of covered canonical packets, at
a transmitting first activation of `who` for a binding of rank `rank` whose
configuration decodes at `rank` to a point of the intended game, installing the
slot-trembled prescribed component of an intended assessment gives, under play
of any other policies until the event completes, the completion-point law of
the source step of the assessment's as-if-honest law at the decoded point, with
success one and error six times the scale
(`Vegas.firstActivation_prescribed_completionPointLaw`): the as-if-honest
choices commit intended values, each completing at the source step committing
it, and the trembles carry at most the scale's share.
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

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A mixture of two values bounded by `left` and `right` is bounded by the
weight times `left` plus `right`. -/
private theorem abs_mix_le {weight first second left right : ℝ} (nonnegative : 0 ≤ weight)
    (le_one : weight ≤ 1) (firstBound : |first| ≤ left) (secondBound : |second| ≤ right) :
    |weight * first + (1 - weight) * second| ≤ weight * left + right := by
  have rest : 0 ≤ 1 - weight := by linarith
  have rightNonneg : 0 ≤ right := (abs_nonneg _).trans secondBound
  calc |weight * first + (1 - weight) * second|
      ≤ |weight * first| + |(1 - weight) * second| := abs_add_le _ _
    _ = weight * |first| + (1 - weight) * |second| := by
        rw [abs_mul, abs_mul, abs_of_nonneg nonnegative, abs_of_nonneg rest]
    _ ≤ weight * left + (1 - weight) * right := by
        gcongr
    _ ≤ weight * left + right := by nlinarith

/-- **Trembles move an expectation by the scale.** If the main law of a
slot-trembled mixture gives a function bounded by `bound` the expectation
`target`, with `target` bounded by `bound`, the mixture gives it an expectation
within six times the scale times `bound` of `target`. -/
theorem abs_expect_slotTrembledChoice_sub_le {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
        info))
    (value : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info → ℝ) {target bound : ℝ} (bounded : ∀ choice, |value choice| ≤ bound)
    (targetBounded : |target| ≤ bound) (mainEq : expect main value = target) :
    |expect (slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who info main alternative slot) value - target| ≤
      6 * scale * bound := by
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans targetBounded
  have gap : ∀ law : PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who info), |expect law value - target| ≤ 2 * bound := by
    intro law
    have inside := abs_le.mp (expect_abs_le_of_bounded (μ := law) boundNonneg bounded)
    have targetInside := abs_le.mp targetBounded
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold slotTrembledChoice
  rw [expect_mix_of_finite, expect_mix_of_finite, expect_mix_of_finite, mainEq]
  have cube : scale ^ 3 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have square : scale ^ 2 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have innermost : |scale * (expect alternative value - target) +
      (1 - scale) * (target - target)| ≤ scale * (2 * bound) + 0 :=
    abs_mix_le nonnegative le_one (gap alternative) (by rw [sub_self, abs_zero])
  have middle := abs_mix_le (sq_nonneg scale) (pow_le_one₀ nonnegative le_one) (gap slot)
    innermost
  have outer := abs_mix_le (pow_nonneg nonnegative 3) (pow_le_one₀ nonnegative le_one)
    (gap ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
      scheduler who info)) middle
  have regroup : scale ^ 3 * expect ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value +
      (1 - scale ^ 3) * (scale ^ 2 * expect slot value +
        (1 - scale ^ 2) * (scale * expect alternative value + (1 - scale) * target)) - target =
      scale ^ 3 * (expect ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value - target) +
      (1 - scale ^ 3) * (scale ^ 2 * (expect slot value - target) +
        (1 - scale ^ 2) * (scale * (expect alternative value - target) +
          (1 - scale) * (target - target))) := by ring
  rw [regroup]
  refine outer.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right cube boundNonneg,
    mul_le_mul_of_nonneg_right square boundNonneg]

/-- **The prescribed component at a first activation.** Under the asynchronous
contract, the timeliness margin and retention of covered canonical packets, let
`who` be at its first activation for the binding `event` pending at a history,
whose configuration is a prefix of `rank` events decoding to a point of the
intended game, and let the canonical decision of every successful encoded
source action transmit there. Installing at the history's information state
the slot-trembled prescribed component of an intended assessment `source`, with
any other policies, until the event completes, the completion-point law is the
source step at the decoded point of the as-if-honest law of `source`, with
success one and error six times the scale, for every property `fresh` of
controls implied by the event not having failed. -/
theorem firstActivation_prescribed_completionPointLaw
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1)
    (profile : ∀ player, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (transmits : CanonicalTransmitsAt setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {fresh : (application setup leaks).Control → Prop}
    (freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store event →
      fresh control)
    (info : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).InfoState
      who)
    (observed : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info) :
    CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).behavioralSignature) profile who ((profile who).withLaw info
          (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
            scale nonnegative le_one who info)))
      rank fresh history 1
      ((asIfHonestProfile setup leaks source who info).bind fun choice =>
        ProtocolState.step setup.program point (fun _ => choice))
      (6 * scale) := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have infoEq : model.infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change (menu.signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    rw [menu.info, current]
    simp [ReactiveApplication.observe]
  have atSite := observed.symm.trans infoEq
  subst atSite
  obtain ⟨turn, readyView, _, unrecorded⟩ := pendingEvent_spec pending
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have fits := firstActivation_inclusionFits contract timely
    (menu.toRawTrace (initialLaw setup) horizon scheduler trace) rfl event turnExecution never
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler rank history := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (menu.protocol (initialLaw setup) horizon scheduler).active history.state who := by
    rw [current]
    rfl
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  intro value valueBound valueBounded
  have boundNonneg : 0 ≤ valueBound := (abs_nonneg _).trans (valueBounded point)
  have pointBounded : ∀ stop, |(completionPoint setup leaks bounds horizon scheduler rank fresh
      stop).elim 0 value| ≤ valueBound := by
    intro stop
    cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
    | none => simpa using boundNonneg
    | some target => exact valueBounded target
  rw [model.runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce profile who
      (profile who) _ _ _ history observed notStopped running active,
    expect_bind_tower_bounded _ _ _ pointBounded, one_mul]
  have stepBounded : |expect ((asIfHonestProfile setup leaks source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).bind
        fun choice => ProtocolState.step setup.program point (fun _ => choice)) value| ≤
      valueBound := expect_abs_le_of_bounded boundNonneg valueBounded
  refine abs_expect_slotTrembledChoice_sub_le nonnegative le_one who _ _ _ _ _
    (fun choice => expect_abs_le_of_bounded boundNonneg pointBounded) stepBounded ?_
  -- The as-if-honest choices complete at the source step committing them.
  change expect ((honestResponse setup leaks source who (execution.recall who)
    (execution.observe (application setup leaks) who)).map (responseChoice setup leaks bounds
      (initialLaw setup) horizon scheduler who (some (execution.recall who,
        execution.observe (application setup leaks) who)))) _ = _
  unfold honestResponse
  rw [turn]
  dsimp only
  rw [PMF.map_comp, expect_map, expect_bind_tower_bounded _ _ _ valueBounded]
  refine expect_congr_on_support fun choice member => ?_
  have encodes := asIfHonestProfile_encodes source who execution rank ordered point decoded
    (execution.recall who) event turnExecution choice member
  rcases choice with _ | action
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event action with
  | none => simp [encoded] at encodes
  | some graphAction =>
      have success := asIfHonestProfile_success source who execution rank ordered point decoded
        (execution.recall who) action member
      have sends := transmits action graphAction encoded success.1 success.2
      obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp sends
      have commits : action.CommitsValue := by
        cases action with
        | commit owner name payload choice =>
            cases choice with
            | failure => exact (success.1 owner name payload rfl).elim
            | success value => exact ⟨value, rfl⟩
        | reveal => trivial
      have effective : EffectiveDecision event graphAction := by
        unfold EffectiveDecision
        rw [node]
        exact encodeEventAction?_commitsValue setup.program event action commits graphAction
          encoded who payload outputEq
      have offered := canonical_mem_onePacket_of_pending bounds trace who event turnExecution
        unrecorded graphAction
        (retains trace who event graphAction turnExecution unrecorded fits effective sends)
      have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (execution.recall who, execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction)).1 =
          some ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction) := by
        unfold responseChoice
        simp only [offered, ↓reduceDIte]
      obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup leaks source who
        execution rank ordered point decoded (execution.recall who) _).mp member
      have legal := intended.2
      change ProtocolView.intendedMenu who setup.program
        (ProtocolState.observe who setup.program point) intended.1 at legal
      rw [same] at legal
      have law := firstActivation_commit_completionPointLaw contract timely profile history
        current event turnExecution never node graphAction material submits _ observed _ selected
        ordered decoded intendedPoint
        (decodeEventAction_encodeEventAction?_eq_some setup.program event action graphAction
          encoded) legal.2 freshOf value valueBound valueBounded
      rw [zero_mul, one_mul] at law
      simp only [Function.comp_apply, Option.bind_some, encoded]
      exact sub_eq_zero.mp (abs_nonpos_iff.mp law)

end Vegas
