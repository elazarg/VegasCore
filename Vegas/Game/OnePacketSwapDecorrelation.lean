/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapFiberSum
import GameTheoryExtensions.Math.Probability.NearDecorrelation

/-! # Records and hidden points are decorrelated at an own turn

At an own-turn forced decision site of `who`, the swap between the end points of
two intended histories of the intended site exchanges the regular histories
replaying them and keeps every operational record. So every function of the
record has the same sum over the regular histories replaying any intended
history (`Vegas.fiber_sum_record_eq_between`).

The reach of a regular history is, up to the factorization error, the intended
reach of its replay times the operational weight of its record, and its decoded
point is the end point of its replay. The weights `intended reach × operational
weight` therefore make the record and the decoded point uncorrelated, and the
Bayes belief at the site, within the factorization error and the irregular
ratio of these weights, decorrelates the record from the decoded point
(`Vegas.ForcedBeliefInputs.beliefDecorrelated`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Finset

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

section Site

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup runtime leaks).PlayerEntry} {view : (application setup runtime
    leaks).PlayerView}
  (wellFormed : setup.WellFormed)
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {n : ℕ}
  (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
    setup) horizon
    scheduler who site.1)
  (decision : site.1 = some (past, view))
  (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
  (ownIntended : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1,
    RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
    OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler)
      who history.1.trace)
  (mixed : (sequence n).IsFullyMixed) {event : (graph setup).EventId}
  (turn : view.application.publicView.ownTurn? who = some event)
  (covered : BindingFieldsCovered bounds)

open Classical in
include wellFormed forced ownIntended mixed turn covered in
/-- **Record functions have common fibers.** Every function of the operational
record has the same sum over the regular histories of the site replaying any two
intended histories of the intended site. -/
theorem fiber_sum_record_eq_between
    [Fintype ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    (weight : List (Option (OperationalState setup runtime leaks)) → ℝ)
    (x y : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
          projected
          history = x,
      weight (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) =
    ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
          projected
          history = y,
      weight (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) := by
  classical
  have between : ∀ (first second : setup.intendedModel.InformationHistory who sourceSite.1),
      Nonempty (ReplayClass (runtime := runtime) (sequence := sequence) (n := n) decision
        projected first) →
      ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
          replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
            projected history = first,
        weight (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) =
      ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
          replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
            projected history = second,
        weight (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) :=
          by
    rintro first second ⟨member⟩
    obtain ⟨p, firstState⟩ :=
      pointed_of_class (runtime := runtime) wellFormed forced decision projected ownIntended
        member first
    obtain ⟨q, secondState⟩ :=
      pointed_of_class (runtime := runtime) wellFormed forced decision projected ownIntended
        member second
    rw [← sum_subtype_eq_sum_filter, ← sum_subtype_eq_sum_filter, subtype_univ, subtype_univ]
    exact Fintype.sum_equiv
      { toFun := siteMap (runtime := runtime) wellFormed forced decision projected ownIntended
          mixed firstState
          secondState covered turn
        invFun := siteMap (runtime := runtime) wellFormed forced decision projected ownIntended
          mixed secondState
          firstState covered turn
        left_inv := siteMap_siteMap (runtime := runtime) wellFormed forced decision projected
          ownIntended mixed
          firstState secondState covered turn
        right_inv := siteMap_siteMap (runtime := runtime) wellFormed forced decision projected
          ownIntended mixed
          secondState firstState covered turn } _ _
      (fun history => congrArg weight
        (operationalRecord_mapTrace (runtime := runtime) _ _ _ history.1.1.trace _).symm)
  by_cases firstMember : Nonempty (ReplayClass (runtime := runtime) (sequence := sequence) (n :=
    n) decision
      projected x)
  · exact between x y firstMember
  by_cases secondMember : Nonempty (ReplayClass (runtime := runtime) (sequence := sequence) (n :=
    n) decision
      projected y)
  · exact (between y x secondMember).symm
  rw [sum_eq_zero fun history member =>
      absurd ⟨⟨history, (mem_filter.mp member).2⟩⟩ firstMember,
    sum_eq_zero fun history member =>
      absurd ⟨⟨history, (mem_filter.mp member).2⟩⟩ secondMember]

end Site

section Belief

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup runtime leaks).PlayerEntry} {view : (application setup runtime
    leaks).PlayerView}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
  {steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who}
  [Fintype ((onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
    who
    site.1)]
  [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
  {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}

open Classical in
/-- The product weight of a native history of the site: the intended reach of
its replay times its projected operational weight when it is regular, and zero
otherwise. -/
def ForcedBeliefInputs.productWeight {decision : site.1 = some (past, view)}
    {projected : sourceSite.1 = projectView setup runtime leaks who site.1}
    (inputs : ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles
      steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1) : ℝ :=
  if RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace then
    (setup.intendedModel.historyReachWeight (sequence n).strategy
      (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
        projected
        history).1).toReal * inputs.projectedOperational past history
  else 0

theorem ForcedBeliefInputs.productWeight_nonneg {decision : site.1 = some (past, view)}
    {projected : sourceSite.1 = projectView setup runtime leaks who site.1}
    (inputs : ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles
      steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1) :
    0 ≤ inputs.productWeight history := by
  unfold ForcedBeliefInputs.productWeight
  split_ifs
  · exact mul_nonneg ENNReal.toReal_nonneg (inputs.projectedOperational_nonneg (runtime :=
      runtime) past history)
  · exact le_rfl

open Classical in
/-- **Product weights factor.** At an own-turn forced decision site whose regular
histories replay intended histories, the sum of the product weights times a
function of the record and a function of the decoded point factors into a sum
over the intended site of the intended reach times the function of the end
point, and a common sum over the regular histories replaying a fixed `base`
of the operational weight times the function of the record. -/
theorem ForcedBeliefInputs.sum_productWeight_mul
    [Fintype (setup.intendedModel.InformationHistory who sourceSite.1)]
    (wellFormed : setup.WellFormed) (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (inputs : ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles
      steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n)
    (ownIntended : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace)
    (mixed : (sequence n).IsFullyMixed) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (covered : BindingFieldsCovered bounds)
    (first : List (Option (OperationalState setup runtime leaks)) → ℝ)
    (second : setup.ProtocolState → ℝ)
    (base : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∑ history, inputs.productWeight history *
        (first (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) *
          second (nativeDecodedState setup runtime leaks history.1.state)) =
      (∑ point : setup.intendedModel.InformationHistory who sourceSite.1,
          (setup.intendedModel.historyReachWeight (sequence n).strategy point.1).toReal *
          second point.1.state) *
        (ownerMass setup runtime leaks bounds horizon scheduler (profiles n who) past /
            inputs.sourceScale *
          ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
              history.1.trace ∧
              replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
                projected history = base,
            operationalWeight setup runtime leaks who (steps.mass n)
                (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) *
              first (operationalRecord setup runtime leaks bounds horizon scheduler
                history.1.trace)) := by
  have hidden : ∀ history, RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
    who
      history.1.trace →
      nativeDecodedState setup runtime leaks history.1.state = (replayProjection setup runtime
        leaks bounds
        horizon scheduler sourceSite site decision projected history).1.state := by
    intro history regular
    obtain ⟨_, replay, _, _, _, replayed, _⟩ :=
      replay_of_regular (runtime := runtime) wellFormed inputs.forced
        decision ownIntended history regular
    rw [← intendedHistory?_state (runtime := runtime) history.1.trace replayed,
      replayProjection_eq (runtime := runtime) decision projected history replayed]
  have fiber := fun point => fiber_sum_record_eq_between (runtime := runtime) wellFormed
    inputs.forced decision
    projected ownIntended mixed turn covered
    (fun record => operationalWeight setup runtime leaks who (steps.mass n)
      record * first record)
    point base
  rw [sum_mul]
  calc ∑ history, inputs.productWeight history *
        (first (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) *
          second (nativeDecodedState setup runtime leaks history.1.state))
      = ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
          history.1.trace,
        (setup.intendedModel.historyReachWeight (sequence n).strategy
            (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
            projected history).1).toReal * inputs.projectedOperational past
              history *
          (first (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) *
            second (nativeDecodedState setup runtime leaks history.1.state)) := by
        rw [sum_filter]
        refine sum_congr rfl fun history _ => ?_
        unfold ForcedBeliefInputs.productWeight
        split_ifs <;> simp
    _ = ∑ point, ∑ history ∈ ({history | RegularTrace setup runtime leaks bounds horizon scheduler
          (sequence n) who history.1.trace} : Finset _) with replayProjection setup runtime leaks
            bounds
          horizon scheduler sourceSite site decision projected history = point,
        (setup.intendedModel.historyReachWeight (sequence n).strategy
            (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
            projected history).1).toReal * inputs.projectedOperational past
              history *
          (first (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) *
            second (nativeDecodedState setup runtime leaks history.1.state)) :=
        (sum_fiberwise _ _ _).symm
    _ = _ := by
      refine sum_congr rfl fun point _ => ?_
      rw [filter_filter, ← fiber point, mul_sum, mul_sum]
      refine sum_congr rfl fun history member => ?_
      obtain ⟨regular, same⟩ := (mem_filter.mp member).2
      rw [hidden history regular, same]
      unfold ForcedBeliefInputs.projectedOperational
      ring

open Classical in
/-- **The record and the decoded point are decorrelated at an own turn.** At an
own-turn forced decision site of `who` whose regular histories replay intended
histories, under a Bayes consistent native assessment playing the stage-`n`
profile at a site of positive mass, with bounds covering every binding field,
the Bayes belief at the site decorrelates the operational record from the
decoded point, up to an explicit bound in the factorization error and the
irregular ratio. -/
theorem ForcedBeliefInputs.beliefDecorrelated
    [Finite (setup.intendedModel.InformationHistory who sourceSite.1)]
    (wellFormed : setup.WellFormed) (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (inputs : ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles
      steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n)
    (ownIntended : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace)
    (mixed : (sequence n).IsFullyMixed) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (covered : BindingFieldsCovered bounds)
    {target : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).BehavioralAssessment}
    {antichain : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).DecisionInformationAntichain}
    (played : target.strategy = profiles n)
    (bayes : BehavioralAssessment.IsBayesConsistent _ target antichain)
    (positive : 0 < (onePacketInformation setup runtime leaks bounds horizon
      scheduler).informationMass
      target.strategy who site)
    (floorPos : 0 < floors n) (scaleNonneg : 0 ≤ scale n) (slackNonneg : 0 ≤ slack)
    (factorSmall : (1 + steps.error n) ^ (2 * horizon + 1) - 1 < 1) :
    BeliefDecorrelated (target.belief who site)
      (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
        history.1.trace)
      (fun history => nativeDecodedState setup runtime leaks history.1.state)
      (3 * (2 * (((1 + steps.error n) ^ (2 * horizon + 1) - 1) +
          Fintype.card ((onePacketInformation setup runtime leaks bounds horizon
            scheduler).InformationHistory who site.1) * (slack * scale n / floors n ^ depth) *
            (1 + ((1 + steps.error n) ^ (2 * horizon + 1) - 1))) /
        (1 - ((1 + steps.error n) ^ (2 * horizon + 1) - 1)))) := by
  have := Fintype.ofFinite (setup.intendedModel.InformationHistory who sourceSite.1)
  set error := (1 + steps.error n) ^ (2 * horizon + 1) - 1 with errorEq
  set ratio := (Fintype.card ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1) : ℝ) * (slack * scale n / floors n ^ depth)
    with ratioEq
  have errorNonneg : 0 ≤ error := by
    have := one_le_pow₀ (n := 2 * horizon + 1)
      (show (1 : ℝ) ≤ 1 + steps.error n by linarith [steps.error_nonneg n])
    linarith
  have ratioNonneg : 0 ≤ ratio :=
    mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg slackNonneg scaleNonneg) (pow_nonneg floorPos.le _))
  have vZero : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
    who
      history.1.trace → inputs.productWeight history = 0 := fun history
        irregular => by
    unfold ForcedBeliefInputs.productWeight
    simp [irregular]
  have regClose : ∀ history, RegularTrace setup runtime leaks bounds horizon scheduler (sequence
    n) who
      history.1.trace →
      |((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal - inputs.productWeight history| ≤
        error * inputs.productWeight history := fun history regular => by
    unfold ForcedBeliefInputs.productWeight
    simp only [regular, ↓reduceIte]
    rw [played]
    exact inputs.factor_close decision history regular
  have vSum : ∑ history, inputs.productWeight history =
      ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        history.1.trace, inputs.productWeight history := by
    rw [← sum_filter_add_sum_filter_not univ (fun history : (onePacketInformation setup runtime
      leaks
      bounds horizon scheduler).InformationHistory who site.1 => RegularTrace setup runtime leaks
        bounds
        horizon scheduler (sequence n) who history.1.trace),
      sum_eq_zero (fun history member => vZero history (mem_filter.mp member).2), add_zero]
  have regUpper : ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
      who history.1.trace,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal ≤
      (1 + error) * ∑ history, inputs.productWeight history := by
    rw [vSum, mul_sum]
    refine sum_le_sum fun history member => ?_
    have close := regClose history (mem_filter.mp member).2
    rw [abs_sub_le_iff] at close
    linarith [close.1]
  have regLower : (1 - error) * ∑ history, inputs.productWeight history ≤
      ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
        who history.1.trace,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal := by
    rw [vSum, mul_sum]
    refine sum_le_sum fun history member => ?_
    have close := regClose history (mem_filter.mp member).2
    rw [abs_sub_le_iff] at close
    linarith [close.2]
  have irregular : ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        ¬ RegularTrace setup runtime leaks bounds horizon scheduler
      (sequence n) who history.1.trace,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal ≤
      ratio * ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
        who history.1.trace,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal := by
    rw [played]
    exact inputs.irregular_reach_le floorPos scaleNonneg slackNonneg
  have split := (sum_filter_add_sum_filter_not univ (fun history : (onePacketInformation setup
    runtime
    leaks bounds horizon scheduler).InformationHistory who site.1 => RegularTrace setup runtime
      leaks
      bounds horizon scheduler (sequence n) who history.1.trace)
    (fun history => ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).historyReachWeight
      target.strategy history.1).toReal)).symm
  have massEq : ((onePacketInformation setup runtime leaks bounds horizon scheduler).informationMass
      target.strategy who site).toReal =
      ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal :=
    informationMass_toReal_eq_sum _
  have massPos : 0 < ∑ history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1, ((onePacketInformation setup runtime leaks bounds
        horizon scheduler).historyReachWeight target.strategy history.1).toReal := by
    rw [← massEq]
    exact ENNReal.toReal_pos positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((onePacketInformation setup runtime leaks bounds horizon scheduler).informationMass_le_one
        target.strategy who site (antichain who site)))
  have irregularNonneg : 0 ≤ ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        ¬ RegularTrace setup runtime leaks bounds horizon scheduler
      (sequence n) who history.1.trace,
        ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          target.strategy history.1).toReal :=
    sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have vNonneg : 0 ≤ ∑ history, inputs.productWeight history :=
    sum_nonneg fun history _ => inputs.productWeight_nonneg history
  have vPos : 0 < ∑ history, inputs.productWeight history := by
    rcases vNonneg.lt_or_eq with positiveSum | zero
    · exact positiveSum
    · rw [← zero, mul_zero] at regUpper
      rw [split] at massPos
      nlinarith
  have base := sourceSite.2.choose
  have weights := fun first second => inputs.sum_productWeight_mul wellFormed
    decision projected
    ownIntended mixed turn covered first second base
  refine beliefDecorrelated_of_close_weights _ _ _
    (fun history => ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).historyReachWeight
      target.strategy history.1).toReal)
    (fun history => by
      rw [belief_toReal_eq_div bayes positive history, massEq])
    inputs.productWeight inputs.productWeight_nonneg
      vPos (fun first second => ?_) ?_
    (sub_pos.mpr factorSmall) ?_
  · have full := weights first second
    have onlyFirst := weights first fun _ => 1
    have onlySecond := weights (fun _ => 1) second
    have neither := weights (fun _ => 1) fun _ => 1
    simp only [mul_one, one_mul] at onlyFirst onlySecond neither
    rw [full, onlyFirst, onlySecond, neither]
    ring
  · rw [← sum_filter_add_sum_filter_not univ (fun history : (onePacketInformation setup runtime
      leaks
      bounds horizon scheduler).InformationHistory who site.1 => RegularTrace setup runtime leaks
        bounds
        horizon scheduler (sequence n) who history.1.trace)]
    have regularPart : ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace,
          |((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
            target.strategy history.1).toReal - inputs.productWeight history| ≤
        error * ∑ history, inputs.productWeight history := by
      rw [vSum, mul_sum]
      exact sum_le_sum fun history member => regClose history (mem_filter.mp member).2
    have irregularPart : ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace,
          |((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
            target.strategy history.1).toReal - inputs.productWeight history| =
        ∑ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1 with
        ¬ RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
          history.1.trace,
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
            target.strategy history.1).toReal := by
      refine sum_congr rfl fun history member => ?_
      rw [vZero history (mem_filter.mp member).2, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [irregularPart]
    have chain := mul_le_mul_of_nonneg_left regUpper ratioNonneg
    nlinarith
  · rw [split]
    linarith

end Belief

end Vegas
