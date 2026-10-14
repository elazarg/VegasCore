/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapExchange
import Vegas.Game.OnePacketSwapRegular
import Vegas.Game.OnePacketReplayExists

/-! # Common fibers at an own turn from the swap between two points

At an own-turn forced decision site of `who`, take two intended histories `x`
and `y` of the intended site the native site projects to. The swap between their
end points, at the table of handles accepted at the site, maps each regular
native history of the site replaying `x` to a regular native history of the site
replaying `y`, and back. It keeps the operational record, so the regular
histories replaying `x` and those replaying `y` have the same total operational
weight (`Vegas.fiber_sum_eq_between`): every intended history of the site carries
a common fiber mass.

The swap moves raw values within the message bounds when, at any two intended
points of the site, each pair of successful commitment values lies inside the
bounds together or outside them together.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

/-- Two points whose successful commitment values lie inside the message bounds
together or outside them together. -/
def BoundsClosedBetween (bounds : MessageBounds (graph setup))
    (p q : ProtocolState setup.program) : Prop :=
  ∀ name owner payload (left right : L.Val payload),
    ProtocolState.cell? setup.program p name (.commitment owner payload) = some (.success left) →
    ProtocolState.cell? setup.program q name (.commitment owner payload) =
      some (.success right) →
    ((⟨payload, left⟩ : Raw L) ∈ bounds.values ↔ (⟨payload, right⟩ : Raw L) ∈ bounds.values)

omit [Fintype Player] in
/-- **The swap between two points keeps the message bounds** when their
commitment values are closed under the bounds. -/
theorem bounded_betweenHandlePairs {p q : ProtocolState setup.program}
    (pairs : (graph setup).SwapPairs) (table : AcceptedHandles (graph setup))
    (closed : BoundsClosedBetween bounds p q) :
    ∀ handle raw, raw ∈ bounds.values →
      (HiddenSwap.ofPairs pairs (betweenHandlePairs setup p q table)).raw handle raw ∈
        bounds.values := by
  intro handle raw member
  change EventGraph.pairSwap (betweenHandlePairs setup p q table handle) raw ∈ _
  unfold betweenHandlePairs
  split_ifs with found
  · generalize fieldCell setup found.choose = cell
    rcases cell with ⟨name, kind⟩
    cases kind with
    | publicData | privateInput | publication => exact member
    | commitment owner payload =>
        cases foundFirst : ProtocolState.cell? setup.program p name (.commitment owner payload)
          with
        | none => simp only [commitmentRawPair, foundFirst]; exact member
        | some firstValue =>
            cases foundSecond : ProtocolState.cell? setup.program q name
                (.commitment owner payload) with
            | none => simp only [commitmentRawPair, foundFirst, foundSecond]; exact member
            | some secondValue =>
                cases firstValue with
                | failure => simp only [commitmentRawPair, foundFirst, foundSecond]; exact member
                | success left =>
                    cases secondValue with
                    | failure =>
                        simp only [commitmentRawPair, foundFirst, foundSecond]; exact member
                    | success right =>
                        have iff := closed name owner payload left right foundFirst foundSecond
                        simp only [commitmentRawPair, foundFirst, foundSecond]
                        split_ifs
                        · exact member
                        · simp only [EventGraph.pairSwap]
                          by_cases isLeft : raw = ⟨payload, left⟩
                          · subst isLeft
                            rw [@Equiv.swap_apply_left _
                                (fun a b => Classical.propDecidable (a = b))]
                            exact iff.mp member
                          · by_cases isRight : raw = ⟨payload, right⟩
                            · subst isRight
                              rw [@Equiv.swap_apply_right _
                                  (fun a b => Classical.propDecidable (a = b))]
                              exact iff.mpr member
                            · rw [@Equiv.swap_apply_of_ne_of_ne _
                                (fun a b => Classical.propDecidable (a = b)) _ _ _
                                isLeft isRight]
                              exact member
  · exact member

omit [Fintype Player] in
theorem BoundsClosedBetween.symm {p q : ProtocolState setup.program}
    (closed : BoundsClosedBetween bounds p q) : BoundsClosedBetween bounds q p :=
  fun name owner payload left right foundFirst foundSecond =>
    (closed name owner payload right left foundSecond foundFirst).symm

omit [DecidableEq (CellTy Player L)] in
/-- **Swapping back undoes a swap**: the images of a history under two equal
swaps, one after the other, give back the history. -/
theorem mapHistory_mapHistory_of_swap_eq {first second : HiddenSwap (graph setup)}
    (same : second = first)
    (firstClosed : ∀ state ∈ (initialLaw setup).support,
      state.config.inputs ∈ swapAllowed first → state.swap first ∈ (initialLaw setup).support)
    (firstBounded : ∀ handle raw, raw ∈ bounds.values → first.raw handle raw ∈ bounds.values)
    (secondClosed : ∀ state ∈ (initialLaw setup).support,
      state.config.inputs ∈ swapAllowed second → state.swap second ∈ (initialLaw setup).support)
    (secondBounded : ∀ handle raw, raw ∈ bounds.values → second.raw handle raw ∈ bounds.values)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (firstGuard : SwapGuardState setup first (swapAllowed first) history.state)
    (secondGuard : SwapGuardState setup second (swapAllowed second)
      ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler first firstClosed
        firstBounded).mapHistory history firstGuard).state) :
    (onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler second secondClosed
        secondBounded).mapHistory
      ((onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler first firstClosed
        firstBounded).mapHistory history firstGuard) secondGuard = history := by
  subst same
  exact StateSymmetry.mapHistory_mapHistory
    (onePacketSwapSymmetry_involutive bounds (initialLaw setup) horizon scheduler second
      secondClosed secondBounded (swapAllowed_closed second)) history firstGuard


section Site

variable {who : Player}
  {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup leaks).PlayerEntry} {view : (application setup leaks).PlayerView}

omit [Fintype Player] [DecidableEq (CellTy Player L)] in
/-- Two intended histories of one intended site end at points their player
observes alike. -/
theorem sameView_of_site {x y : setup.intendedModel.InformationHistory who sourceSite.1}
    {p q : ProtocolState setup.program} (xState : x.1.state = some p)
    (yState : y.1.state = some q) :
    ProtocolState.observe who setup.program p = ProtocolState.observe who setup.program q := by
  have seen := ((setup.intended_info who x.1.trace).symm.trans x.2).trans
    ((setup.intended_info who y.1.trace).symm.trans y.2).symm
  rw [xState, yState] at seen
  exact Option.some.inj seen

variable (wellFormed : setup.WellFormed)
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {n : ℕ}
  (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
    scheduler who site.1)
  (decision : site.1 = some (past, view))
  (projected : sourceSite.1 = projectView setup leaks who site.1)
  (ownIntended : ∀ history : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who site.1,
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
    OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
      who history.1.trace)
  (mixed : (sequence n).IsFullyMixed)

omit [DecidableEq (CellTy Player L)] in
include wellFormed forced decision ownIntended in
/-- **A regular history of the site replays an intended history with an end
point.** -/
theorem replay_of_regular
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1)
    (regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    ∃ (control : (application setup leaks).Control) (replay : setup.intendedProtocol.History)
      (point : ProtocolState setup.program), history.1.state = some control ∧
      control.execution.observe (application setup leaks) who = view ∧
      intendedHistory? setup leaks bounds horizon scheduler history.1.trace = some replay ∧
      replay.state = some point := by
  have forcedState := forcedState_of_regular wellFormed (sequence n) decision forced history
    regular (ownIntended history regular)
  obtain ⟨control, stateEq, viewEq⟩ := state_of_decision history decision
  rw [stateEq] at forcedState
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome (sequence n) who history.1.trace control
    stateEq forcedState regular (ownIntended history regular)
  obtain ⟨rank, point, ordered, decoded, _⟩ := forcedState
  refine ⟨control, replay, point, stateEq, viewEq, replayed, ?_⟩
  rw [intendedHistory?_state history.1.trace replayed, stateEq, ← decoded]
  have exists_ordered : ∃ rank, control.execution.application.config.cut.IsPrefix rank :=
    ⟨rank, ordered⟩
  change decodedPoint setup _ = _
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true exists_ordered), show exists_ordered.choose = rank from
    isPrefix_unique exists_ordered.choose_spec ordered]

/-- The class of regular histories of the site whose replay projection is a
given intended history. -/
abbrev ReplayClass (point : setup.intendedModel.InformationHistory who sourceSite.1) :=
  {history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1 //
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace ∧
      replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
        history = point}

omit [DecidableEq (CellTy Player L)] in
include wellFormed forced ownIntended in
/-- A member of a replay class replays its intended history. -/
theorem replay_of_class {x : setup.intendedModel.InformationHistory who sourceSite.1}
    (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    ∃ (control : (application setup leaks).Control) (point : ProtocolState setup.program),
      history.1.1.state = some control ∧
      control.execution.observe (application setup leaks) who = view ∧
      intendedHistory? setup leaks bounds horizon scheduler history.1.1.trace = some x.1 ∧
      x.1.state = some point := by
  obtain ⟨control, replay, point, stateEq, viewEq, replayed, pointEq⟩ :=
    replay_of_regular wellFormed forced decision ownIntended history.1 history.2.1
  have same := replayProjection_eq decision projected history.1 replayed
  rw [history.2.2] at same
  subst same
  exact ⟨control, point, stateEq, viewEq, replayed, pointEq⟩

section Points

variable {x y : setup.intendedModel.InformationHistory who sourceSite.1}
  {p q : ProtocolState setup.program} (xState : x.1.state = some p)
  (yState : y.1.state = some q)

variable (view) in
/-- **The swap between the end points of two intended histories of a site**, at
the table of handles accepted at the native site. -/
def siteSwap : HiddenSwap (graph setup) :=
  HiddenSwap.ofPairs (betweenPairs (publicCellsAgree_of_observe (sameView_of_site xState yState))
      (commitmentCellsSucceed_of_intended wellFormed xState yState))
    (betweenHandlePairs setup p q view.application.publicView.accepted)

variable (closed : BoundsClosedBetween bounds p q)

variable (view) in
/-- The symmetry of the one-packet game given by the swap between two end points. -/
abbrev siteSymmetry :=
  onePacketSwapSymmetry bounds (initialLaw setup) horizon scheduler
    (siteSwap view wellFormed xState yState)
    (initialClosed_swapAllowed (siteSwap view wellFormed xState yState))
    (bounded_betweenHandlePairs _ _ closed)

variable {event : (graph setup).EventId}
  (turn : view.application.publicView.ownTurn? who = some event)

include forced ownIntended turn in
/-- **Histories replaying `x` are guarded** by the swap toward `y`. -/
theorem siteGuard (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    SwapGuardState setup (siteSwap view wellFormed xState yState)
      (swapAllowed (siteSwap view wellFormed xState yState)) history.1.1.state := by
  obtain ⟨control, point, stateEq, viewEq, replayed, pointEq⟩ :=
    replay_of_class wellFormed forced decision projected ownIntended history
  rw [xState] at pointEq
  cases pointEq
  obtain ⟨⟨⟨state, trace⟩, info⟩, member⟩ := history
  change state = some control at stateEq
  subst stateEq
  refine swapGuardState_of_replay wellFormed xState yState who (sameView_of_site xState yState)
    trace replayed ?_ (table := view.application.publicView.accepted)
    (by rw [← viewEq]; rfl)
  have ownTurn : control.execution.application.publicView.ownTurn? who = some event := by
    rw [← viewEq] at turn
    exact turn
  exact readyOwn_of_ownTurn _ ownTurn

/-- **The image of a history replaying `x` is at the site.** -/
theorem siteImage_info
    (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    (onePacketInformation setup leaks bounds horizon scheduler).infoOf who
      ((siteSymmetry view wellFormed xState yState closed).mapHistory history.1.1
        (siteGuard wellFormed forced decision projected ownIntended xState yState turn
          history)).trace = site.1 := by
  have guarded := siteGuard wellFormed forced decision projected ownIntended xState yState turn
    history
  obtain ⟨control, point, stateEq, viewEq, replayed, pointEq⟩ :=
    replay_of_class wellFormed forced decision projected ownIntended history
  rw [xState] at pointEq
  cases pointEq
  obtain ⟨⟨⟨state, trace⟩, info⟩, member⟩ := history
  change state = some control at stateEq
  subst stateEq
  have owned : ∀ field handle, view.application.publicView.accepted field = some handle →
      ∃ payload, (graph setup).layout field = .binding handle.1 payload := by
    intro field handle accepted
    rw [← viewEq] at accepted
    exact accepted_owner_of_trace trace accepted
  have fixes := fixes_between (publicAgree := publicCellsAgree_of_observe
    (sameView_of_site xState yState))
    (succeed := commitmentCellsSucceed_of_intended wellFormed xState yState)
    (sameView_of_site xState yState) owned
  exact (infoOf_mapTrace_of_fixes _ _ _ fixes ⟨some control, trace⟩ guarded
    (info.trans decision)).trans decision.symm

include mixed in
/-- **The image of a history replaying `x` is regular and replays `y`.** -/
theorem siteImage_class
    (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        ((siteSymmetry view wellFormed xState yState closed).mapHistory history.1.1
          (siteGuard wellFormed forced decision projected ownIntended xState yState turn
            history)).trace ∧
      replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
        ⟨_, siteImage_info wellFormed forced decision projected ownIntended xState yState closed
          turn history⟩ = y := by
  have guarded := siteGuard wellFormed forced decision projected ownIntended xState yState turn
    history
  have info := siteImage_info wellFormed forced decision projected ownIntended xState yState
    closed turn history
  obtain ⟨control, point, stateEq, viewEq, replayed, pointEq⟩ :=
    replay_of_class wellFormed forced decision projected ownIntended history
  rw [xState] at pointEq
  cases pointEq
  have sameView := sameView_of_site xState yState
  have sameLength := setup.intendedProtocol_length_eq_of_observe xState yState who sameView
  obtain ⟨⟨⟨state, trace⟩, member⟩, _⟩ := history
  change state = some control at stateEq
  subst stateEq
  have ownTurn : (control.execution.observe (application setup leaks)
      who).application.publicView.ownTurn? who = some event := by
    rw [viewEq]
    exact turn
  refine ⟨regularTrace_mapTrace wellFormed xState yState sameLength _
    (initialClosed_swapAllowed (siteSwap view wellFormed xState yState))
    (bounded_betweenHandlePairs _ _ closed) mixed who trace guarded replayed ownTurn, ?_⟩
  apply Subtype.ext
  exact replayProjection_eq decision projected _
    (intendedHistory?_mapTrace_full xState yState sameLength _
      (initialClosed_swapAllowed (siteSwap view wellFormed xState yState))
      (bounded_betweenHandlePairs _ _ closed) trace guarded replayed)

include mixed in
/-- **The map of the histories replaying `x` to those replaying `y`.** -/
def siteMap (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    ReplayClass (sequence := sequence) (n := n) decision projected y :=
  ⟨⟨_, siteImage_info wellFormed forced decision projected ownIntended xState yState closed turn
      history⟩,
    siteImage_class wellFormed forced decision projected ownIntended mixed xState yState closed
      turn history⟩


include forced ownIntended mixed turn in
/-- **The swap between two end points exchanges their replay classes.** -/
theorem siteMap_siteMap {closed' : BoundsClosedBetween bounds q p}
    (history : ReplayClass (sequence := sequence) (n := n) decision projected x) :
    siteMap wellFormed forced decision projected ownIntended mixed yState xState closed' turn
      (siteMap wellFormed forced decision projected ownIntended mixed xState yState closed turn
        history) = history := by
  apply Subtype.ext
  apply Subtype.ext
  exact mapHistory_mapHistory_of_swap_eq
    (hiddenSwap_between_comm view.application.publicView.accepted) _ _ _ _ history.1.1 _ _


open Classical in
include wellFormed forced ownIntended mixed xState yState closed turn in
/-- **Two end points have the same fiber.** The regular histories of the site
replaying `x` and those replaying `y` have the same total operational weight. -/
theorem fiber_sum_eq_of_points
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    (closed' : BoundsClosedBetween bounds q p) :
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = x,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) =
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = y,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) :=
  fiber_sum_eq_of_swap (steps := steps) _ x y
    { toFun := siteMap wellFormed forced decision projected ownIntended mixed xState yState
        closed turn
      invFun := siteMap wellFormed forced decision projected ownIntended mixed yState xState
        closed' turn
      left_inv := siteMap_siteMap wellFormed forced decision projected ownIntended mixed xState
        yState closed turn
      right_inv := siteMap_siteMap wellFormed forced decision projected ownIntended mixed yState
        xState closed' turn }
    (fun history => operationalRecord_mapTrace _ _ _ history.1.1.trace _)

end Points

omit [DecidableEq (CellTy Player L)] in
include wellFormed forced ownIntended in
/-- Once some regular history of the site replays an intended history, every
intended history of the intended site has an end point. -/
theorem pointed_of_class {x : setup.intendedModel.InformationHistory who sourceSite.1}
    (history : ReplayClass (sequence := sequence) (n := n) decision projected x)
    (other : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∃ point, other.1.state = some point := by
  obtain ⟨_, point, _, _, _, pointEq⟩ :=
    replay_of_class wellFormed forced decision projected ownIntended history
  have seen := ((setup.intended_info who x.1.trace).symm.trans x.2).trans
    ((setup.intended_info who other.1.trace).symm.trans other.2).symm
  rw [pointEq] at seen
  cases otherState : other.1.state with
  | none =>
      rw [otherState] at seen
      cases seen
  | some found => exact ⟨found, rfl⟩

variable {event : (graph setup).EventId}
  (turn : view.application.publicView.ownTurn? who = some event)

open Classical in
include wellFormed forced ownIntended mixed turn in
/-- **Common fibers from the swap between two points.** At an own-turn forced
decision site whose regular histories replay intended histories, if any two end
points of the intended site are closed under the message bounds, then the
regular histories replaying any two intended histories of the site have the same
total operational weight. -/
theorem fiber_sum_eq_between
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    (closed : ∀ (x y : setup.intendedModel.InformationHistory who sourceSite.1)
      (p q : ProtocolState setup.program), x.1.state = some p → y.1.state = some q →
        BoundsClosedBetween bounds p q)
    (x y : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = x,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) =
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧
        replayProjection setup leaks bounds horizon scheduler sourceSite site decision projected
          history = y,
      operationalWeight setup leaks who (steps.mass n)
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) := by
  have between : ∀ (first second : setup.intendedModel.InformationHistory who sourceSite.1),
      Nonempty (ReplayClass (sequence := sequence) (n := n) decision projected first) →
      ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
          replayProjection setup leaks bounds horizon scheduler sourceSite site decision
            projected history = first,
        operationalWeight setup leaks who (steps.mass n)
          (operationalRecord setup leaks bounds horizon scheduler history.1.trace) =
      ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
          history.1.trace ∧
          replayProjection setup leaks bounds horizon scheduler sourceSite site decision
            projected history = second,
        operationalWeight setup leaks who (steps.mass n)
          (operationalRecord setup leaks bounds horizon scheduler history.1.trace) := by
    rintro first second ⟨member⟩
    obtain ⟨p, firstState⟩ :=
      pointed_of_class wellFormed forced decision projected ownIntended member first
    obtain ⟨q, secondState⟩ :=
      pointed_of_class wellFormed forced decision projected ownIntended member second
    exact fiber_sum_eq_of_points wellFormed forced decision projected ownIntended mixed
      firstState secondState (closed first second p q firstState secondState) turn
      (closed second first q p secondState firstState)
  by_cases firstMember : Nonempty (ReplayClass (sequence := sequence) (n := n) decision
      projected x)
  · exact between x y firstMember
  by_cases secondMember : Nonempty (ReplayClass (sequence := sequence) (n := n) decision
      projected y)
  · exact (between y x secondMember).symm
  rw [Finset.sum_eq_zero fun history member =>
      absurd ⟨⟨history, (Finset.mem_filter.mp member).2⟩⟩ firstMember,
    Finset.sum_eq_zero fun history member =>
      absurd ⟨⟨history, (Finset.mem_filter.mp member).2⟩⟩ secondMember]

end Site


end Vegas
