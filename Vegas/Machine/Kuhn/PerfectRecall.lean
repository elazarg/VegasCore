/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Kuhn.Model

/-!
# Kuhn adapter: perfect recall and locality

Step action-determinism, the no-nontrivial-info-state-repeat theorem, and the
locality / local-support vocabulary establishing the perfect-recall hypotheses
the generic Kuhn theorem requires.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

/-- The Kuhn adapter step is action-deterministic: if two adapter joint actions
can reach the same next adapter history from the same source history, then the
joint actions are equal. The reason is structural: nonterminal successor
histories record the legal joint action that produced them, while terminal
histories allow only the no-op optional move. -/
theorem kuhnModel_stepActionDeterminism
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    ObsModelCore.StepActionDeterminism
      (view.kuhnModel horizon hMenus) := by
  classical
  intro h next left right hleft hright
  change view.kuhnStep horizon h left next ≠ 0 at hleft
  change view.kuhnStep horizon h right next ≠ 0 at hright
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · exact view.kuhnActionAtHistory_eq_of_terminal horizon h hterm left right
  · unfold kuhnStep at hleft hright
    rw [dif_neg hterm] at hleft hright
    let leftLegal := view.kuhnLegalAction horizon h hterm left
    let rightLegal := view.kuhnLegalAction horizon h hterm right
    change
      (PMF.map (fun dst => h.extendByOutcome leftLegal dst)
        (view.boundedTransition horizon h.lastState leftLegal)) next ≠ 0
        at hleft
    change
      (PMF.map (fun dst => h.extendByOutcome rightLegal dst)
        (view.boundedTransition horizon h.lastState rightLegal)) next ≠ 0
        at hright
    have hleftMem :
        next ∈
          (PMF.map (fun dst => h.extendByOutcome leftLegal dst)
            (view.boundedTransition horizon h.lastState leftLegal)).support :=
      (PMF.mem_support_iff _ _).2 hleft
    have hrightMem :
        next ∈
          (PMF.map (fun dst => h.extendByOutcome rightLegal dst)
            (view.boundedTransition horizon h.lastState rightLegal)).support :=
      (PMF.mem_support_iff _ _).2 hright
    rcases (PMF.mem_support_map_iff _ _ _).mp hleftMem with
      ⟨leftDst, hleftDstMem, hleftNext⟩
    rcases (PMF.mem_support_map_iff _ _ _).mp hrightMem with
      ⟨rightDst, hrightDstMem, hrightNext⟩
    have hleftDst :
        view.boundedTransition horizon h.lastState leftLegal leftDst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hleftDstMem
    have hrightDst :
        view.boundedTransition horizon h.lastState rightLegal rightDst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hrightDstMem
    rw [BoundedHistory.extendByOutcome_of_support h leftLegal leftDst hleftDst]
      at hleftNext
    rw [BoundedHistory.extendByOutcome_of_support h rightLegal rightDst hrightDst]
      at hrightNext
    have hhist :
        h.snoc leftLegal leftDst hleftDst =
          h.snoc rightLegal rightDst hrightDst := by
      rw [hleftNext, hrightNext]
    have hsteps := congrArg
      (fun history : view.BoundedHistory horizon => history.steps) hhist
    simp only [BoundedHistory.steps_snoc] at hsteps
    have hstepEq :=
      (Math.TraceRun.append_singleton_inj hsteps).2
    have hlegalEq : leftLegal = rightLegal := by
      injection hstepEq
    have hjointEq :
        view.kuhnJointAction horizon h left =
          view.kuhnJointAction horizon h right :=
      congrArg Subtype.val hlegalEq
    funext player
    apply Subtype.ext
    exact congrFun hjointEq player

private theorem kuhnPureStep_update_player_nonzero_iff
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    (view.kuhnModel horizon hMenus).pureStep
        (Function.update profile player strategy) trace next ≠ 0 ↔
      strategy ((view.kuhnModel horizon hMenus).projectStates player trace) =
        profile player
          ((view.kuhnModel horizon hMenus).projectStates player trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hDet : ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  rw [ObsModelCore.pureStep_nonzero_iff_forall_player
    (O := O) hDet hsupport (Function.update profile player strategy)]
  constructor
  · intro hall
    simpa [O] using hall player
  · intro hstrategy other
    by_cases hother : other = player
    · subst hother
      simpa [O] using hstrategy
    · simp [Function.update_of_ne hother]

private theorem lastState_take_succ
    {ι σ : Type} {Obs : ι → Type}
    {Act : (i : ι) → Obs i → Type}
    (O : ObsModelCore ι σ Obs Act) {states : List σ} {index : Nat}
    (hindex : index < states.length) :
    O.lastState (states.take (index + 1)) = states[index] := by
  unfold ObsModelCore.lastState
  rw [List.getLast?_take]
  have hget : states[index]? = some states[index] :=
    List.getElem?_eq_getElem hindex
  simp [hget]

/-- At a terminal native history, every Kuhn-adapter action for that exact
reachable information state is the no-op move. -/
private theorem kuhnActionAtInfo_eq_none_of_terminal
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (hterm : view.boundedTerminal horizon h.lastState)
    (action : view.KuhnActionAtInfo horizon player info) :
    action.1 = none := by
  have hlegal : action.1 ∈ view.boundedAvailableMoves horizon h player :=
    action.2 h hinfo
  rw [mem_boundedAvailableMoves_iff] at hlegal
  cases hmove : action.1 with
  | none => rfl
  | some choice =>
      cases hterm with
      | inl hmachine =>
          have hactive := view.terminal_active_eq_empty hmachine
          simp [boundedLocallyLegalAtState, boundedActive, hmove, hactive]
            at hlegal
      | inr hcut =>
          simp [boundedLocallyLegalAtState, boundedActive,
            boundedAvailableActions, hmove, hcut] at hlegal

/-- Terminal reachable information states have a singleton adapter action
space. -/
private theorem kuhnActionAtInfo_subsingleton_of_terminal
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (hterm : view.boundedTerminal horizon h.lastState) :
    Subsingleton (view.KuhnActionAtInfo horizon player info) := by
  refine ⟨fun left right => ?_⟩
  apply Subtype.ext
  rw [view.kuhnActionAtInfo_eq_none_of_terminal horizon h hinfo hterm left,
    view.kuhnActionAtInfo_eq_none_of_terminal horizon h hinfo hterm right]

/-- A supported Kuhn-adapter step either stutters at a terminal history or
strictly advances the native history depth by one. -/
private theorem kuhnStep_support_terminal_or_depth_succ
    (view : M.RoundView) (horizon : Nat)
    (h : view.BoundedHistory horizon)
    (action : view.KuhnActionAtHistory horizon h)
    {next : view.BoundedHistory horizon}
    (hsupport : view.kuhnStep horizon h action next ≠ 0) :
    (view.boundedTerminal horizon h.lastState ∧ next = h) ∨
      (¬ view.boundedTerminal horizon h.lastState ∧
        next.lastState.depth = h.lastState.depth + 1) := by
  classical
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · left
    have hnext : next = h := by
      have hmem : next ∈ (view.kuhnStep horizon h action).support :=
        (PMF.mem_support_iff _ _).2 hsupport
      rw [view.kuhnStep_terminal horizon h action hterm,
        PMF.support_pure, Set.mem_singleton_iff] at hmem
      exact hmem
    exact ⟨hterm, hnext⟩
  · right
    rw [view.kuhnStep_nonterminal horizon h action hterm] at hsupport
    have hmem :
        next ∈
          (PMF.map
            (fun dst =>
              h.extendByOutcome
                (view.kuhnLegalAction horizon h hterm action) dst)
            (view.boundedTransition horizon h.lastState
              (view.kuhnLegalAction horizon h hterm action))).support :=
      (PMF.mem_support_iff _ _).2 hsupport
    rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
      ⟨dst, hdstMem, hnextEq⟩
    have hdst :
        view.boundedTransition horizon h.lastState
            (view.kuhnLegalAction horizon h hterm action) dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdstMem
    have hdstDepth :
        dst.depth = h.lastState.depth + 1 :=
      view.boundedTransition_support_depth horizon h.lastState
        (view.kuhnLegalAction horizon h hterm action) hdst
    subst next
    refine ⟨hterm, ?_⟩
    rw [BoundedHistory.extendByOutcome_of_support h
      (view.kuhnLegalAction horizon h hterm action) dst hdst]
    simp [hdstDepth]

/-- The same terminal-or-depth-advance property for the pure-step kernel used
by `runDistPure`. -/
private theorem kuhnPureStep_support_terminal_or_depth_succ
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    (trace : List (view.BoundedHistory horizon))
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0) :
    (view.boundedTerminal horizon
        ((view.kuhnModel horizon hMenus).lastState trace).lastState ∧
      next = (view.kuhnModel horizon hMenus).lastState trace) ∨
      (¬ view.boundedTerminal horizon
          ((view.kuhnModel horizon hMenus).lastState trace).lastState ∧
        next.lastState.depth =
          ((view.kuhnModel horizon hMenus).lastState trace).lastState.depth +
            1) := by
  classical
  let O := view.kuhnModel horizon hMenus
  change
    (O.stepDist (O.pureToBehavioral profile) trace) next ≠ 0
      at hsupport
  change
    ((O.jointActionDist (O.pureToBehavioral profile) trace).bind
      (fun action => O.step (O.lastState trace)
        (O.castJointAction trace action))) next ≠ 0 at hsupport
  have hmem :
      next ∈
        (((O.jointActionDist (O.pureToBehavioral profile) trace).bind
          (fun action => O.step (O.lastState trace)
            (O.castJointAction trace action))).support) :=
    (PMF.mem_support_iff _ _).2 hsupport
  rw [PMF.mem_support_bind_iff] at hmem
  rcases hmem with ⟨action, _haction, hnext⟩
  change
    view.kuhnStep horizon (O.lastState trace)
      (O.castJointAction trace action) next ≠ 0 at hnext
  exact
    view.kuhnStep_support_terminal_or_depth_succ horizon
      (O.lastState trace) (O.castJointAction trace action) hnext

/-- Along a supported pure adapter trace, if a later history is nonterminal
then every strictly earlier trace position has smaller native history depth. -/
private theorem kuhnTrace_depth_lt_of_later_nonterminal
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (profile : (view.kuhnModel horizon hMenus).PureProfile)
    {steps : Nat} {states : List (view.BoundedHistory horizon)}
    (hrun :
      (view.kuhnModel horizon hMenus).runDistPure steps profile states ≠ 0)
    {early late : Nat} (hearlyLate : early < late)
    (hlate : late < states.length)
    (hlateNot :
      ¬ view.boundedTerminal horizon
        (((view.kuhnModel horizon hMenus).lastState
          (states.take (late + 1))).lastState)) :
    (((view.kuhnModel horizon hMenus).lastState
        (states.take (early + 1))).lastState.depth) <
      (((view.kuhnModel horizon hMenus).lastState
        (states.take (late + 1))).lastState.depth) := by
  classical
  let O := view.kuhnModel horizon hMenus
  change O.runDistPure steps profile states ≠ 0 at hrun
  rw [O.runDistPure_eq_pureRun] at hrun
  induction late generalizing early with
  | zero =>
      omega
  | succ m ih =>
      have hmLen : m < states.length := by omega
      have hstep :
          O.pureStep profile (states.take (m + 1)) states[m + 1] ≠ 0 := by
        exact
          Math.ParameterizedChain.pureRun_step_nonzero
            O.pureStep O.init steps profile states hrun m (by omega)
      have hnextLast :
          O.lastState (states.take (m + 1 + 1)) = states[m + 1] :=
        lastState_take_succ O hlate
      have hsourceLast :
          O.lastState (states.take (m + 1)) = states[m] :=
        lastState_take_succ O hmLen
      have hnextLast' :
          (view.kuhnModel horizon hMenus).lastState
              (states.take (m + 1 + 1)) = states[m + 1] := by
        simpa [O] using hnextLast
      have hsourceLast' :
          (view.kuhnModel horizon hMenus).lastState
              (states.take (m + 1)) = states[m] := by
        simpa [O] using hsourceLast
      have hlateNot' :
          ¬ view.boundedTerminal horizon (states[m + 1]).lastState := by
        simpa [hnextLast'] using hlateNot
      have hstruct :=
        view.kuhnPureStep_support_terminal_or_depth_succ
          horizon hMenus profile (states.take (m + 1)) hstep
      rcases hstruct with hterminal | hadvance
      · rcases hterminal with ⟨hsourceTerm, hnextEq⟩
        exact False.elim (hlateNot' (by simpa [hnextEq] using hsourceTerm))
      · rcases hadvance with ⟨hsourceNot, hdepthSucc⟩
        by_cases heq : early = m
        · subst early
          have hdepthSucc' :
              states[m + 1].lastState.depth =
                states[m].lastState.depth + 1 := by
            simpa [hsourceLast'] using hdepthSucc
          rw [hsourceLast', hnextLast']
          omega
        · have hearlyM : early < m := by omega
          have hltPrev :
              (O.lastState (states.take (early + 1))).lastState.depth <
                (O.lastState (states.take (m + 1))).lastState.depth :=
            ih hearlyM hmLen hsourceNot
          have hltPrev' :
              ((view.kuhnModel horizon hMenus).lastState
                  (states.take (early + 1))).lastState.depth <
                states[m].lastState.depth := by
            simpa [O, hsourceLast'] using hltPrev
          have hdepthSucc' :
              states[m + 1].lastState.depth =
                states[m].lastState.depth + 1 := by
            simpa [hsourceLast'] using hdepthSucc
          rw [hnextLast']
          omega

/-- The native round-view Kuhn adapter cannot revisit a nontrivial
information state along a supported pure trace.  If a reachable information
state repeats, all intervening adapter steps are terminal stutters, and the
adapter action space is the singleton no-op move. -/
theorem kuhnModel_noNontrivialInfoStateRepeat
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)] :
    ObsModelCore.NoNontrivialInfoStateRepeat
      (view.kuhnModel horizon hMenus) := by
  classical
  let O := view.kuhnModel horizon hMenus
  intro player profile steps states hrun j₁ j₂ hjlt hjlen hEq
  let h₁ : view.BoundedHistory horizon :=
    O.lastState (states.take (j₁ + 1))
  let h₂ : view.BoundedHistory horizon :=
    O.lastState (states.take (j₂ + 1))
  have hinfoEq :
      view.reachableInfoStateOfHistory horizon player h₁ =
        view.reachableInfoStateOfHistory horizon player h₂ := by
    exact (view.kuhnModel_projectStates horizon hMenus player
          (List.take (j₁ + 1) states)).symm.trans
        (hEq.trans (view.kuhnModel_projectStates horizon hMenus player
          (List.take (j₂ + 1) states)))
  have hviewEq : h₁.playerView player = h₂.playerView player :=
    congrArg Subtype.val hinfoEq
  have hdepthEq : h₁.lastState.depth = h₂.lastState.depth :=
    BoundedHistory.depth_eq_of_playerView_eq
      (view := view) (horizon := horizon) h₁ h₂ player hviewEq
  by_cases hterm : view.boundedTerminal horizon h₂.lastState
  · have hsub :
        Subsingleton (view.KuhnActionAtInfo horizon player
          (view.reachableInfoStateOfHistory horizon player h₂)) :=
      view.kuhnActionAtInfo_subsingleton_of_terminal horizon h₂ rfl hterm
    simpa only [ObsModelCore.currentObs_projectStates, kuhnModel_observe]
      using hsub
  · have hlt :
        h₁.lastState.depth < h₂.lastState.depth := by
      have hraw :=
        view.kuhnTrace_depth_lt_of_later_nonterminal
          horizon hMenus profile hrun hjlt hjlen hterm
      simpa [O, h₁, h₂] using hraw
    omega

/-- Local support/perfect-recall condition needed for mixed-to-behavioral
Kuhn realization on the adapter model. It says that replacing one player's
local strategy preserves reachability of a trace according only to that
player's endpoint information state. -/
def KuhnLocality
    (view : M.RoundView) (horizon : Nat)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (hMenus : view.MenusObservable horizon) : Prop :=
  ∀ player,
    ObsModelCore.ObsLocalFeasibilityFull
      (view.kuhnModel horizon hMenus) player

/-- Information prefix obtained by consuming a visible event suffix. This is
extensionally `pref ++ events`, but its recursive shape matches
`KuhnLocalSupportReqFrom`. -/
def KuhnInfoAfter
    (view : M.RoundView) (player : Player)
    (pref events : view.InfoState player) : view.InfoState player :=
  match events with
  | [] => pref
  | event :: rest =>
      view.KuhnInfoAfter player (pref ++ [event]) rest

theorem KuhnInfoAfter_eq_append
    (view : M.RoundView) (player : Player)
    (pref events : view.InfoState player) :
    view.KuhnInfoAfter player pref events = pref ++ events := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnInfoAfter]
  | cons event rest ih =>
      simp [KuhnInfoAfter, ih, List.append_assoc]

/-- A local strategy chooses `action` at a concrete reachable information
state represented by the raw player-visible event list `info`. -/
def KuhnStrategyChoosesAt
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (info : view.InfoState player)
    (action : view.Act player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  ∀ hinfo : ∃ h : view.BoundedHistory horizon,
      h.playerView player = info,
    (strategy ⟨info, hinfo⟩).1 = some action

/-- Support requirements induced by a player-visible event suffix.

The accumulator `pref` is the information state before reading `events`.
Observation events add no strategic support requirement.  An own-action event
requires a replacement local strategy to choose that action at the preceding
reachable prefix. -/
def KuhnLocalSupportReqFrom
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  match events with
  | [] => True
  | event :: rest =>
      match event with
      | PlayerEvent.obs _ _ =>
          view.KuhnLocalSupportReqFrom horizon hMenus player
            (pref ++ [event]) rest strategy
      | PlayerEvent.act action =>
          (∀ hprefix : ∃ h : view.BoundedHistory horizon,
              h.playerView player = pref,
            (strategy ⟨pref, hprefix⟩).1 = some action) ∧
          view.KuhnLocalSupportReqFrom horizon hMenus player
            (pref ++ [event]) rest strategy

/-- A replacement local strategy supports an endpoint information state when it
agrees with every own-action event recorded in that state. -/
def KuhnLocalSupportReq
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (info : (view.kuhnModel horizon hMenus).InfoState player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) : Prop :=
  view.KuhnLocalSupportReqFrom horizon hMenus player [] info.1 strategy

theorem KuhnLocalSupportReqFrom_append_obs
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (priv : M.Obs player) (pub : M.Public)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ [PlayerEvent.obs priv pub]) strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
        events strategy := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnLocalSupportReqFrom]
  | cons event rest ih =>
      cases event <;>
        simp [KuhnLocalSupportReqFrom, ih]

theorem KuhnLocalSupportReqFrom_append_act_obs
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (action : view.Act player)
    (priv : M.Obs player) (pub : M.Public)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ [PlayerEvent.act action, PlayerEvent.obs priv pub])
        strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
          events strategy ∧
        view.KuhnStrategyChoosesAt horizon hMenus player
          (view.KuhnInfoAfter player pref events) action strategy := by
  induction events generalizing pref with
  | nil =>
      simp [KuhnLocalSupportReqFrom, KuhnInfoAfter,
        KuhnStrategyChoosesAt]
  | cons event rest ih =>
      cases event <;>
        simp [KuhnLocalSupportReqFrom, KuhnInfoAfter, ih,
          and_assoc]

theorem KuhnLocalSupportReqFrom_append_playerView
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (player : Player)
    (pref events : view.InfoState player)
    (step : view.BoundedStep horizon)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReqFrom horizon hMenus player pref
        (events ++ step.playerView player) strategy ↔
      view.KuhnLocalSupportReqFrom horizon hMenus player pref
          events strategy ∧
        match step.ownAction? player with
        | none => True
        | some action =>
            view.KuhnStrategyChoosesAt horizon hMenus player
              (view.KuhnInfoAfter player pref events) action strategy := by
  cases hact : step.ownAction? player with
  | none =>
      simp [BoundedStep.playerView, hact,
        KuhnLocalSupportReqFrom_append_obs]
  | some action =>
      simp [BoundedStep.playerView, hact,
        KuhnLocalSupportReqFrom_append_act_obs]

private theorem kuhnActionAtInfo_eq_of_base_none
    (view : M.RoundView) (horizon : Nat)
    {player : Player} {info : view.ReachableInfoState horizon player}
    (h : view.BoundedHistory horizon)
    (hinfo : view.reachableInfoStateOfHistory horizon player h = info)
    (base action : view.KuhnActionAtInfo horizon player info)
    (hbase : base.1 = none) :
    action = base := by
  apply Subtype.ext
  have hbaseLegal : none ∈ view.boundedAvailableMoves horizon h player := by
    simpa [hbase] using base.2 h hinfo
  have hactionLegal : action.1 ∈
      view.boundedAvailableMoves horizon h player :=
    action.2 h hinfo
  rw [mem_boundedAvailableMoves_iff] at hbaseLegal hactionLegal
  cases haction : action.1 with
  | none =>
      simp [hbase]
  | some choice =>
      exfalso
      have hlocal :
          view.boundedLocallyLegalAtState horizon h.lastState player
            (some choice) := by
        simpa [boundedLocallyLegalAtState, haction] using hactionLegal
      have hactive : player ∈ view.boundedActive horizon h.lastState := by
        exact hlocal.1
      exact hbaseLegal hactive

private theorem kuhnPureStep_support_req_iff
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    {next : view.BoundedHistory horizon}
    (hsupport :
      (view.kuhnModel horizon hMenus).pureStep profile trace next ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    view.KuhnLocalSupportReq horizon hMenus player
        ((view.kuhnModel horizon hMenus).projectStates player
          (trace ++ [next])) strategy ↔
      view.KuhnLocalSupportReq horizon hMenus player
          ((view.kuhnModel horizon hMenus).projectStates player trace)
          strategy ∧
        strategy
          ((view.kuhnModel horizon hMenus).projectStates player trace) =
          profile player
            ((view.kuhnModel horizon hMenus).projectStates player trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let h := O.lastState trace
  let action : view.KuhnActionAtHistory horizon h :=
    O.castJointAction trace
      (fun player => profile player (O.projectStates player trace))
  have hprefixInfo :
      O.projectStates player trace =
        view.reachableInfoStateOfHistory horizon player h := by
    simp [O, h]
  rw [ObsModelCore.pureStep_eq] at hsupport
  change view.kuhnStep horizon h action next ≠ 0 at hsupport
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · have hnext : next = h := by
      have hmem : next ∈ (view.kuhnStep horizon h action).support :=
        (PMF.mem_support_iff _ _).2 hsupport
      rw [view.kuhnStep_terminal horizon h action hterm,
        PMF.support_pure, Set.mem_singleton_iff] at hmem
      exact hmem
    subst next
    have hstrategy :
        strategy (O.projectStates player trace) =
          profile player (O.projectStates player trace) := by
      rw [hprefixInfo]
      dsimp [O, kuhnModel, ObsModelCore.currentObs]
      haveI :
          Subsingleton
            (view.KuhnActionAtInfo horizon player
              (view.reachableInfoStateOfHistory horizon player h)) :=
        view.kuhnActionAtInfo_subsingleton_of_terminal horizon h rfl hterm
      exact Subsingleton.elim _ _
    have hfinalSame :
        O.projectStates player (trace ++ [h]) =
          O.projectStates player trace := by
      have htmp :=
        view.kuhnModel_projectStates horizon hMenus player (trace ++ [h])
      rw [ObsModelCore.lastState_append_singleton] at htmp
      have htmp' :
          O.projectStates player (trace ++ [h]) =
            view.reachableInfoStateOfHistory horizon player h := by
        simpa [O] using htmp
      exact htmp'.trans hprefixInfo.symm
    rw [hfinalSame]
    constructor
    · intro hreq
      exact ⟨by
        simpa [KuhnLocalSupportReq, O, h] using hreq, hstrategy⟩
    · intro hreq
      simpa [KuhnLocalSupportReq, O, h] using hreq.1
  · rw [view.kuhnStep_nonterminal horizon h action hterm] at hsupport
    let legalAction := view.kuhnLegalAction horizon h hterm action
    have hmem :
        next ∈
          (PMF.map
            (fun dst => h.extendByOutcome legalAction dst)
            (view.boundedTransition horizon h.lastState legalAction)).support :=
      (PMF.mem_support_iff _ _).2 hsupport
    rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
      ⟨dst, hdstMem, hnextEq⟩
    have hdst :
        view.boundedTransition horizon h.lastState legalAction dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdstMem
    have hnextSnoc :
        next = h.snoc legalAction dst hdst := by
      rw [BoundedHistory.extendByOutcome_of_support h legalAction dst hdst]
        at hnextEq
      exact hnextEq.symm
    let step : view.BoundedStep horizon :=
      ⟨h.lastState, legalAction, dst, hdst⟩
    have hnextView :
        next.playerView player =
          h.playerView player ++ step.playerView player := by
      rw [hnextSnoc]
      exact BoundedHistory.playerView_snoc h player legalAction dst hdst
    have hJoint :
        view.kuhnJointAction horizon h action =
          fun player =>
            (profile player (O.projectStates player trace)).1 := by
      dsimp [action]
      exact
        view.kuhnJointAction_castJointAction horizon hMenus trace
          (fun player => profile player (O.projectStates player trace))
    have hstepOwn :
        step.ownAction? player =
          (profile player (O.projectStates player trace)).1 := by
      change legalAction.1 player =
        (profile player (O.projectStates player trace)).1
      simpa [legalAction, kuhnLegalAction] using congrFun hJoint player
    rw [hprefixInfo] at hstepOwn
    have hfinalInfo :
        O.projectStates player (trace ++ [next]) =
          view.reachableInfoStateOfHistory horizon player next := by
      have htmp :=
        view.kuhnModel_projectStates horizon hMenus player (trace ++ [next])
      rw [ObsModelCore.lastState_append_singleton] at htmp
      simpa [O] using htmp
    rw [hfinalInfo, hprefixInfo]
    simp only [KuhnLocalSupportReq,
      reachableInfoStateOfHistory_val]
    rw [hnextView]
    have happend :=
      view.KuhnLocalSupportReqFrom_append_playerView horizon hMenus player
        [] (h.playerView player) step strategy
    rw [happend]
    rw [view.KuhnInfoAfter_eq_append player [] (h.playerView player)]
    simp only [List.nil_append]
    cases hmove : (profile player
        (view.reachableInfoStateOfHistory horizon player h)).1 with
    | none =>
        have hstepNone : step.ownAction? player = none := by
          simpa [hmove] using hstepOwn
        have hstrategy :
            strategy (view.reachableInfoStateOfHistory horizon player h) =
              profile player
                (view.reachableInfoStateOfHistory horizon player h) := by
          exact
            view.kuhnActionAtInfo_eq_of_base_none horizon h rfl
              (profile player
                (view.reachableInfoStateOfHistory horizon player h))
              (strategy
                (view.reachableInfoStateOfHistory horizon player h))
              hmove
        simp only [hstepNone]
        apply and_congr_right_iff.mpr
        intro _hreq
        exact ⟨fun _ => hstrategy, fun _ => trivial⟩
    | some move =>
        have hstepSome : step.ownAction? player = some move := by
          simpa [hmove] using hstepOwn
        simp only [hstepSome]
        constructor
        · intro hreq
          refine ⟨hreq.1, ?_⟩
          apply Subtype.ext
          rw [hmove]
          exact hreq.2 ⟨h, rfl⟩
        · intro hreq
          refine ⟨hreq.1, ?_⟩
          intro hprefix
          have harg :
              (⟨h.playerView player, hprefix⟩ :
                view.ReachableInfoState horizon player) =
                view.reachableInfoStateOfHistory horizon player h := by
            apply Subtype.ext
            rfl
          have hstrategyAtVal :
              (strategy ⟨h.playerView player, hprefix⟩).1 =
                (strategy
                  (view.reachableInfoStateOfHistory horizon player h)).1 := by
            cases harg
            rfl
          rw [hstrategyAtVal]
          have hval := congrArg Subtype.val hreq.2
          rw [hmove] at hval
          exact hval

private theorem kuhnPureRun_update_support_iff_req
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (steps : Nat)
    {profile : (view.kuhnModel horizon hMenus).PureProfile}
    {trace : List (view.BoundedHistory horizon)}
    (hsupport :
      Math.ParameterizedChain.pureRun
          ((view.kuhnModel horizon hMenus).pureStep)
          ((view.kuhnModel horizon hMenus).init)
          steps profile trace ≠ 0)
    (player : Player)
    (strategy :
      (view.kuhnModel horizon hMenus).LocalStrategy player) :
    Math.ParameterizedChain.pureRun
        ((view.kuhnModel horizon hMenus).pureStep)
        ((view.kuhnModel horizon hMenus).init)
        steps (Function.update profile player strategy) trace ≠ 0 ↔
      view.KuhnLocalSupportReq horizon hMenus player
        ((view.kuhnModel horizon hMenus).projectStates player trace)
        strategy := by
  classical
  let O := view.kuhnModel horizon hMenus
  induction steps generalizing trace profile with
  | zero =>
      simp only [Math.ParameterizedChain.pureRun,
        Math.TraceRun.traceRun_zero, PMF.pure_apply] at hsupport ⊢
      have htraceRaw :
          trace = [(view.kuhnModel horizon hMenus).init] := by
        by_contra hne
        have hne' : ¬ trace = [BoundedHistory.nil view horizon] := by
          simpa [kuhnModel] using hne
        exact hsupport (by simp [hne'])
      have htrace : trace = [O.init] := by
        simpa [O] using htraceRaw
      subst htrace
      have hinfo :
          O.projectStates player [O.init] =
            view.reachableInfoStateOfHistory horizon player
              (BoundedHistory.nil view horizon) := by
        have hproject :=
          view.kuhnModel_projectStates horizon hMenus player [O.init]
        exact hproject
      rw [hinfo]
      constructor
      · intro _
        change True
        trivial
      · intro _
        simp [O, kuhnModel]
  | succ steps ih =>
      rcases List.eq_nil_or_concat trace with rfl | ⟨pref, next, rfl⟩
      · exact absurd
          (Math.ParameterizedChain.pureRun_succ_nil
            (O.pureStep) O.init steps profile) hsupport
      · simp only [List.concat_eq_append,
          Math.ParameterizedChain.pureRun_succ_append] at hsupport ⊢
        have hprefix :
            Math.ParameterizedChain.pureRun (O.pureStep) O.init
              steps profile pref ≠ 0 :=
          left_ne_zero_of_mul hsupport
        have hstep :
            O.pureStep profile pref next ≠ 0 :=
          right_ne_zero_of_mul hsupport
        have ihPrefix :=
          ih (profile := profile) hprefix
        have hstepReq :=
          view.kuhnPureStep_support_req_iff horizon hMenus
            hstep player strategy
        have hstepUpdate :=
          view.kuhnPureStep_update_player_nonzero_iff horizon hMenus
            hstep player strategy
        constructor
        · intro hrun
          have hrunPrefix :
              Math.ParameterizedChain.pureRun (O.pureStep) O.init
                steps (Function.update profile player strategy) pref ≠ 0 :=
            left_ne_zero_of_mul hrun
          have hrunStep :
              O.pureStep (Function.update profile player strategy)
                pref next ≠ 0 :=
            right_ne_zero_of_mul hrun
          exact hstepReq.mpr
            ⟨ihPrefix.mp hrunPrefix, hstepUpdate.mp hrunStep⟩
        · intro hreq
          have hparts := hstepReq.mp hreq
          have hrunPrefix :
              Math.ParameterizedChain.pureRun (O.pureStep) O.init
                steps (Function.update profile player strategy) pref ≠ 0 :=
            ihPrefix.mpr hparts.1
          have hrunStep :
              O.pureStep (Function.update profile player strategy)
                pref next ≠ 0 :=
            hstepUpdate.mpr hparts.2
          exact mul_ne_zero hrunPrefix hrunStep

def kuhnModel_localSupportSignatureFull
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (player : Player) :
    ObsModelCore.LocalSupportSignatureFull
      (view.kuhnModel horizon hMenus) player where
  Req := fun info strategy =>
    view.KuhnLocalSupportReq horizon hMenus player info strategy
  support_iff := by
    intro steps profile trace hsupport strategy
    exact
      view.kuhnPureRun_update_support_iff_req horizon hMenus
        steps hsupport player strategy

theorem kuhnModel_obsLocalFeasibilityFull
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (player : Player) :
    ObsModelCore.ObsLocalFeasibilityFull
      (view.kuhnModel horizon hMenus) player :=
  ObsModelCore.obsLocalFeasibilityFull_of_localSupportSignatureFull
    player
    (view.kuhnModel_localSupportSignatureFull horizon hMenus player)

theorem kuhnLocality
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))] :
    view.KuhnLocality horizon hMenus := by
  intro player
  exact view.kuhnModel_obsLocalFeasibilityFull horizon hMenus player

open Classical in
noncomputable instance instFintypeKuhnModelInfoState
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player] [Fintype M.State]
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player) :
    Fintype ((view.kuhnModel horizon hMenus).InfoState player) := by
  dsimp [kuhnModel, ObsModelCore.InfoState]
  exact view.instFintypeReachableInfoState horizon player

open Classical in
noncomputable instance instFintypeKuhnModelLocalStrategy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [∀ player, Fintype (Option (view.Act player))]
    (player : Player)
    [Finite ((view.kuhnModel horizon hMenus).InfoState player)] :
    Fintype ((view.kuhnModel horizon hMenus).LocalStrategy player) := by
  letI : Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    Fintype.ofFinite _
  dsimp [ObsModelCore.LocalStrategy]
  infer_instance


end RoundView

end Machine

end Vegas
