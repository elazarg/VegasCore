module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.LastScheduler
public import Vegas.EventGraph.SchedulerErasure
public import Vegas.EventGraph.RevealRelaxedScheduling

@[expose] public section

/-! # Taking other players' events early under the last scheduler

Under the scheduler that serves one player last, that player acts only when
every enabled event is its own. So when the other players' simultaneously ready
events commute, and that player's action laws are fixed once it has defaulted,
any ready event of another player or of chance (or any event once the player
has defaulted) may be taken first without changing the law of the final key.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- An event that may be taken out of the last scheduler's order: one not owned
by `who`, or any event once `who` has defaulted. -/
def Movable (who : Player) (config : graph.Config) (event : graph.EventId) : Prop :=
  graph.actor? event ≠ some who ∨ who ∈ config.defaulted

/-- **Ready independence away from one player.** Simultaneously ready events
have different actors; completing one leaves the action law of a movable event
unchanged; and every action law is read from the order-free key. -/
structure LastIndependent (profile : graph.BehavioralProfile) (who : Player) : Prop where
  actorsDiffer : ∀ (config : graph.Config) {left right : graph.EventId},
    config.cut.Ready left → config.cut.Ready right → left ≠ right →
      graph.ActorsDiffer left right
  stable : ∀ (config : graph.Config) {event other : graph.EventId},
    config.cut.Ready event → ∀ (otherReady : config.cut.Ready other), other ≠ event →
      Movable who config event →
      ∀ (action : graph.Action other) (value : (graph.outputLayout other).Value),
        actionLaw profile (config.complete other otherReady action value) event =
          actionLaw profile config event
  congr : ∀ {left right : graph.Config}, runKey left = runKey right →
    ∀ event, actionLaw profile left event = actionLaw profile right event

/-- The law of the final key when `who` is served last. -/
def lastLaw (profile : graph.BehavioralProfile) (who : Player) (config : graph.Config) :=
  (graph.runPlan (graph.policyPlan profile (graph.lastScheduler who)) config.remaining
    config).map runKey

omit [DecidableEq Player] in
private theorem not_terminal_of_ready {config : graph.Config} {event : graph.EventId}
    (ready : config.cut.Ready event) : ¬ config.cut.Terminal := by
  intro terminal
  apply ready.1
  rw [terminal]
  exact Finset.mem_univ _

/-- The last scheduler's law takes its picked event first. -/
theorem lastLaw_step (profile : graph.BehavioralProfile) (who : Player) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) (event : graph.EventId) (ready : config.cut.Ready event)
    (picked : event = graph.lastPick who config.cut.enabled
      (enabled_nonempty_of_not_terminal config notTerminal)) :
    lastLaw profile who config =
      (eventStep profile config event ready).bind (lastLaw profile who) := by
  obtain ⟨rest, restEq⟩ : ∃ rest, config.remaining = rest + 1 := by
    have positive : config.remaining ≠ 0 :=
      fun zero => notTerminal ((config.terminal_iff_remaining_zero).mpr zero)
    exact ⟨config.remaining - 1, by omega⟩
  unfold lastLaw
  rw [restEq, runPlan_policyPlan_succ profile _ rest config notTerminal]
  simp only [EventGraph.lastScheduler, PMF.pure_bind]
  rw [eventStep_congr_event profile config picked.symm _ ready, PMF.map_bind]
  apply bind_congr_on_support _
  intro next member
  have consumed : next.remaining + 1 = config.remaining := by
    unfold eventStep at member
    rw [PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepped⟩ := member
    exact config.remaining_step event ready action next stepped
  rw [(by omega : next.remaining = rest)]

/-- **The last law is read from the order-free key.** -/
theorem LastIndependent.lastLaw_congr {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) :
    ∀ fuel (left right : graph.Config), left.remaining = fuel → runKey left = runKey right →
      lastLaw profile who left = lastLaw profile who right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right remaining same
      have rightRemaining := (remaining_eq_of_runKey_eq same).symm.trans remaining
      unfold lastLaw
      rw [remaining, rightRemaining]
      simp only [EventGraph.runPlan, PMF.pure_map, same]
  | succ fuel ih =>
      intro left right remaining same
      have cut : left.cut = right.cut := congrArg Prod.fst same
      have notTerminal : ¬ left.cut.Terminal := fun terminal => by
        have := (left.terminal_iff_remaining_zero).mp terminal
        omega
      have rightNotTerminal : ¬ right.cut.Terminal := by rw [← cut]; exact notTerminal
      let event := graph.lastPick who left.cut.enabled
        (enabled_nonempty_of_not_terminal left notTerminal)
      have ready : left.cut.Ready event :=
        (EventOrder.Cut.mem_enabled _ _).mp (graph.lastPick_mem who _ _)
      have rightReady : right.cut.Ready event := by rw [← cut]; exact ready
      have rightPicked : event = graph.lastPick who right.cut.enabled
          (enabled_nonempty_of_not_terminal right rightNotTerminal) :=
        graph.lastPick_congr who (congrArg EventOrder.Cut.enabled cut) _ _
      rw [lastLaw_step profile who left notTerminal event ready rfl,
        lastLaw_step profile who right rightNotTerminal event rightReady rightPicked]
      unfold eventStep
      rw [independent.congr same event, PMF.bind_bind, PMF.bind_bind]
      apply bind_congr_on_support _
      intro action _
      have carried (config : graph.Config) (configReady : config.cut.Ready event)
          (configRemaining : config.remaining = fuel + 1) :
          (config.step event configReady action).support ⊆
            {next | next.remaining = fuel} := by
        intro next member
        have := config.remaining_step event configReady action next member
        simp only [Set.mem_ofPred_eq]
        omega
      exact bind_eq_of_map_key_eq runKey {next | next.remaining = fuel} _ _
        (carried left ready remaining)
        (carried right rightReady ((remaining_eq_of_runKey_eq same).symm.trans remaining))
        (step_map_runKey_congr same event ready rightReady action) _
        (fun a aRemaining b _ keys => ih a b aRemaining keys)

/-- A movable event stays movable after a step. -/
private theorem Movable.step {who : Player} {config next : graph.Config}
    {event first : graph.EventId} (movable : Movable who config event)
    (firstReady : config.cut.Ready first) (action : graph.Action first)
    (member : next ∈ (config.step first firstReady action).support) :
    Movable who next event :=
  movable.imp_right fun defaulted =>
    config.defaulted_step first firstReady action next member defaulted

/-- **A movable event may be taken first.** Completing a ready movable event
and then continuing with `who` served last is the law of serving `who` last. -/
theorem LastIndependent.eventStep_bind_lastLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      ∀ event (ready : config.cut.Ready event), Movable who config event →
        (eventStep profile config event ready).bind (lastLaw profile who) =
          lastLaw profile who config := by
  intro fuel
  induction fuel with
  | zero =>
      intro config remaining event ready _
      exact absurd ((config.terminal_iff_remaining_zero).mpr remaining)
        (not_terminal_of_ready ready)
  | succ fuel ih =>
      intro config remaining event ready movable
      have notTerminal := not_terminal_of_ready ready
      let picked := graph.lastPick who config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal)
      have pickedReady : config.cut.Ready picked :=
        (EventOrder.Cut.mem_enabled _ _).mp (graph.lastPick_mem who _ _)
      have pickedMovable : Movable who config picked := by
        rcases movable with foreign | defaulted
        · exact Or.inl (graph.lastPick_other who _ ((EventOrder.Cut.mem_enabled _ _).mpr ready)
            foreign)
        · exact Or.inr defaulted
      rw [lastLaw_step profile who config notTerminal picked pickedReady rfl]
      by_cases same : event = picked
      · exact congrArg (fun law => law.bind (lastLaw profile who))
          (eventStep_congr_event profile config same ready pickedReady)
      -- Each order expands into both action laws and the two fixed steps.
      have expand (first second : graph.EventId) (firstReady : config.cut.Ready first)
          (secondReady : config.cut.Ready second) (different : first ≠ second)
          (secondMovable : Movable who config second) :
          (eventStep profile config first firstReady).bind (lastLaw profile who) =
            (actionLaw profile config first).bind fun firstAction =>
              (actionLaw profile config second).bind fun secondAction =>
                (stepThen config first second firstReady secondReady different firstAction
                  secondAction).bind (lastLaw profile who) := by
        unfold eventStep
        rw [PMF.bind_bind]
        apply bind_congr_on_support _
        intro firstAction _
        simp only [stepThen_bind]
        rw [PMF.bind_comm]
        apply bind_congr_on_support _
        intro next member
        have nextRemaining : next.remaining = fuel := by
          have := config.remaining_step first firstReady firstAction next member
          omega
        have nextReady : next.cut.Ready second := by
          rw [config.step_cut first firstReady firstAction next member]
          exact secondReady.after_complete firstReady different.symm
        rw [← ih next nextRemaining second nextReady
          (secondMovable.step firstReady firstAction member)]
        simp only [dite_eq_left nextReady]
        unfold eventStep
        rw [PMF.bind_bind]
        rw [Config.step, PMF.support_map] at member
        obtain ⟨value, _, rfl⟩ := member
        rw [independent.stable config secondReady firstReady different secondMovable firstAction
          value]
      rw [expand event picked ready pickedReady same pickedMovable,
        expand picked event pickedReady ready (Ne.symm same) movable, PMF.bind_comm]
      apply bind_congr_on_support _
      intro pickedAction _
      apply bind_congr_on_support _
      intro eventAction _
      exact bind_eq_of_map_key_eq runKey Set.univ _ _ (Set.subset_univ _) (Set.subset_univ _)
        (stepThen_map_runKey_comm config ready pickedReady same
          (independent.actorsDiffer config ready pickedReady same) eventAction pickedAction) _
        (fun a _ b _ keys => independent.lastLaw_congr _ a b rfl keys)

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- **Ready independence away from one player on reveal-only concurrency.** The
normalization of a profile whose other players ignore the observation at
publications is ready independent away from that player. -/
theorem RevealsOnlyConcurrent.lastIndependent_normalizeProfile
    (only : graph.RevealsOnlyConcurrent) (profile : graph.BehavioralProfile) (who : Player)
    (oblivious : ∀ owner, owner ≠ who → ∀ event (actor : graph.actor? event = some owner),
      (graph.outputLayout event).IsPublication →
        ∀ (left right : graph.PlayerObservation owner) leftActive rightActive,
          profile owner event actor left leftActive = profile owner event actor right rightActive) :
    LastIndependent (graph.normalizeProfile profile) who where
  actorsDiffer config left right leftReady rightReady different := by
    rcases only config.cut leftReady rightReady different with independent | independent
    · exact independent.actorsDiffer
    · exact independent.actorsDiffer.symm
  stable config event other eventReady otherReady different movable action value := by
    have independent : graph.IndependentReveals other event ∨
        graph.IndependentReveals event other :=
      only config.cut otherReady eventReady different
    have publication : (graph.outputLayout event).IsPublication := by
      rcases independent with independent | independent
      · exact independent.2.1
      · exact independent.1
    have actorsNe : graph.actor? other ≠ graph.actor? event := by
      rcases independent with independent | independent
      · exact independent.2.2.2
      · exact Ne.symm independent.2.2.2
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
          owner (fun otherActor => actorsNe (otherActor.trans ownerEq.symm))
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
        · rw [dite_eq_right (fun active => inactive (member.mp active)),
            dite_eq_right inactive]
          have ownerNe : owner ≠ who := by
            rintro rfl
            rcases movable with foreign | defaulted
            · exact foreign ownerEq
            · exact inactive defaulted
          exact oblivious owner ownerNe event ownerEq publication _ _ _ _
  congr {left right} same event := by
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaulted := defaulted_eq_of_completionOf_eq records
    cases ownerEq : (graph.nodes event).actor with
    | none =>
        rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
        by_cases inactive : owner ∈ left.defaulted
        · rw [dite_eq_left inactive, dite_eq_left (defaulted ▸ inactive)]
        · rw [dite_eq_right inactive, dite_eq_right (defaulted ▸ inactive)]
          exact policy_congr _ event ownerEq
            (graph.normalizeObservation_playerObserve_congr owner (congrArg Prod.snd same)) _ _

end Vegas.EventGraph
