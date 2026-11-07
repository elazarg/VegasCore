/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.LastKeyTarget

/-! # The closure of the determined reveals

An event *settles* at a configuration when it is a ready reveal, or a ready
event of a defaulted owner, that may be taken before the events of a
distinguished player `who` (one of another player, or any event once `who` has
defaulted), and both its action under a reference profile and its output are
determined. The closure of a configuration completes
settling events, least first, until none is left.

The closure forgets the order in which settling events were completed: when
simultaneously ready events commute, completing a settling event first does not
change the order-free key of the closure. And under the scheduler that serves
`who` last, a profile that agrees with the reference at settling events has the
same law of the final erased key from a configuration and from its closure.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
private theorem pmf_pure_inj {α : Type} {first second : α}
    (same : PMF.pure first = PMF.pure second) : first = second := by
  have supports := congrArg PMF.support same
  simpa [PMF.support_pure] using supports

/-- The kinds of event the closure completes: reveals, and events of a
defaulted owner. -/
def ClosureKind (config : graph.Config) (event : graph.EventId) : Prop :=
  (graph.outputLayout event).IsPublication ∨
    ∃ owner, (graph.nodes event).actor = some owner ∧ owner ∈ config.defaulted

/-- A closure kind persists while defaults grow. -/
theorem ClosureKind.mono {before after : graph.Config} {event : graph.EventId}
    (kind : ClosureKind before event) (grows : before.defaulted ⊆ after.defaulted) :
    ClosureKind after event :=
  kind.imp_right fun ⟨owner, owned, inactive⟩ => ⟨owner, owned, grows inactive⟩

/-- An event settles: a ready reveal or event of a defaulted owner that may be
taken before the events of `who`, whose action under the reference and whose
output are determined. -/
def Settles (reference : graph.BehavioralProfile) (who : Player) (config : graph.Config)
    (event : graph.EventId) : Prop :=
  config.cut.Ready event ∧ ClosureKind config event ∧ Movable who config event ∧
    ∃ (action : graph.Action event) (value : (graph.outputLayout event).Value),
      actionLaw reference config event = PMF.pure action ∧
        (graph.nodes event).eval? (config.effectiveAction event action) config.store =
          some (PMF.pure value)

/-- The configuration after completing a settling event with its determined
action and output. -/
def settled {reference : graph.BehavioralProfile} {who : Player} (config : graph.Config)
    (event : graph.EventId) (settles : Settles reference who config event) : graph.Config :=
  config.complete event settles.1 settles.2.2.2.choose settles.2.2.2.choose_spec.choose

/-- The determined action and output of a settling event are the chosen ones. -/
theorem settled_eq {reference : graph.BehavioralProfile} {who : Player} {config : graph.Config}
    {event : graph.EventId} (settles : Settles reference who config event)
    {action : graph.Action event} {value : (graph.outputLayout event).Value}
    (acting : actionLaw reference config event = PMF.pure action)
    (evaluates : (graph.nodes event).eval? (config.effectiveAction event action) config.store =
      some (PMF.pure value)) :
    settled config event settles = config.complete event settles.1 action value := by
  obtain ⟨chosenActing, chosenEvaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  have actions : settles.2.2.2.choose = action :=
    pmf_pure_inj (chosenActing.symm.trans acting)
  unfold settled
  revert chosenEvaluates
  generalize settles.2.2.2.choose_spec.choose = chosenValue
  rw [actions]
  intro chosenEvaluates
  rw [evaluates] at chosenEvaluates
  rw [pmf_pure_inj (Option.some.inj chosenEvaluates)]

/-- A settling event's step is the point mass at its settled configuration. -/
theorem eventStep_settles {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} {event : graph.EventId} (settles : Settles reference who config event) :
    eventStep reference config event settles.1 = PMF.pure (settled config event settles) := by
  obtain ⟨acting, evaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  unfold eventStep
  refine (congrArg (fun law => law.bind (config.step event settles.1)) acting).trans ?_
  rw [PMF.pure_bind, config.step_eq_map_of_eval event settles.1 _ _ evaluates, PMF.pure_map]
  rfl

/-- The settled configuration is a supported step. -/
theorem settled_step {reference : graph.BehavioralProfile} {who : Player} {config : graph.Config}
    {event : graph.EventId} (settles : Settles reference who config event) :
    Config.Step config (settled config event settles) := by
  obtain ⟨acting, evaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  refine ⟨event, settles.1, settles.2.2.2.choose, ?_⟩
  rw [config.step_eq_map_of_eval event settles.1 _ _ evaluates, PMF.pure_map,
    PMF.support_pure]
  rfl

/-- Completing a settling event consumes one remaining event. -/
theorem settled_remaining {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} {event : graph.EventId} (settles : Settles reference who config event) :
    (settled config event settles).remaining + 1 = config.remaining := by
  obtain ⟨acting, evaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  refine config.remaining_step event settles.1 settles.2.2.2.choose _ ?_
  rw [config.step_eq_map_of_eval event settles.1 _ _ evaluates, PMF.pure_map,
    PMF.support_pure]
  rfl

open scoped Classical in
/-- Complete the least settling event, if any. -/
def settleStep (reference : graph.BehavioralProfile) (who : Player) (config : graph.Config) :
    graph.Config :=
  if found : (Finset.univ.filter (Settles reference who config)).Nonempty then
    settled config _ (Finset.mem_filter.mp (Finset.min'_mem _ found)).2
  else config

/-- Complete settling events, least first, for a given number of steps. -/
def closureFor (reference : graph.BehavioralProfile) (who : Player) :
    Nat → graph.Config → graph.Config
  | 0, config => config
  | fuel + 1, config => closureFor reference who fuel (settleStep reference who config)

/-- **The closure.** Complete settling events, least first, until none is left. -/
def closure (reference : graph.BehavioralProfile) (who : Player) (config : graph.Config) :
    graph.Config :=
  closureFor reference who config.remaining config

/-- Without a settling event the step does nothing. -/
theorem settleStep_of_none {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} (none : ∀ event, ¬ Settles reference who config event) :
    settleStep reference who config = config := by
  classical
  unfold settleStep
  rw [dite_eq_right]
  intro found
  obtain ⟨event, member⟩ := found
  exact none event (Finset.mem_filter.mp member).2

/-- Without a settling event the closure does nothing. -/
theorem closureFor_of_none {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} (none : ∀ event, ¬ Settles reference who config event) :
    ∀ fuel, closureFor reference who fuel config = config := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change closureFor reference who fuel (settleStep reference who config) = config
      rw [settleStep_of_none none, ih]

/-- Without a settling event the closure does nothing. -/
theorem closure_of_none {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} (none : ∀ event, ¬ Settles reference who config event) :
    closure reference who config = config :=
  closureFor_of_none none _

/-- With a settling event the step completes the least one. -/
theorem settleStep_of_settles {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} {event : graph.EventId} (settles : Settles reference who config event) :
    ∃ (least : graph.EventId) (leastSettles : Settles reference who config least),
      settleStep reference who config = settled config least leastSettles := by
  classical
  have found : (Finset.univ.filter (Settles reference who config)).Nonempty :=
    ⟨event, Finset.mem_filter.mpr ⟨Finset.mem_univ _, settles⟩⟩
  refine ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ found)).2, ?_⟩
  unfold settleStep
  rw [dite_eq_left found]

/-- With a settling event the closure is the closure after the step. -/
theorem closure_of_settles {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} {event : graph.EventId} (settles : Settles reference who config event) :
    closure reference who config = closure reference who (settleStep reference who config) := by
  obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
  have consumed := settled_remaining leastSettles
  rw [← stepEq] at consumed
  unfold closure
  obtain ⟨rest, restEq⟩ : ∃ rest, config.remaining = rest + 1 := ⟨_, consumed.symm⟩
  rw [restEq]
  change closureFor reference who rest (settleStep reference who config) = _
  rw [(by omega : (settleStep reference who config).remaining = rest)]

/-- **The closure is reached by supported steps, and nothing settles there.** -/
theorem closure_spec (reference : graph.BehavioralProfile) (who : Player) :
    ∀ (fuel : Nat) (config : graph.Config), config.remaining = fuel →
      Relation.ReflTransGen Config.Step config (closure reference who config) ∧
        ∀ event, ¬ Settles reference who (closure reference who config) event := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro config remaining
  by_cases some : ∃ event, Settles reference who config event
  · obtain ⟨event, settles⟩ := some
    obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
    have consumed := settled_remaining leastSettles
    rw [← stepEq] at consumed
    rw [closure_of_settles settles]
    obtain ⟨path, quiet⟩ := ih _ (by omega) (settleStep reference who config) rfl
    refine ⟨Relation.ReflTransGen.head ?_ path, quiet⟩
    rw [stepEq]
    exact settled_step leastSettles
  · push Not at some
    rw [closure_of_none some]
    exact ⟨.refl, some⟩

/-- The closure is reached by supported steps. -/
theorem closure_path (reference : graph.BehavioralProfile) (who : Player)
    (config : graph.Config) :
    Relation.ReflTransGen Config.Step config (closure reference who config) :=
  (closure_spec reference who _ config rfl).1

/-- Nothing settles at the closure. -/
theorem closure_quiet (reference : graph.BehavioralProfile) (who : Player)
    (config : graph.Config) :
    ∀ event, ¬ Settles reference who (closure reference who config) event :=
  (closure_spec reference who _ config rfl).2

section Keys

/-- Settling is read from the order-free key, when the reference's action laws
are. -/
theorem Settles.congr {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event)
    {left right : graph.Config} (same : runKey left = runKey right) {event : graph.EventId}
    (settles : Settles reference who left event) : Settles reference who right event := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have defaulted := defaulted_eq_of_completionOf_eq records
  obtain ⟨ready, kind, movable, action, value, acting, evaluates⟩ := settles
  refine ⟨cut ▸ ready, kind.mono (fun owner member => by rw [← defaulted]; exact member), ?_,
    action, value, (keyed same event) ▸ acting, ?_⟩
  · unfold Movable at movable ⊢
    rw [← defaulted]
    exact movable
  · have effective : left.effectiveAction event action = right.effectiveAction event action := by
      simp only [Config.effectiveAction, defaulted]
    exact (congrArg₂ (fun chosen stored => (graph.nodes event).eval? chosen stored) effective
      store).symm.trans evaluates

/-- Settling configurations with one key settle to configurations with one key. -/
theorem settled_runKey_congr {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event)
    {left right : graph.Config} (same : runKey left = runKey right)
    {leftEvent rightEvent : graph.EventId} (events : leftEvent = rightEvent)
    (leftSettles : Settles reference who left leftEvent)
    (rightSettles : Settles reference who right rightEvent) :
    runKey (settled left leftEvent leftSettles) =
      runKey (settled right rightEvent rightSettles) := by
  subst events
  obtain ⟨-, -, -, leftAction, leftValue, leftActing, leftEvaluates⟩ := id leftSettles
  obtain ⟨-, -, -, rightAction, rightValue, rightActing, rightEvaluates⟩ := id rightSettles
  rw [settled_eq leftSettles leftActing leftEvaluates,
    settled_eq rightSettles rightActing rightEvaluates]
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have defaulted := defaulted_eq_of_completionOf_eq records
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  obtain rfl : leftAction = rightAction :=
    pmf_pure_inj (leftActing.symm.trans ((keyed same leftEvent).trans rightActing))
  have effective : left.effectiveAction leftEvent leftAction =
      right.effectiveAction leftEvent leftAction := by
    simp only [Config.effectiveAction, defaulted]
  have evals := (leftEvaluates.symm.trans (congrArg₂ (fun chosen stored =>
    (graph.nodes leftEvent).eval? chosen stored) effective store)).trans rightEvaluates
  obtain rfl : leftValue = rightValue := pmf_pure_inj (Option.some.inj evals)
  exact runKey_complete_congr same leftEvent _ _ _ _

/-- The step is read from the order-free key. -/
theorem settleStep_runKey_congr {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event)
    {left right : graph.Config} (same : runKey left = runKey right) :
    runKey (settleStep reference who left) = runKey (settleStep reference who right) := by
  classical
  have sets : Finset.univ.filter (Settles reference who left) =
      Finset.univ.filter (Settles reference who right) :=
    Finset.filter_congr fun _ _ =>
      ⟨Settles.congr keyed same, Settles.congr keyed same.symm⟩
  unfold settleStep
  by_cases found : (Finset.univ.filter (Settles reference who right)).Nonempty
  · have leftFound : (Finset.univ.filter (Settles reference who left)).Nonempty :=
      sets ▸ found
    rw [dite_eq_left leftFound, dite_eq_left found]
    have least : ∀ (first second : Finset graph.EventId) (equal : first = second)
        (firstFound : first.Nonempty) (secondFound : second.Nonempty),
        first.min' firstFound = second.min' secondFound := by
      rintro first second rfl _ _
      rfl
    exact settled_runKey_congr keyed same (least _ _ sets leftFound found) _ _
  · have leftFound : ¬ (Finset.univ.filter (Settles reference who left)).Nonempty :=
      sets ▸ found
    rw [dite_eq_right leftFound, dite_eq_right found]
    exact same

/-- **The closure is read from the order-free key.** -/
theorem closure_runKey_congr {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event) :
    ∀ (fuel : Nat) (left right : graph.Config), left.remaining = fuel →
      runKey left = runKey right →
        runKey (closure reference who left) = runKey (closure reference who right) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro left right remaining same
  by_cases some : ∃ event, Settles reference who left event
  · obtain ⟨event, settles⟩ := some
    have rightSettles := Settles.congr keyed same settles
    obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
    have consumed := settled_remaining leastSettles
    rw [← stepEq] at consumed
    rw [closure_of_settles settles, closure_of_settles rightSettles]
    exact ih _ (by omega) _ _ rfl (settleStep_runKey_congr keyed same)
  · push Not at some
    have rightNone : ∀ event, ¬ Settles reference who right event :=
      fun event settles => some event (Settles.congr keyed same.symm settles)
    rw [closure_of_none some, closure_of_none rightNone]
    exact same

end Keys

section Commuting

variable {reference : graph.BehavioralProfile} {who : Player}

/-- A settling event keeps its determined action and output, and keeps
settling, after another settling event completes. -/
theorem Settles.after {config : graph.Config} {event other : graph.EventId}
    (independent : ReadyIndependent reference)
    (settles : Settles reference who config event)
    (otherSettles : Settles reference who config other) (different : event ≠ other)
    {action : graph.Action event} {value : (graph.outputLayout event).Value}
    (acting : actionLaw reference config event = PMF.pure action)
    (evaluates : (graph.nodes event).eval? (config.effectiveAction event action) config.store =
      some (PMF.pure value)) :
    ∃ after : Settles reference who (settled config other otherSettles) event,
      actionLaw reference (settled config other otherSettles) event = PMF.pure action ∧
      (graph.nodes event).eval? ((settled config other otherSettles).effectiveAction event action)
        (settled config other otherSettles).store = some (PMF.pure value) ∧
      settled (settled config other otherSettles) event after =
        (settled config other otherSettles).complete event after.1 action value := by
  have differ := independent.actorsDiffer config otherSettles.1 settles.1 (Ne.symm different)
  have afterActing : actionLaw reference (settled config other otherSettles) event =
      PMF.pure action := by
    unfold settled
    rw [independent.stable config settles.1 otherSettles.1 (Ne.symm different)]
    exact acting
  have afterEvaluates : (graph.nodes event).eval?
      ((settled config other otherSettles).effectiveAction event action)
      (settled config other otherSettles).store = some (PMF.pure value) := by
    unfold settled
    rw [effectiveAction_complete_of_actorsDiffer config otherSettles.1 differ,
      eval?_after_complete otherSettles.1 settles.1]
    exact evaluates
  have after : Settles reference who (settled config other otherSettles) event :=
    ⟨settles.1.after_complete otherSettles.1 different,
      settles.2.1.mono (config.complete_defaulted_mono other otherSettles.1 _ _),
      settles.2.2.1.imp_right fun defaulted =>
        config.complete_defaulted_mono other otherSettles.1 _ _ defaulted,
      action, value, afterActing, afterEvaluates⟩
  exact ⟨after, afterActing, afterEvaluates, settled_eq after afterActing afterEvaluates⟩

/-- **Settling events commute.** Two settling events completed in either
order give configurations with one key. -/
theorem settled_settled_runKey_comm {config : graph.Config} {left right : graph.EventId}
    (independent : ReadyIndependent reference)
    (leftSettles : Settles reference who config left)
    (rightSettles : Settles reference who config right) (different : left ≠ right)
    (leftAfter : Settles reference who (settled config right rightSettles) left)
    (rightAfter : Settles reference who (settled config left leftSettles) right) :
    runKey (settled (settled config left leftSettles) right rightAfter) =
      runKey (settled (settled config right rightSettles) left leftAfter) := by
  obtain ⟨leftActing, leftEvaluates⟩ := leftSettles.2.2.2.choose_spec.choose_spec
  obtain ⟨rightActing, rightEvaluates⟩ := rightSettles.2.2.2.choose_spec.choose_spec
  obtain ⟨_, rightActing', rightEvaluates', _⟩ :=
    Settles.after independent rightSettles leftSettles (Ne.symm different) rightActing
      rightEvaluates
  obtain ⟨_, leftActing', leftEvaluates', _⟩ :=
    Settles.after independent leftSettles rightSettles different leftActing leftEvaluates
  rw [settled_eq rightAfter rightActing' rightEvaluates',
    settled_eq leftAfter leftActing' leftEvaluates']
  have differ := independent.actorsDiffer config leftSettles.1 rightSettles.1 different
  unfold settled
  simp only [runKey]
  refine Prod.ext ?_ ?_
  · ext member
    simp only [Config.complete_cut, EventOrder.Cut.mem_complete]
    tauto
  · exact storeRecall_complete_comm config leftSettles.1 rightSettles.1 different differ _ _ _ _

/-- **The closure forgets the order of settling.** Completing a settling event
first does not change the key of the closure. -/
theorem closure_settled_runKey (independent : ReadyIndependent reference) :
    ∀ (fuel : Nat) (config : graph.Config), config.remaining = fuel →
      ∀ (event : graph.EventId) (settles : Settles reference who config event),
        runKey (closure reference who (settled config event settles)) =
          runKey (closure reference who config) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro config remaining event settles
  obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
  rw [closure_of_settles settles, stepEq]
  by_cases same : event = least
  · subst same
    rfl
  obtain ⟨leastActing, leastEvaluates⟩ := leastSettles.2.2.2.choose_spec.choose_spec
  obtain ⟨eventActing, eventEvaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  obtain ⟨leastAfter, -, -, -⟩ :=
    Settles.after independent leastSettles settles (Ne.symm same) leastActing leastEvaluates
  obtain ⟨eventAfter, -, -, -⟩ :=
    Settles.after independent settles leastSettles same eventActing eventEvaluates
  have eventConsumed := settled_remaining settles
  have leastConsumed := settled_remaining leastSettles
  have viaEvent := ih _ (by omega) (settled config event settles) rfl least leastAfter
  have viaLeast := ih _ (by omega) (settled config least leastSettles) rfl event eventAfter
  rw [← viaEvent, ← viaLeast]
  have afterRemaining := settled_remaining leastAfter
  exact closure_runKey_congr independent.congr _ _ _ rfl
    (settled_settled_runKey_comm independent settles leastSettles same eventAfter leastAfter)

end Commuting

section Law

/-- **The closure keeps the last-served law.** A profile that is ready
independent away from `who` and agrees with the reference at settling events
has the same last-served erased-key law at a configuration and at its closure. -/
theorem lastErasedLaw_closure {reference profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who)
    (agree : ∀ config event, Settles reference who config event →
      actionLaw profile config event = actionLaw reference config event) :
    ∀ (fuel : Nat) (config : graph.Config), config.remaining = fuel →
      lastErasedLaw profile who (closure reference who config) =
        lastErasedLaw profile who config := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro config remaining
  by_cases some : ∃ event, Settles reference who config event
  · obtain ⟨event, settles⟩ := some
    obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
    have consumed := settled_remaining leastSettles
    rw [closure_of_settles settles, stepEq, ih _ (by omega) _ rfl]
    apply lastErasedLaw_eq_of_lastLaw_eq
    have taken := independent.eventStep_bind_lastLaw config.remaining config rfl least
      leastSettles.1 leastSettles.2.2.1
    have stepped : eventStep profile config least leastSettles.1 =
        PMF.pure (settled config least leastSettles) := by
      unfold eventStep
      rw [agree config least leastSettles]
      exact eventStep_settles leastSettles
    rw [stepped, PMF.pure_bind] at taken
    exact taken
  · push Not at some
    rw [closure_of_none some]

end Law

section Deterministic

omit [DecidableEq Player] in
private theorem pmf_eq_pure_of_support {α : Type} (law : PMF α) (value : α)
    (only : ∀ other ∈ law.support, other = value) : law = PMF.pure value := by
  have support : law.support = {value} := by
    ext other
    constructor
    · intro member
      exact only other member
    · intro same
      rw [Set.mem_singleton_iff] at same
      subst same
      obtain ⟨anchor, anchored⟩ := law.support_nonempty
      rwa [only anchor anchored] at anchored
  ext other
  by_cases same : other = value
  · subst same
    rw [PMF.pure_apply_self, (PMF.apply_eq_one_iff law other).mpr support]
  · rw [PMF.pure_apply_of_ne _ _ same, (PMF.apply_eq_zero_iff law other).mpr (by
      rw [support]
      exact same)]

/-- A step that is the point mass at one completion has that completion's
output as its evaluated output. -/
theorem eval_eq_of_step {config : graph.Config} {event : graph.EventId}
    {ready : config.cut.Ready event} {action : graph.Action event}
    {value : (graph.outputLayout event).Value}
    (stepped : config.step event ready action =
      PMF.pure (config.complete event ready action value)) :
    (graph.nodes event).eval? (config.effectiveAction event action) config.store =
      some (PMF.pure value) := by
  have available := EventCode.eval?_isSome_of_reads (graph.nodes event)
    (config.effectiveAction event action) config.store
    (fun _ read => config.read_available ready read)
  unfold Config.step at stepped
  rw [← Option.some_get available]
  congr 1
  apply pmf_eq_pure_of_support
  intro other member
  have mapped : config.complete event ready action other ∈
      (PMF.pure (config.complete event ready action value)).support := by
    rw [← stepped, PMF.support_map]
    exact ⟨other, member, rfl⟩
  have same := congrArg (fun next : graph.Config => next.outputs event)
    ((PMF.mem_support_pure_iff _ _).mp mapped)
  simp only [Config.complete_output_same] at same
  exact Option.some.inj same

/-- A ready movable reveal whose action under the reference is determined and
whose step is the point mass at one completion settles. -/
theorem Settles.of_step {reference : graph.BehavioralProfile} {who : Player}
    {config : graph.Config} {event : graph.EventId} (ready : config.cut.Ready event)
    (kind : ClosureKind config event) (movable : Movable who config event)
    {action : graph.Action event} {value : (graph.outputLayout event).Value}
    (acting : actionLaw reference config event = PMF.pure action)
    (stepped : config.step event ready action =
      PMF.pure (config.complete event ready action value)) :
    Settles reference who config event :=
  ⟨ready, kind, movable, action, value, acting, eval_eq_of_step stepped⟩

end Deterministic

section Absorbing

variable {reference : graph.BehavioralProfile} {who : Player}

/-- A settling event keeps its determined action and output, and keeps
settling, after any other ready event completes. -/
theorem Settles.after_complete {config : graph.Config} {event other : graph.EventId}
    (independent : ReadyIndependent reference)
    (settles : Settles reference who config event) (otherReady : config.cut.Ready other)
    (different : event ≠ other) (otherAction : graph.Action other)
    (otherValue : (graph.outputLayout other).Value)
    {action : graph.Action event} {value : (graph.outputLayout event).Value}
    (acting : actionLaw reference config event = PMF.pure action)
    (evaluates : (graph.nodes event).eval? (config.effectiveAction event action) config.store =
      some (PMF.pure value)) :
    ∃ after : Settles reference who (config.complete other otherReady otherAction otherValue)
        event,
      settled (config.complete other otherReady otherAction otherValue) event after =
        (config.complete other otherReady otherAction otherValue).complete event after.1
          action value := by
  have differ := independent.actorsDiffer config otherReady settles.1 (Ne.symm different)
  have afterActing : actionLaw reference (config.complete other otherReady otherAction otherValue)
      event = PMF.pure action := by
    rw [independent.stable config settles.1 otherReady (Ne.symm different)]
    exact acting
  have afterEvaluates : (graph.nodes event).eval?
      ((config.complete other otherReady otherAction otherValue).effectiveAction event action)
      (config.complete other otherReady otherAction otherValue).store =
        some (PMF.pure value) := by
    rw [effectiveAction_complete_of_actorsDiffer config otherReady differ,
      eval?_after_complete otherReady settles.1]
    exact evaluates
  have after : Settles reference who (config.complete other otherReady otherAction otherValue)
      event :=
    ⟨settles.1.after_complete otherReady different,
      settles.2.1.mono (config.complete_defaulted_mono other otherReady _ _),
      settles.2.2.1.imp_right fun defaulted =>
        config.complete_defaulted_mono other otherReady _ _ defaulted,
      action, value, afterActing, afterEvaluates⟩
  exact ⟨after, settled_eq after afterActing afterEvaluates⟩

/-- **The closure absorbs a step of the distinguished player.** While `who`
has not defaulted, completing a ready event of `who` before or after the
closure gives closures with one key. -/
theorem closure_complete_runKey (independent : ReadyIndependent reference) :
    ∀ (fuel : Nat) (config : graph.Config), config.remaining = fuel →
      ∀ (event : graph.EventId) (ready : config.cut.Ready event)
        (_owned : graph.actor? event = some who) (_active : who ∉ config.defaulted)
        (action : graph.Action event) (value : (graph.outputLayout event).Value)
        (readyAfter : (closure reference who config).cut.Ready event),
        runKey (closure reference who (config.complete event ready action value)) =
          runKey (closure reference who
            ((closure reference who config).complete event readyAfter action value)) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro config remaining event ready owned active action value readyAfter
  by_cases some : ∃ least, Settles reference who config least
  swap
  · push Not at some
    have same : closure reference who config = config := closure_of_none some
    have generalized : ∀ (closed : graph.Config) (equal : closed = config)
        (closedReady : closed.cut.Ready event),
        runKey (closure reference who (config.complete event ready action value)) =
          runKey (closure reference who (closed.complete event closedReady action value)) := by
      rintro closed rfl closedReady
      rfl
    exact generalized _ same readyAfter
  obtain ⟨anyEvent, anySettles⟩ := some
  obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles anySettles
  have consumed := settled_remaining leastSettles
  have different : least ≠ event := by
    intro same
    subst same
    rcases leastSettles.2.2.1 with foreign | defaulted
    · exact foreign owned
    · exact active defaulted
  obtain ⟨leastActing, leastEvaluates⟩ := leastSettles.2.2.2.choose_spec.choose_spec
  have closureEq : closure reference who config =
      closure reference who (settled config least leastSettles) := by
    rw [closure_of_settles anySettles, stepEq]
  have nextReady : (settled config least leastSettles).cut.Ready event :=
    ready.after_complete leastSettles.1 (Ne.symm different)
  have nextActive : who ∉ (settled config least leastSettles).defaulted := by
    unfold settled
    rw [mem_defaulted_complete_of_actor_ne config least leastSettles.1 _ _ who
      (fun leastOwned => by
        rcases leastSettles.2.2.1 with foreign | defaulted
        · exact foreign leastOwned
        · exact active defaulted)]
    exact active
  have readyAfter' : (closure reference who (settled config least leastSettles)).cut.Ready
      event := closureEq ▸ readyAfter
  have inner := ih _ (by omega) (settled config least leastSettles) rfl event nextReady owned
    nextActive action value readyAfter'
  have rightEq : runKey (closure reference who
      ((closure reference who config).complete event readyAfter action value)) =
      runKey (closure reference who ((closure reference who
        (settled config least leastSettles)).complete event readyAfter' action value)) := by
    have generalized : ∀ (first second : graph.Config) (equal : first = second)
        (firstReady : first.cut.Ready event) (secondReady : second.cut.Ready event),
        runKey (closure reference who (first.complete event firstReady action value)) =
          runKey (closure reference who (second.complete event secondReady action value)) := by
      rintro first second rfl _ _
      rfl
    exact generalized _ _ closureEq _ _
  rw [rightEq, ← inner]
  obtain ⟨leastAfter, leastAfterEq⟩ := Settles.after_complete independent leastSettles ready
    different action value leastActing leastEvaluates
  have absorbed := closure_settled_runKey independent _
    (config.complete event ready action value) rfl least leastAfter
  rw [← absorbed]
  apply closure_runKey_congr independent.congr _ _ _ rfl
  rw [leastAfterEq]
  have differ := independent.actorsDiffer config leastSettles.1 ready different
  have generalized : ∀ (first : graph.Config)
      (equal : first = config.complete least leastSettles.1 leastSettles.2.2.2.choose
        leastSettles.2.2.2.choose_spec.choose) (firstReady : first.cut.Ready event),
      runKey ((config.complete event ready action value).complete least leastAfter.1
          leastSettles.2.2.2.choose leastSettles.2.2.2.choose_spec.choose) =
        runKey (first.complete event firstReady action value) := by
    rintro first rfl firstReady
    simp only [runKey]
    refine Prod.ext ?_ ?_
    · ext member
      simp only [Config.complete_cut, EventOrder.Cut.mem_complete]
      tauto
    · exact (storeRecall_complete_comm config leastSettles.1 ready different differ _ _ _ _).symm
  exact generalized _ (settled_eq leastSettles leastActing leastEvaluates) nextReady

end Absorbing

section Shape

variable {reference : graph.BehavioralProfile} {who : Player}

/-- A ready event of a defaulted owner settles under every reference. -/
theorem settles_of_defaulted {config : graph.Config} {event : graph.EventId}
    (ready : config.cut.Ready event) {owner : Player}
    (owned : (graph.nodes event).actor = some owner)
    (inactive : owner ∈ config.defaulted) : Settles reference who config event := by
  have movable : Movable who config event := by
    by_cases same : owner = who
    · subst same
      exact Or.inr inactive
    · exact Or.inl fun ownedWho => same (Option.some.inj (owned.symm.trans ownedWho))
  have effective : config.effectiveAction event ((graph.nodes event).failureAction owner owned) =
      (graph.nodes event).failureAction owner owned :=
    EventCode.effectiveAction_of_defaulted _ _ owner owned inactive _
  obtain ⟨value, evaluates, _⟩ := EventCode.failureAction_eval? (graph.nodes event) owner owned
    config.store (fun _ read => config.read_available ready read)
  refine ⟨ready, Or.inr ⟨owner, owned, inactive⟩, movable,
    (graph.nodes event).failureAction owner owned, value, ?_, ?_⟩
  · rw [actionLaw_of_actor reference config owned, dite_eq_left inactive]
  · rw [effective]
    exact evaluates

/-- A settled event is of a closure kind and of another player than `who`, or
`who` has defaulted; and completing it keeps `who` active if `who` was. -/
theorem settled_shape {config : graph.Config} {event : graph.EventId}
    (settles : Settles reference who config event) :
    ClosureKind config event ∧
      (who ∉ config.defaulted → graph.actor? event ≠ some who ∧
        who ∉ (settled config event settles).defaulted) := by
  refine ⟨settles.2.1, fun active => ?_⟩
  have foreign : graph.actor? event ≠ some who := by
    rcases settles.2.2.1 with foreign | defaulted
    · exact foreign
    · exact (active defaulted).elim
  refine ⟨foreign, ?_⟩
  unfold settled
  rw [mem_defaulted_complete_of_actor_ne config event settles.1 _ _ who foreign]
  exact active

/-- **What the closure adds.** Every event the closure completes is a reveal or
an event of an owner defaulted at the closure; while `who` is active, it is not
an event of `who`, and `who` stays active. -/
theorem closure_shape (reference : graph.BehavioralProfile) (who : Player) :
    ∀ (fuel : Nat) (config : graph.Config), config.remaining = fuel →
      (∀ event, event ∈ (closure reference who config).cut.completed →
        event ∉ config.cut.completed → ClosureKind (closure reference who config) event ∧
          (who ∉ config.defaulted → graph.actor? event ≠ some who)) ∧
      (who ∉ config.defaulted → who ∉ (closure reference who config).defaulted) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro config remaining
  by_cases some : ∃ event, Settles reference who config event
  · obtain ⟨event, settles⟩ := some
    obtain ⟨least, leastSettles, stepEq⟩ := settleStep_of_settles settles
    have consumed := settled_remaining leastSettles
    rw [closure_of_settles settles, stepEq]
    obtain ⟨added, stays⟩ := ih _ (by omega) (settled config least leastSettles) rfl
    obtain ⟨kind, shape⟩ := settled_shape leastSettles
    have grows : (settled config least leastSettles).defaulted ⊆
        (closure reference who (settled config least leastSettles)).defaulted :=
      Config.Step.path_defaulted_mono (closure_path reference who _)
    refine ⟨fun query done fresh => ?_, fun active => stays (shape active).2⟩
    by_cases same : query = least
    · rw [same]
      exact ⟨kind.mono fun _ member =>
        grows (config.complete_defaulted_mono least leastSettles.1 _ _ member),
        fun active => (shape active).1⟩
    · have notBefore : query ∉ (settled config least leastSettles).cut.completed := by
        unfold settled
        rw [Config.complete_cut, EventOrder.Cut.mem_complete]
        rintro (equal | old)
        · exact same equal
        · exact fresh old
      obtain ⟨queryPublication, queryShape⟩ := added query done notBefore
      exact ⟨queryPublication, fun active => queryShape (shape active).2⟩
  · push Not at some
    rw [closure_of_none some]
    exact ⟨fun _ done fresh => (fresh done).elim, id⟩

end Shape

section Steps

variable {reference : graph.BehavioralProfile} {who : Player}

/-- Completing an event depends on the requested action only through the
recorded decision. -/
theorem Config.complete_congr_decision (config : graph.Config) {event : graph.EventId}
    (ready : config.cut.Ready event) {first second : graph.Action event}
    (decisions : config.actualDecision event first = config.actualDecision event second)
    (value : (graph.outputLayout event).Value) :
    config.complete event ready first value = config.complete event ready second value := by
  unfold Config.complete
  simp only [decisions]

omit [DecidableEq Player] in
private theorem effectiveAction_of_active [DecidableEq Player] {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (defaulted : Finset Player) (owner : Player)
    (owned : code.actor = some owner) (active : owner ∉ defaulted) (requested : code.Action) :
    code.effectiveAction defaulted requested = requested ∧
      code.actualDecision defaulted requested = some requested := by
  cases code with
  | bind who payload =>
      have same : who = owner := Option.some.inj owned
      subst who
      simp [EventCode.effectiveAction, EventCode.actualDecision, EventCode.actor, active]
  | resolve who payload binding checks =>
      have same : who = owner := Option.some.inj owned
      subst who
      simp [EventCode.effectiveAction, EventCode.actualDecision, EventCode.actor, active]
  | sample => simp [EventCode.actor] at owned

/-- **A step recording the determined decision of an owned settling event is
its settling.** -/
theorem step_eq_settled {config next : graph.Config} {event : graph.EventId}
    (settles : Settles reference who config event) {owner : Player}
    (owned : (graph.nodes event).actor = some owner) {ready : config.cut.Ready event}
    {action : graph.Action event} (member : next ∈ (config.step event ready action).support)
    (decisions : config.actualDecision event action =
      config.actualDecision event settles.2.2.2.choose) :
    next = settled config event settles := by
  obtain ⟨acting, evaluates⟩ := settles.2.2.2.choose_spec.choose_spec
  have effective : config.effectiveAction event action =
      config.effectiveAction event settles.2.2.2.choose := by
    unfold Config.effectiveAction
    by_cases inactive : owner ∈ config.defaulted
    · rw [EventCode.effectiveAction_of_defaulted _ _ owner owned inactive,
        EventCode.effectiveAction_of_defaulted _ _ owner owned inactive]
    · obtain ⟨actionEffective, actionDecision⟩ :=
        effectiveAction_of_active _ config.defaulted owner owned inactive action
      obtain ⟨chosenEffective, chosenDecision⟩ :=
        effectiveAction_of_active _ config.defaulted owner owned inactive settles.2.2.2.choose
      unfold Config.actualDecision at decisions
      rw [actionDecision, chosenDecision] at decisions
      rw [actionEffective, chosenEffective, Option.some.inj decisions]
  have stepEq := config.step_eq_map_of_eval event ready action _
    ((congrArg (fun chosen => (graph.nodes event).eval? chosen config.store) effective).trans
      evaluates)
  rw [stepEq, PMF.pure_map, PMF.mem_support_pure_iff] at member
  rw [member]
  unfold settled
  exact config.complete_congr_decision ready decisions _

end Steps

end Vegas.EventGraph
