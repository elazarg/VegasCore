module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.NormalizedPolicy
public import Vegas.EventGraph.ActorTurns

@[expose] public section

/-! # Erasing public scheduling choices

A profile is ready independent when simultaneously ready events have different
actors, completing one of them leaves the other's action law unchanged, and
every action law is read from the cut, the store and the completion recorded
for each event. For such a profile the scheduler is invisible: under every
public scheduler the law of the final store and completion records is the
canonical one. The completion order itself is not part of that law.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Two laws with the same image under a key agree under every continuation that
depends only on the key on a set carrying both laws. -/
theorem bind_eq_of_map_key_eq {α β γ : Type} (key : α → β) (carrier : Set α) (left right : PMF α)
    (leftCarried : left.support ⊆ carrier) (rightCarried : right.support ⊆ carrier)
    (same : left.map key = right.map key) (continuation : α → PMF γ)
    (congr : ∀ a ∈ carrier, ∀ b ∈ carrier, key a = key b → continuation a = continuation b) :
    left.bind continuation = right.bind continuation := by
  classical
  let through : β → PMF γ := fun image =>
    if found : ∃ a ∈ carrier, key a = image then continuation found.choose
    else left.bind continuation
  have factors (law : PMF α) (carried : law.support ⊆ carrier) :
      law.bind continuation = (law.map key).bind through := by
    rw [PMF.bind_map]
    apply bind_congr_on_support _
    intro a supported
    have found : ∃ b ∈ carrier, key b = key a := ⟨a, carried supported, rfl⟩
    simp only [Function.comp_apply, through, dite_eq_left found]
    exact (congr _ found.choose_spec.1 a (carried supported) found.choose_spec.2).symm
  rw [factors left leftCarried, factors right rightCarried, same]

/-- The order-free state of a run: the cut, the store and each event's completion record. -/
def runKey (config : graph.Config) := (config.cut, graph.storeRecall config)

omit [DecidableEq Player] in
/-- A completion is an event's record exactly when it lies in the history with that event. -/
theorem completionOf_eq_some_iff (config : graph.Config) (event : graph.EventId)
    (completion : graph.Completion) :
    completionOf config event = some completion ↔
      completion ∈ config.history ∧ completion.event = event := by
  unfold completionOf
  constructor
  · intro found
    exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩
  · rintro ⟨member, same⟩
    obtain ⟨other, otherFound⟩ : ∃ other, config.history.find?
        (fun completion => completion.event = event) = some other := by
      apply Option.isSome_iff_exists.mp
      rw [List.find?_isSome]
      exact ⟨completion, member, by simpa using same⟩
    have otherMember := List.mem_of_find?_eq_some otherFound
    have otherSame : other.event = event := by simpa using List.find?_some otherFound
    rw [otherFound]
    congr 1
    exact List.inj_on_of_nodup_map config.history_nodup otherMember member
      (otherSame.trans same.symm)

/-- The defaulted players are read from the completion records. -/
theorem mem_defaulted_iff_completionOf (config : graph.Config) (who : Player) :
    who ∈ config.defaulted ↔
      ∃ event, (completionOf config event).bind EventCompletion.defaultEvent = some who := by
  change who ∈ (EventCompletion.defaults config.history).defaulted ↔ _
  simp only [EventCompletion.defaults, DefaultHistory.defaulted, List.mem_toFinset,
    List.mem_filterMap, List.mem_reverse, List.mem_map, id_eq, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨completion, member, rfl⟩, recorded⟩
    exact ⟨completion.event, completion,
      (completionOf_eq_some_iff config _ completion).mpr ⟨member, rfl⟩, recorded⟩
  · rintro ⟨event, completion, found, recorded⟩
    exact ⟨_, ⟨completion, ((completionOf_eq_some_iff config event completion).mp found).1,
      rfl⟩, recorded⟩

theorem defaulted_eq_of_completionOf_eq {left right : graph.Config}
    (same : completionOf left = completionOf right) : left.defaulted = right.defaulted := by
  ext who
  rw [mem_defaulted_iff_completionOf, mem_defaulted_iff_completionOf, same]

/-- Completing an event adds exactly its record. -/
theorem completionOf_complete (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    completionOf (config.complete event ready action value) =
      Function.update (completionOf config) event
        (some (EventGraph.completion graph event (config.actualDecision event action) value)) := by
  funext query
  unfold completionOf
  rw [Config.complete_history, List.find?_append]
  by_cases same : query = event
  · subst query
    have absent : config.history.find? (fun completion => completion.event = event) = none := by
      rw [List.find?_eq_none]
      intro completion member hit
      exact ready.1 ((config.history_exact event).mp
        (List.mem_map.mpr ⟨completion, member, by simpa using hit⟩))
    simp [absent, EventGraph.completion]
  · rw [Function.update_of_ne same]
    cases config.history.find? (fun completion => completion.event = query) with
    | some found => rfl
    | none =>
        have miss : ¬ event = query := fun hit => same hit.symm
        simp [EventGraph.completion, miss]

private theorem option_get_congr {α : Type} {left right : Option α} (same : left = right)
    (leftSome : left.isSome) (rightSome : right.isSome) :
    left.get leftSome = right.get rightSome := by
  subst same
  rfl

/-- Configurations with the same key take the same step to configurations with the same key. -/
theorem step_map_runKey_congr {left right : graph.Config} (same : runKey left = runKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (action : graph.Action event) :
    (left.step event leftReady action).map runKey =
      (right.step event rightReady action).map runKey := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have defaulted := defaulted_eq_of_completionOf_eq records
  have effective : left.effectiveAction event action = right.effectiveAction event action := by
    simp only [Config.effectiveAction, defaulted]
  have decision : left.actualDecision event action = right.actualDecision event action := by
    simp only [Config.actualDecision, defaulted]
  unfold Config.step
  rw [PMF.map_comp, PMF.map_comp]
  have outputs := option_get_congr
    (congrArg₂ (fun chosen store => (graph.nodes event).eval? chosen store) effective store)
    (EventCode.eval?_isSome_of_reads (graph.nodes event) (left.effectiveAction event action)
      left.store (fun _ read => left.read_available leftReady read))
    (EventCode.eval?_isSome_of_reads (graph.nodes event) (right.effectiveAction event action)
      right.store (fun _ read => right.read_available rightReady read))
  rw [outputs]
  congr 1
  funext value
  simp only [Function.comp_apply, runKey, storeRecall]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext member
    simp only [Config.complete_cut, EventOrder.Cut.mem_complete, cut]
  · simp only [store_complete, store]
  · simp only [completionOf_complete, records, decision]

/-- **Ready independence.** Simultaneously ready events have different actors;
completing one leaves the other's action law unchanged; and every action law is
read from the order-free key. -/
structure ReadyIndependent (profile : graph.BehavioralProfile) : Prop where
  actorsDiffer : ∀ (config : graph.Config) {left right : graph.EventId},
    config.cut.Ready left → config.cut.Ready right → left ≠ right →
      graph.ActorsDiffer left right
  stable : ∀ (config : graph.Config) {event other : graph.EventId},
    config.cut.Ready event → ∀ (otherReady : config.cut.Ready other), other ≠ event →
      ∀ (action : graph.Action other) (value : (graph.outputLayout other).Value),
        actionDistribution profile (config.complete other otherReady action value) event =
          actionDistribution profile config event
  congr : ∀ {left right : graph.Config}, runKey left = runKey right →
    ∀ event, actionDistribution profile left event = actionDistribution profile right event

/-- Ready independence entails actor-local uniqueness on every cut. -/
theorem ReadyIndependent.actorSerial {graph : Vegas.EventGraph Player L}
    {profile : graph.BehavioralProfile} (independent : graph.ReadyIndependent profile) :
    graph.ActorSerial := by
  intro event cut other who ready otherReady actor otherActor
  obtain ⟨config, same⟩ := Config.cut_surjective graph cut
  subst same
  by_contra different
  exact independent.actorsDiffer config ready otherReady (Ne.symm different) who actor otherActor

/-- Observation-independent event laws are ready independent under actor-local seriality.
Binding omissions remain possible; only another actor can complete a simultaneous ready event. -/
theorem ActorSerial.readyIndependent_of_eventDistributions (serial : graph.ActorSerial)
    (choices : ∀ who event, graph.actor? event = some who → PMF (graph.Action event)) :
    ReadyIndependent (fun who event actor _ _ => choices who event actor) where
  actorsDiffer config left right leftReady rightReady different owner leftActor rightActor := by
    exact different (serial.ready_actor_unique config.cut leftReady rightReady leftActor
      rightActor).symm
  stable config event other eventReady otherReady different action value := by
    cases owned : (graph.nodes event).actor with
    | none => rw [actionDistribution_of_ownerless _ _ owned, actionDistribution_of_ownerless _ _
      owned]
    | some owner =>
      rw [actionDistribution_of_actor _ _ owned, actionDistribution_of_actor _ _ owned]
      have notOwned : graph.actor? other ≠ some owner := by
        intro otherActor
        exact different (serial.ready_actor_unique config.cut eventReady otherReady owned
          otherActor)
      have member := mem_defaulted_complete_of_actor_ne config other otherReady action value
        owner notOwned
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left (member.mpr inactive), dite_eq_left inactive]
      · rw [dite_eq_right (fun active => inactive (member.mp active)), dite_eq_right inactive]
  congr {left right} same event := by
    have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
    have defaulted := defaulted_eq_of_completionOf_eq records
    cases owned : (graph.nodes event).actor with
    | none => rw [actionDistribution_of_ownerless _ _ owned, actionDistribution_of_ownerless _ _
      owned]
    | some owner =>
      rw [actionDistribution_of_actor _ _ owned, actionDistribution_of_actor _ _ owned]
      by_cases inactive : owner ∈ left.defaulted
      · rw [dite_eq_left inactive, dite_eq_left (defaulted ▸ inactive)]
      · rw [dite_eq_right inactive, dite_eq_right (defaulted ▸ inactive)]

/-- The law of the final key under canonical scheduling from one configuration. -/
def canonicalDistribution (profile : graph.BehavioralProfile) (config : graph.Config) :=
  (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) config.remaining config).map
    runKey

omit [DecidableEq Player] in
theorem remaining_eq_of_runKey_eq {left right : graph.Config} (same : runKey left = runKey right) :
    left.remaining = right.remaining := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  simp only [Config.remaining, cut]

/-- The full canonical configuration law factors through its next graph event. -/
theorem runPlan_remaining_canonical_step (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (least : ∀ other, config.cut.Ready other → event ≤ other) :
    let plan := graph.policyPlan profile graph.canonicalScheduler
    graph.runPlan plan config.remaining config = (eventStep profile config event ready).bind
      (fun next => graph.runPlan plan next.remaining next) := by
  dsimp only
  obtain ⟨rest, restEq⟩ : ∃ rest, config.remaining = rest + 1 := by
    have positive : config.remaining ≠ 0 :=
      fun zero => ready.not_terminal ((config.terminal_iff_remaining_zero).mpr zero)
    exact ⟨config.remaining - 1, by omega⟩
  rw [restEq, runPlan_canonical_succ profile rest config ready.not_terminal event ready least]
  apply bind_congr_on_support _
  intro next member
  have consumed : next.remaining + 1 = config.remaining := by
    unfold eventStep at member
    rw [PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepped⟩ := member
    exact config.remaining_step event ready action next stepped
  rw [(by omega : next.remaining = rest)]

theorem canonicalDistribution_step (profile : graph.BehavioralProfile) (config : graph.Config)
    (_notTerminal : ¬ config.cut.Terminal) (event : graph.EventId) (ready : config.cut.Ready event)
    (least : ∀ other, config.cut.Ready other → event ≤ other) :
    canonicalDistribution profile config = (eventStep profile config event ready).bind
      (canonicalDistribution profile) := by
  unfold canonicalDistribution
  rw [runPlan_remaining_canonical_step profile config event ready least, PMF.map_bind]

/-- **(A)** The canonical law is read from the order-free key. -/
theorem ReadyIndependent.canonicalDistribution_congr {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) :
    ∀ fuel (left right : graph.Config), left.remaining = fuel → runKey left = runKey right →
      canonicalDistribution profile left = canonicalDistribution profile right := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right remaining same
      have rightRemaining := (remaining_eq_of_runKey_eq same).symm.trans remaining
      unfold canonicalDistribution
      rw [remaining, rightRemaining]
      simp only [EventGraph.runPlan, PMF.pure_map, same]
  | succ fuel ih =>
      intro left right remaining same
      have cut : left.cut = right.cut := congrArg Prod.fst same
      have notTerminal : ¬ left.cut.Terminal := fun terminal => by
        have := (left.terminal_iff_remaining_zero).mp terminal
        omega
      have rightNotTerminal : ¬ right.cut.Terminal := by rw [← cut]; exact notTerminal
      obtain ⟨event, ready, least⟩ := exists_least_ready left notTerminal
      have rightReady : right.cut.Ready event := by rw [← cut]; exact ready
      have rightLeast : ∀ other, right.cut.Ready other → event ≤ other := by
        rw [← cut]; exact least
      rw [canonicalDistribution_step profile left notTerminal event ready least,
        canonicalDistribution_step profile right rightNotTerminal event rightReady rightLeast]
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

/-- Two fixed steps followed by a continuation. -/
theorem stepThen_bind (config : graph.Config) {first second : graph.EventId}
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) {γ : Type} (continuation : graph.Config → PMF γ) :
    (stepThen config first second firstReady secondReady different firstAction
        secondAction).bind continuation =
      (config.step first firstReady firstAction).bind fun next =>
        if ready : next.cut.Ready second then
          (next.step second ready secondAction).bind continuation
        else continuation next := by
  classical
  unfold stepThen
  rw [bindOnSupport_eq_bind_of_eq_on_support _ (g := fun next : graph.Config =>
    if ready : next.cut.Ready second then next.step second ready secondAction
    else PMF.pure next)]
  · rw [PMF.bind_bind]
    apply bind_congr_on_support _
    intro next _
    by_cases ready : next.cut.Ready second
    · simp only [dite_eq_left ready]
    · simp only [dite_eq_right ready, PMF.pure_bind]
  · intro next member
    have ready : next.cut.Ready second := by
      rw [config.step_cut first firstReady firstAction next member]
      exact secondReady.after_complete firstReady different.symm
    simp only [dite_eq_left ready]

omit [DecidableEq Player] in
private theorem cut_complete_comm {cut : graph.order.Cut} {first second : graph.EventId}
    (firstReady : cut.Ready first) (secondReady : cut.Ready second) (different : first ≠ second) :
    (cut.complete first firstReady).complete second
        (secondReady.after_complete firstReady different.symm) =
      (cut.complete second secondReady).complete first
        (firstReady.after_complete secondReady different) := by
  ext event
  simp only [EventOrder.Cut.mem_complete]
  tauto

/-- Every result of two fixed steps has the same cut. -/
theorem stepThen_cut (config : graph.Config) {first second : graph.EventId}
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstAction : graph.Action first)
    (secondAction : graph.Action second) (result : graph.Config)
    (member : result ∈ (stepThen config first second firstReady secondReady different
      firstAction secondAction).support) :
    result.cut = (config.cut.complete first firstReady).complete second
      (secondReady.after_complete firstReady different.symm) := by
  unfold stepThen at member
  rw [PMF.support_bindOnSupport] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨next, nextMember, resultMember⟩ := member
  rw [next.step_cut second _ secondAction result resultMember]
  ext event
  simp only [EventOrder.Cut.mem_complete,
    config.step_cut first firstReady firstAction next nextMember]

/-- Fixed actions at two ready events of different actors commute in their key law. -/
theorem stepThen_map_runKey_comm (config : graph.Config) {left right : graph.EventId}
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (differ : graph.ActorsDiffer left right)
    (leftAction : graph.Action left) (rightAction : graph.Action right) :
    (stepThen config left right leftReady rightReady different leftAction rightAction).map
        runKey =
      (stepThen config right left rightReady leftReady different.symm rightAction
        leftAction).map runKey := by
  let cut := (config.cut.complete left leftReady).complete right
    (rightReady.after_complete leftReady different.symm)
  have through (first second : graph.EventId) (firstReady : config.cut.Ready first)
      (secondReady : config.cut.Ready second) (firstSecond : first ≠ second)
      (firstAction : graph.Action first) (secondAction : graph.Action second)
      (sameCut : (config.cut.complete first firstReady).complete second
        (secondReady.after_complete firstReady firstSecond.symm) = cut) :
      (stepThen config first second firstReady secondReady firstSecond firstAction
          secondAction).map runKey =
        ((stepThen config first second firstReady secondReady firstSecond firstAction
          secondAction).map graph.storeRecall).map (Prod.mk cut) := by
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro result member
    simp only [Function.comp_apply, runKey]
    rw [stepThen_cut config firstReady secondReady firstSecond firstAction secondAction result
      member, sameCut]
  rw [through left right leftReady rightReady different leftAction rightAction rfl,
    through right left rightReady leftReady different.symm rightAction leftAction
      (cut_complete_comm rightReady leftReady different.symm),
    stepThen_map_storeRecall_comm config left right leftReady rightReady different differ]

/-- **(B)** Completing any ready event first and then continuing canonically
is the canonical continuation. -/
theorem ReadyIndependent.eventStep_bind_canonicalDistribution {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      ∀ event (ready : config.cut.Ready event),
        (eventStep profile config event ready).bind (canonicalDistribution profile) =
          canonicalDistribution profile config := by
  intro fuel
  induction fuel with
  | zero =>
      intro config remaining event ready
      exact absurd ((config.terminal_iff_remaining_zero).mpr remaining)
        ready.not_terminal
  | succ fuel ih =>
      intro config remaining event ready
      have notTerminal := ready.not_terminal
      obtain ⟨least, leastReady, leastLe⟩ := exists_least_ready config notTerminal
      rw [canonicalDistribution_step profile config notTerminal least leastReady leastLe]
      by_cases same : event = least
      · exact congrArg (fun law => law.bind (canonicalDistribution profile))
          (eventStep_congr_event profile config same ready leastReady)
      -- Each order expands into both action laws and the two fixed steps.
      have expand (first second : graph.EventId) (firstReady : config.cut.Ready first)
          (secondReady : config.cut.Ready second) (different : first ≠ second) :
          (eventStep profile config first firstReady).bind (canonicalDistribution profile) =
            (actionDistribution profile config first).bind fun firstAction =>
              (actionDistribution profile config second).bind fun secondAction =>
                (stepThen config first second firstReady secondReady different firstAction
                  secondAction).bind (canonicalDistribution profile) := by
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
        rw [← ih next nextRemaining second nextReady]
        simp only [dite_eq_left nextReady]
        unfold eventStep
        rw [PMF.bind_bind]
        rw [Config.step, PMF.support_map] at member
        obtain ⟨value, _, rfl⟩ := member
        rw [independent.stable config secondReady firstReady different firstAction value]
      rw [expand event least ready leastReady same,
        expand least event leastReady ready (Ne.symm same), PMF.bind_comm]
      apply bind_congr_on_support _
      intro leastAction _
      apply bind_congr_on_support _
      intro eventAction _
      exact bind_eq_of_map_key_eq runKey Set.univ _ _ (Set.subset_univ _) (Set.subset_univ _)
        (stepThen_map_runKey_comm config ready leastReady same
          (independent.actorsDiffer config ready leastReady same) eventAction leastAction) _
        (fun a _ b _ keys => independent.canonicalDistribution_congr _ a b rfl keys)

/-- **(C) Scheduler erasure.** Under every public scheduler a ready-independent
profile has the canonical law of the final key. -/
theorem ReadyIndependent.runPlan_map_runKey {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (scheduler : graph.PublicScheduler) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      (graph.runPlan (graph.policyPlan profile scheduler) fuel config).map runKey =
        canonicalDistribution profile config := by
  intro fuel
  induction fuel with
  | zero =>
      intro config remaining
      unfold canonicalDistribution
      rw [remaining]
      simp only [EventGraph.runPlan]
  | succ fuel ih =>
      intro config remaining
      have notTerminal : ¬ config.cut.Terminal := fun terminal => by
        have := (config.terminal_iff_remaining_zero).mp terminal
        omega
      rw [runPlan_policyPlan_succ profile scheduler fuel config notTerminal, PMF.map_bind]
      have each : ∀ selected : {event // event ∈ config.cut.enabled},
          ((eventStep profile config selected.1
            ((EventOrder.Cut.mem_enabled _ _).mp selected.2)).bind
              (graph.runPlan (graph.policyPlan profile scheduler) fuel)).map runKey =
            canonicalDistribution profile config := by
        intro selected
        rw [PMF.map_bind, ← independent.eventStep_bind_canonicalDistribution _ config rfl selected.1
          ((EventOrder.Cut.mem_enabled _ _).mp selected.2)]
        apply bind_congr_on_support _
        intro next member
        unfold eventStep at member
        rw [PMF.support_bind] at member
        simp only [Set.mem_iUnion] at member
        obtain ⟨action, _, stepped⟩ := member
        have := config.remaining_step _ _ action next stepped
        exact ih next (by omega)
      simp only [each]
      exact PMF.bind_const _ _

/-- Under every public scheduler a ready-independent profile has the canonical
law of the final store and completion records. -/
theorem ReadyIndependent.runPolicies_map_runKey {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (scheduler : graph.PublicScheduler)
    (inputs : graph.Inputs) :
    (graph.runPolicies scheduler profile inputs).map runKey =
      (graph.runPolicies graph.canonicalScheduler profile inputs).map runKey := by
  have initialRemaining : (Config.initial inputs : graph.Config).remaining =
      graph.order.eventCount := by
    simp [Config.remaining, Config.initial, EventOrder.Cut.empty]
  unfold EventGraph.runPolicies EventGraph.run
  rw [independent.runPlan_map_runKey scheduler _ _ initialRemaining,
    independent.runPlan_map_runKey graph.canonicalScheduler _ _ initialRemaining]

end Vegas.EventGraph

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem ReadyIndependent.actionDistribution_path_of_unfinished
    {profile : graph.BehavioralProfile} (independent : ReadyIndependent profile)
    {before after : graph.Config} {event : graph.EventId}
    (path : Relation.ReflTransGen Config.Step before after)
    (ready : before.cut.Ready event) (unfinished : event ∉ after.cut.completed) :
    actionDistribution profile after event = actionDistribution profile before event := by
  revert ready
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => intro _; rfl
  | @head before middle moved rest ih =>
      intro ready
      have middlePending : event ∉ middle.cut.completed :=
        fun completed => unfinished (Config.Step.path_completed_mono rest completed)
      have middleReady := Config.Step.path_ready_of_not_completed (.single moved) ready
        middlePending
      refine (ih middleReady).trans ?_
      obtain ⟨other, otherReady, action, supported⟩ := moved
      have different : other ≠ event := by
        intro same
        subst other
        apply middlePending
        rw [before.step_cut event otherReady action middle supported]
        exact Finset.mem_insert_self _ _
      rw [Config.step, PMF.mem_support_map_iff] at supported
      obtain ⟨value, _, rfl⟩ := supported
      exact independent.stable before ready otherReady different action value


/-- A supported step, and hence a finite path, lifts across equal graph keys. -/
theorem Config.Step.exists_of_runKey_eq {before after other : graph.Config}
    (step : Config.Step before after) (same : runKey before = runKey other) :
    ∃ next : graph.Config, Config.Step other next ∧ runKey after = runKey next := by
  obtain ⟨event, ready, action, supported⟩ := step
  have cut : before.cut = other.cut := congrArg Prod.fst same
  have otherReady : other.cut.Ready event := by rw [← cut]; exact ready
  have mapped : runKey after ∈ ((before.step event ready action).map runKey).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨after, supported, rfl⟩
  rw [step_map_runKey_congr same event ready otherReady action] at mapped
  obtain ⟨next, reached, key⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
  exact ⟨next, ⟨event, otherReady, action, reached⟩, key.symm⟩

theorem Config.Step.path_exists_of_runKey_eq {before after other : graph.Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (same : runKey before = runKey other) :
    ∃ next : graph.Config, Relation.ReflTransGen Config.Step other next ∧
      runKey after = runKey next := by
  induction path generalizing other with
  | refl => exact ⟨other, .refl, same⟩
  | tail path step ih =>
      obtain ⟨current, currentPath, currentKey⟩ := ih same
      obtain ⟨next, nextStep, nextKey⟩ := step.exists_of_runKey_eq currentKey
      exact ⟨next, currentPath.tail nextStep, nextKey⟩

end Vegas.EventGraph
