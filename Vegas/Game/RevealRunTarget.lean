/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunAgree
import Vegas.Game.LastOwnedPhase

/-! # The deviator's next reveal in a run

Inside a run of reveals whose earlier events have completed, let `target` be
the deviator's earliest reveal of the run not yet completed. While `target`
is pending, it is the only event of the deviator that can be ready. At the
closure, while the deviator is active, `target` is ready and is the only ready
event: every other event either settles or waits for `target`.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- **Only the target can be ready for the deviator.** In a run whose earlier
events and whose deviator reveals before `target` have completed, every ready
event of the deviator at a later configuration with `target` pending is
`target`. -/
theorem ready_owned_eq_target (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {origin : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ origin.cut.completed)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    (before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ origin.cut.completed)
    {config : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step origin config)
    (pending : target ∉ config.cut.completed) {event : (serviceGraph setup mode).EventId}
    (ready : config.cut.Ready event) (owned : (serviceGraph setup mode).actor? event = some who) :
    event = target := by
  let G := serviceGraph setup mode
  have mono := Config.Step.path_completed_mono path
  by_cases early : event.val < start
  · exact (ready.1 (mono (earlier event early))).elim
  push Not at early
  by_cases late : finish ≤ event.val
  · exfalso
    have closing : finish < G.order.eventCount := lt_of_le_of_lt late event.isLt
    let closer : G.EventId := ⟨finish, closing⟩
    have targetBefore : target ∈ G.order.predecessors closer :=
      relaxed.predecessor_of_later_not_publication (run.closed closer rfl)
        (show target.val < closer.val from targetLate)
    rcases Nat.eq_or_lt_of_le late with same | later
    · have equal : event = closer := Fin.ext same.symm
      subst equal
      exact pending (ready.2 targetBefore)
    · have closerDone : closer ∈ config.cut.completed :=
        ready.2 (relaxed.predecessor_of_not_publication (run.closed closer rfl) later)
      exact pending (config.cut.predecessor_closed closerDone targetBefore)
  push Not at late
  rcases Nat.lt_trichotomy event.val target.val with smaller | same | larger
  · exact (ready.1 (mono (before event early smaller owned))).elim
  · exact Fin.ext same
  · exact (pending (ready.2 ((relaxed target event).mpr ⟨larger, fun independent =>
      independent.2.2.2 (targetOwned.trans owned.symm)⟩))).elim

/-- **The target is alone at the closure.** While the deviator is active at a
point of a run whose earlier events and whose deviator reveals before a pending
`target` have completed, `target` is ready at the closure and every ready event
there is `target`. -/
theorem closure_target_alone (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ config.cut.completed)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    (before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ config.cut.completed)
    (active : who ∉ config.defaulted) (pending : target ∉ config.cut.completed) :
    (closure ((serviceGraph setup mode).normalizeProfile base) who config).cut.Ready target ∧
      ∀ event, (closure ((serviceGraph setup mode).normalizeProfile base) who
        config).cut.Ready event → event = target := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have path := closure_path R who config
  have completedIff := closure_completed_iff_target base decides who relaxed run earlier target
    targetOwned targetLate before active pending
  have targetPending : target ∉ (closure R who config).cut.completed := fun done =>
    ((completedIff target).mp done).2 .refl
  have closureActive := (closure_shape R who _ config rfl).2 active
  have closureEarlier : ∀ event : G.EventId, event.val < start →
      event ∈ (closure R who config).cut.completed :=
    fun event early => Config.Step.path_completed_mono path (earlier event early)
  have closureBefore : ∀ event : G.EventId, start ≤ event.val → event.val < target.val →
      G.actor? event = some who → event ∈ (closure R who config).cut.completed :=
    fun event early smaller owned => Config.Step.path_completed_mono path
      (before event early smaller owned)
  refine ⟨⟨targetPending, fun prior member => ?_⟩, fun event ready => ?_⟩
  · have smaller := G.order.predecessor_lt member
    refine (completedIff prior).mpr ⟨lt_trans smaller targetLate, fun depends => ?_⟩
    have cycle := depends.le
    omega
  · by_contra different
    by_cases owned : G.actor? event = some who
    · exact different (ready_owned_eq_target who relaxed run closureEarlier target targetOwned
        targetLate closureBefore .refl targetPending ready owned)
    · have publication : (G.outputLayout event).IsPublication := by
        rcases concurrent (closure R who config).cut ready
            ⟨targetPending, fun prior member => (completedIff prior).mpr
              ⟨lt_trans (G.order.predecessor_lt member) targetLate, fun depends => by
                have := depends.le
                have := G.order.predecessor_lt member
                omega⟩⟩ different with independent | independent
        · exact independent.1
        · exact independent.2.1
      exact closure_quiet R who config event
        (honest_settles base decides who ready publication owned)

section Advance

variable {graph : Vegas.EventGraph Player L}

/-- The closure key after an owned event takes an action from a configuration
of a key where it is ready; the key itself when it takes no action or is ready
at no configuration of the key. -/
def closureAdvance (reference : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (key : RunKey graph) : Option (graph.Action event) → RunKey graph
  | none => key
  | some action =>
      open scoped Classical in
      if found : ∃ config : graph.Config, runKey config = key ∧ config.cut.Ready event then
        runKey (closure reference who
          (ownedStepped event owned found.choose found.choose_spec.2 action))
      else key

/-- The closure advance from a configuration where the owned event is ready. -/
theorem closureAdvance_runKey {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event)
    (event : graph.EventId) (owned : graph.actor? event = some who) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    closureAdvance reference who event owned (runKey config) (some action) =
      runKey (closure reference who (ownedStepped event owned config ready action)) := by
  have found : ∃ other : graph.Config, runKey other = runKey config ∧ other.cut.Ready event :=
    ⟨config, rfl, ready⟩
  dsimp only [closureAdvance]
  rw [dite_eq_left found]
  have keys : runKey (ownedStepped event owned found.choose found.choose_spec.2 action) =
      runKey (ownedStepped event owned config ready action) := by
    have mapped := step_map_runKey_congr found.choose_spec.1 event found.choose_spec.2 ready
      action
    rw [step_eq_ownedStepped event owned found.choose found.choose_spec.2 action,
      step_eq_ownedStepped event owned config ready action, PMF.pure_map, PMF.pure_map]
      at mapped
    have supports := congrArg PMF.support mapped
    rw [PMF.support_pure, PMF.support_pure] at supports
    exact Set.singleton_eq_singleton_iff.mp supports
  exact closure_runKey_congr keyed _ _ _ rfl keys

/-- Without a configuration of the key where the owned event is ready, the key
does not advance. -/
theorem closureAdvance_of_not_ready {reference : graph.BehavioralProfile} {who : Player}
    (event : graph.EventId) (owned : graph.actor? event = some who) (key : RunKey graph)
    (blocked : ∀ config : graph.Config, runKey config = key → ¬ config.cut.Ready event)
    (choice : Option (graph.Action event)) :
    closureAdvance reference who event owned key choice = key := by
  cases choice with
  | none => rfl
  | some action =>
      dsimp only [closureAdvance]
      rw [dite_eq_right]
      rintro ⟨config, keyEq, ready⟩
      exact blocked config keyEq ready

/-- A completion supported by an owned event's step is the owned step. -/
theorem ownedStepped_eq_of_mem {event : graph.EventId} {who : Player}
    (owned : graph.actor? event = some who) {config next : graph.Config}
    {ready : config.cut.Ready event} {action : graph.Action event}
    (member : next ∈ (config.step event ready action).support) :
    next = ownedStepped event owned config ready action := by
  rw [step_eq_ownedStepped event owned config ready action, PMF.mem_support_pure_iff] at member
  exact member

end Advance

end Vegas
