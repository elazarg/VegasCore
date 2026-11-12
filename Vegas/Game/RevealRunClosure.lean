module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealPhasing
public import Vegas.Game.RevealBlockGraph
public import Vegas.EventGraph.HonestClosure

@[expose] public section

/-! # The closure inside a run of reveals

Under a reference whose honest owners open a reveal exactly when its opening is
accepted, every ready reveal of another player than the deviator settles: its
action and output are determined. So inside a run of reveals the closure
completes every event of the run that does not depend on a pending reveal of
the active deviator. When the deviator's earliest pending reveal of the run is
`target`, the closure has completed exactly the events before the run's end
that do not depend on `target`.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Generic

variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- An event depends on another through a chain of predecessors. -/
def DependsOn (prior later : graph.EventId) : Prop :=
  Relation.ReflTransGen (fun before after => before ∈ graph.order.predecessors after) prior later

omit [DecidableEq Player] in
/-- A completed event's dependencies have completed. -/
theorem DependsOn.completed {prior later : graph.EventId} (depends : DependsOn graph prior later)
    {cut : graph.order.Cut} (done : later ∈ cut.completed) : prior ∈ cut.completed := by
  induction depends using Relation.ReflTransGen.head_induction_on with
  | refl => exact done
  | head member _ ih => exact cut.predecessor_closed ih member

end Generic

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- **Honest reveals settle.** Under a reference whose honest owners open a
reveal exactly when its opening is accepted, a ready reveal of another player
than `who` settles. -/
theorem honest_settles (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {config : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} (ready : config.cut.Ready event)
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication)
    (foreign : (serviceGraph setup mode).actor? event ≠ some who) :
    Settles ((serviceGraph setup mode).normalizeProfile base) who config event := by
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
    exists_resolve_of_publication publication
  have owned := nodeView_resolve_actor outputEq codeEq
  have ownedNode : ((serviceGraph setup mode).nodes event).actor = some owner := owned
  by_cases inactive : owner ∈ config.defaulted
  · exact settles_of_defaulted ready ownedNode inactive
  have honest : owner ≠ who := fun same => foreign (same ▸ owned)
  obtain ⟨value, stepEq, _⟩ := honest_complete_records (who := who) ready node honest inactive
  refine Settles.of_step ready (Or.inl publication) (Or.inl foreign) ?_ stepEq
  rw [actionLaw_of_actor _ _ ownedNode, dite_eq_right inactive]
  exact decides config event owner payload binding checks outputEq codeEq node owned inactive

/-- **The closure completes what does not wait for the active deviator.** In a
run of reveals whose earlier events have completed, the closure completes
every event before the run's end all of whose dependencies of the deviator
have completed, or once the deviator has defaulted. -/
theorem closure_completes_run (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ config.cut.completed) :
    ∀ event : (serviceGraph setup mode).EventId, event.val < finish →
      (∀ owned : (serviceGraph setup mode).EventId,
        DependsOn (serviceGraph setup mode) owned event →
        (serviceGraph setup mode).actor? owned = some who →
          owned ∈ config.cut.completed ∨ who ∈ config.defaulted) →
      event ∈ (closure ((serviceGraph setup mode).normalizeProfile base) who
        config).cut.completed := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have path := closure_path R who config
  intro event
  induction hval : event.val using Nat.strong_induction_on generalizing event with
  | _ rank ih =>
  intro late waits
  by_contra pending
  by_cases early : event.val < start
  · exact pending (Config.Step.path_completed_mono path (earlier event early))
  push Not at early
  have ready : (closure R who config).cut.Ready event := by
    refine ⟨pending, fun prior member => ?_⟩
    have smaller := G.order.predecessor_lt member
    exact ih prior.val (hval ▸ smaller) prior rfl (by omega) fun owned depends ownedWho =>
      waits owned (depends.tail member) ownedWho
  have publication := run.publications event early (hval ▸ late)
  by_cases mine : G.actor? event = some who
  · rcases waits event .refl mine with done | defaulted
    · exact pending (Config.Step.path_completed_mono path done)
    · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
        exists_resolve_of_publication publication
      have owned := nodeView_resolve_actor outputEq codeEq
      have ownedNode : (G.nodes event).actor = some owner := owned
      have same : owner = who := Option.some.inj (owned.symm.trans mine)
      subst same
      exact closure_quiet R owner config event (settles_of_defaulted ready ownedNode
        (Config.Step.path_defaulted_mono path defaulted))
  · exact closure_quiet R who config event (honest_settles base decides who ready publication mine)

omit [DecidableEq Player] in
/-- A dependency is no later than the event depending on it. -/
theorem DependsOn.le {graph : Vegas.EventGraph Player L} {prior later : graph.EventId}
    (depends : DependsOn graph prior later) : prior.val ≤ later.val := by
  induction depends with
  | refl => exact le_rfl
  | tail _ member ih => exact ih.trans (graph.order.predecessor_lt member).le

omit [DecidableEq Player] in
/-- Two reveals of one owner in a graph relaxing the rank order only between
independent reveals are ordered by rank. -/
theorem RelaxedOrder.dependsOn_of_same_owner {graph : Vegas.EventGraph Player L}
    (relaxed : RelaxedOrder graph) {prior later : graph.EventId} {owner : Player}
    (priorOwned : graph.actor? prior = some owner) (laterOwned : graph.actor? later = some owner)
    (earlier : prior.val < later.val) : DependsOn graph prior later :=
  .single ((relaxed prior later).mpr ⟨earlier, fun independent =>
    independent.2.2.2 (priorOwned.trans laterOwned.symm)⟩)

/-- The closure completes nothing from the end of a run on while the closure
leaves the run unfinished. -/
theorem closure_before_finish (base : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    {blocked : (serviceGraph setup mode).EventId} (blockedLate : blocked.val < finish)
    (blockedPending : blocked ∉ (closure ((serviceGraph setup mode).normalizeProfile base) who
      config).cut.completed)
    {event : (serviceGraph setup mode).EventId}
    (done : event ∈ (closure ((serviceGraph setup mode).normalizeProfile base) who
      config).cut.completed) : event.val < finish := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  by_contra late
  push Not at late
  have closing : finish < G.order.eventCount := lt_of_le_of_lt late event.isLt
  let closer : G.EventId := ⟨finish, closing⟩
  have closerDone : closer ∈ (closure R who config).cut.completed := by
    rcases Nat.eq_or_lt_of_le late with same | later
    · have equal : event = closer := Fin.ext same.symm
      rw [← equal]
      exact done
    · exact (closure R who config).cut.predecessor_closed done
        (relaxed.predecessor_of_not_publication (run.closed closer rfl) later)
  exact blockedPending ((closure R who config).cut.predecessor_closed closerDone
    (relaxed.predecessor_of_later_not_publication (run.closed closer rfl) blockedLate))

/-- **The closure at a point of a run.** When the deviator is active and
`target` is its earliest pending reveal of an unfinished run whose earlier
events have completed, the closure has completed exactly the events before the
run's end that do not depend on `target`. -/
theorem closure_completed_iff_target (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
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
    ∀ event : (serviceGraph setup mode).EventId,
      event ∈ (closure ((serviceGraph setup mode).normalizeProfile base) who
        config).cut.completed ↔
        event.val < finish ∧ ¬ DependsOn (serviceGraph setup mode) target event := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have targetPending : target ∉ (closure R who config).cut.completed := fun targetDone =>
    ((closure_shape R who _ config rfl).1 target targetDone pending).2 active targetOwned
  intro event
  constructor
  · intro done
    refine ⟨closure_before_finish base who relaxed run targetLate targetPending done,
      fun depends => targetPending (depends.completed done)⟩
  · rintro ⟨late, independent⟩
    apply closure_completes_run base decides who run earlier event late
    intro owned depends ownedWho
    left
    by_cases early : owned.val < start
    · exact earlier owned early
    push Not at early
    rcases Nat.lt_trichotomy owned.val target.val with smaller | same | larger
    · exact before owned early smaller ownedWho
    · have equal : owned = target := Fin.ext same
      subst equal
      exact (independent depends).elim
    · exact (independent ((relaxed.dependsOn_of_same_owner targetOwned ownedWho larger).trans
        depends)).elim

/-- **The closure at the end of the deviator's part of a run.** When every
reveal of the deviator in a run whose earlier events have completed has
completed, or the deviator has defaulted, the closure has completed every event
before the run's end. -/
theorem closure_completes_done (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ config.cut.completed)
    (finished : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → (serviceGraph setup mode).actor? event = some who →
        event ∈ config.cut.completed ∨ who ∈ config.defaulted) :
    ∀ event : (serviceGraph setup mode).EventId, event.val < finish →
      event ∈ (closure ((serviceGraph setup mode).normalizeProfile base) who
        config).cut.completed := by
  intro event late
  apply closure_completes_run base decides who run earlier event late
  intro owned depends ownedWho
  by_cases early : owned.val < start
  · exact Or.inl (earlier owned early)
  push Not at early
  exact finished owned early (lt_of_le_of_lt depends.le late) ownedWho

end Vegas
