/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.BarrierInformation

/-! # Reveal-relaxed event dependencies

Under public-barrier dependencies every publication waits for every earlier
event, and every later event waits for it. Two publications with different
owners, the later of which reads nothing the earlier one writes, need not wait
for each other. Dropping exactly those direct dependencies lets a run of
consecutive independent reveals complete in any order. Every other event still
waits for each of them, so a commitment or a sample between two publications
keeps them ordered.

Information stays exact at every ready event that is not a publication. At a
ready publication the actor may additionally see, or miss, the outputs of the
publications it is independent of; nothing else differs from the source
prefix.
-/

noncomputable section

namespace Vegas.EventGraph

section Fields

variable {Player : Type} {L : IExpr}

namespace EventField

/-- The output of a reveal. -/
def IsPublication : EventField Player L → Prop
  | .publication _ => True
  | .publicData _ | .binding _ _ | .privateInput _ _ => False

instance (field : EventField Player L) : Decidable field.IsPublication := by
  cases field <;> simp only [IsPublication] <;> infer_instance

/-- A publication is public. -/
theorem IsPublication.isPublic {field : EventField Player L}
    (publication : field.IsPublication) : field.IsPublic := by
  cases field <;> simp_all [IsPublication, IsPublic]

end EventField

/-- A node without an actor is a chance node, never a reveal. -/
theorem EventCode.not_publication_of_actor_none [IExpr.ResultTypes L]
    {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (ownerless : code.actor = none) :
    ¬ output.IsPublication := by
  cases code <;> simp_all [EventCode.actor, EventField.IsPublication]

end Fields

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

variable (graph : Vegas.EventGraph Player L)

/-- Two publications that need not be ordered: the later is a reveal of a
different owner that does not read the earlier one. -/
def IndependentReveals (prior event : graph.EventId) : Prop :=
  (graph.outputLayout prior).IsPublication ∧ (graph.outputLayout event).IsPublication ∧
    (.inr prior : graph.Field) ∉ (graph.nodes event).readFields ∧
    graph.actor? prior ≠ graph.actor? event

/-- The graph keeps every public-barrier dependency except possibly the direct
dependencies between independent reveals. -/
def RevealRelaxedOrdered : Prop :=
  ∀ event prior, prior ∈ (barrierOrder graph.outputLayout).predecessors event →
    ¬ graph.IndependentReveals prior event → prior ∈ graph.order.predecessors event

variable {graph}

omit [DecidableEq Player] in
/-- An event that is not a publication is independent of no reveal. -/
theorem IndependentReveals.not_of_not_publication_left {prior event : graph.EventId}
    (notPublication : ¬ (graph.outputLayout prior).IsPublication) :
    ¬ graph.IndependentReveals prior event :=
  fun independent => notPublication independent.1

omit [DecidableEq Player] in
/-- An event that is not a publication depends on every reveal it follows. -/
theorem IndependentReveals.not_of_not_publication_right {prior event : graph.EventId}
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    ¬ graph.IndependentReveals prior event :=
  fun independent => notPublication independent.2.1

omit [DecidableEq Player] in
/-- Events of one actor are never independent reveals. -/
theorem IndependentReveals.not_of_actor_eq {prior event : graph.EventId}
    (sameActor : graph.actor? prior = graph.actor? event) :
    ¬ graph.IndependentReveals prior event :=
  fun independent => independent.2.2.2 sameActor

/-- Public-barrier dependencies keep every reveal-relaxed dependency. -/
theorem BarrierOrdered.revealRelaxedOrdered (ordered : graph.BarrierOrdered) :
    graph.RevealRelaxedOrdered :=
  fun event _ member _ => ordered event member

namespace RevealRelaxedOrdered

/-- Two distinct ready events one of which is public are independent reveals,
the rank-earlier one first. -/
theorem ready_public_pair (relaxed : graph.RevealRelaxedOrdered)
    (cut : graph.order.Cut) {left right : graph.EventId}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right) (different : left ≠ right)
    (isPublic : (graph.outputLayout left).IsPublic ∨ (graph.outputLayout right).IsPublic) :
    (left.val < right.val ∧ graph.IndependentReveals left right) ∨
      (right.val < left.val ∧ graph.IndependentReveals right left) := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with before | after
  · refine Or.inl ⟨before, ?_⟩
    by_contra dependent
    have member : left ∈ (barrierOrder graph.outputLayout).predecessors right :=
      (mem_barrierOrder graph.outputLayout left right).2
        ⟨before, isPublic.elim Or.inl fun rightPublic => Or.inr (Or.inl rightPublic)⟩
    exact leftReady.1 (rightReady.2 (relaxed right left member dependent))
  · refine Or.inr ⟨after, ?_⟩
    by_contra dependent
    have member : right ∈ (barrierOrder graph.outputLayout).predecessors left :=
      (mem_barrierOrder graph.outputLayout right left).2
        ⟨after, isPublic.elim (fun leftPublic => Or.inr (Or.inl leftPublic)) Or.inl⟩
    exact rightReady.1 (leftReady.2 (relaxed left right member dependent))

/-- Two distinct ready events one of which is public are both publications
with different actors. -/
theorem ready_public_pair_publications (relaxed : graph.RevealRelaxedOrdered)
    (cut : graph.order.Cut) {left right : graph.EventId}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right) (different : left ≠ right)
    (isPublic : (graph.outputLayout left).IsPublic ∨ (graph.outputLayout right).IsPublic) :
    (graph.outputLayout left).IsPublication ∧ (graph.outputLayout right).IsPublication ∧
      graph.actor? left ≠ graph.actor? right := by
  rcases relaxed.ready_public_pair cut leftReady rightReady different isPublic with
    ⟨_, independent⟩ | ⟨_, independent⟩
  · exact ⟨independent.1, independent.2.1, independent.2.2.2⟩
  · exact ⟨independent.2.1, independent.1, fun same => independent.2.2.2 same.symm⟩

omit [DecidableEq Player] in
private theorem binding_of_not_public (event : graph.EventId)
    (notPublic : ¬ (graph.outputLayout event).IsPublic) :
    ∃ owner payload, graph.actor? event = some owner ∧
      graph.outputLayout event = .binding owner payload := by
  cases actor : graph.actor? event with
  | none =>
      exact absurd (EventCode.output_public_of_actor_none (graph.nodes event) actor) notPublic
  | some owner =>
      rcases EventCode.output_public_or_binding_of_actor (graph.nodes event) owner actor with
        isPublic | ⟨payload, binding⟩
      · exact absurd isPublic notPublic
      · exact ⟨owner, payload, rfl, binding⟩

omit [DecidableEq Player] in
private theorem actor_of_publication (event : graph.EventId)
    (publication : (graph.outputLayout event).IsPublication) :
    ∃ owner, graph.actor? event = some owner := by
  cases actor : graph.actor? event with
  | none =>
      exact absurd publication
        (EventCode.not_publication_of_actor_none (graph.nodes event) actor)
  | some owner => exact ⟨owner, rfl⟩

/-- Distinct simultaneously ready events are strategic and have different
actors: either both are independent reveals, or both are bindings of different
owners. -/
theorem ready_pair_actors (relaxed : graph.RevealRelaxedOrdered)
    {cut : graph.order.Cut} {left right : graph.EventId}
    (leftReady : cut.Ready left) (rightReady : cut.Ready right) (different : left ≠ right) :
    ∃ leftOwner rightOwner,
      graph.actor? left = some leftOwner ∧
      graph.actor? right = some rightOwner ∧ leftOwner ≠ rightOwner := by
  by_cases isPublic :
      (graph.outputLayout left).IsPublic ∨ (graph.outputLayout right).IsPublic
  · obtain ⟨leftPublication, rightPublication, actorsNe⟩ :=
      relaxed.ready_public_pair_publications cut leftReady rightReady different isPublic
    obtain ⟨leftOwner, leftActor⟩ := actor_of_publication left leftPublication
    obtain ⟨rightOwner, rightActor⟩ := actor_of_publication right rightPublication
    refine ⟨leftOwner, rightOwner, leftActor, rightActor, ?_⟩
    intro same
    exact actorsNe (by rw [leftActor, rightActor, same])
  · obtain ⟨leftPrivate, rightPrivate⟩ := not_or.mp isPublic
    obtain ⟨leftOwner, leftPayload, leftActor, leftBinding⟩ :=
      binding_of_not_public left leftPrivate
    obtain ⟨rightOwner, rightPayload, rightActor, rightBinding⟩ :=
      binding_of_not_public right rightPrivate
    refine ⟨leftOwner, rightOwner, leftActor, rightActor, ?_⟩
    intro same
    subst same
    have leftNotPublication : ¬ (graph.outputLayout left).IsPublication :=
      fun publication => leftPrivate publication.isPublic
    have rightNotPublication : ¬ (graph.outputLayout right).IsPublication :=
      fun publication => rightPrivate publication.isPublic
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with before | after
    · have member : left ∈ (barrierOrder graph.outputLayout).predecessors right :=
        (mem_barrierOrder graph.outputLayout left right).2 ⟨before, Or.inr (Or.inr (by
          rw [leftBinding, rightBinding]
          simp [EventField.SameBindingOwner]))⟩
      exact leftReady.1 (rightReady.2 (relaxed right left member
        (IndependentReveals.not_of_not_publication_left leftNotPublication)))
    · have member : right ∈ (barrierOrder graph.outputLayout).predecessors left :=
        (mem_barrierOrder graph.outputLayout right left).2 ⟨after, Or.inr (Or.inr (by
          rw [leftBinding, rightBinding]
          simp [EventField.SameBindingOwner]))⟩
      exact rightReady.1 (leftReady.2 (relaxed left right member
        (IndependentReveals.not_of_not_publication_left rightNotPublication)))

/-- Each player acts at most at one ready event. -/
theorem ready_actor_unique (relaxed : graph.RevealRelaxedOrdered)
    (cut : graph.order.Cut) {event other : graph.EventId} {who : Player}
    (ready : cut.Ready event) (otherReady : cut.Ready other)
    (actor : graph.actor? event = some who) (otherActor : graph.actor? other = some who) :
    other = event := by
  by_contra different
  obtain ⟨otherOwner, eventOwner, otherActor', eventActor', ownersNe⟩ :=
    relaxed.ready_pair_actors otherReady ready different
  rw [otherActor] at otherActor'
  rw [actor] at eventActor'
  exact ownersNe ((Option.some.inj otherActor').symm.trans (Option.some.inj eventActor'))

/-- At a ready strategic event, an output visible to the actor that is not
independent of the event in either direction is available exactly when its
producer is rank-earlier. -/
theorem ready_visible_iff (relaxed : graph.RevealRelaxedOrdered) (cut : graph.order.Cut)
    {event other : graph.EventId} {who : Player}
    (ready : cut.Ready event) (actor : graph.actor? event = some who)
    (visible : (graph.outputLayout other).VisibleTo who)
    (notBefore : ¬ graph.IndependentReveals other event)
    (notAfter : ¬ graph.IndependentReveals event other) :
    other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro completed
    by_contra notEarlier
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt notEarlier) with same | later
    · have eventEq : event = other := Fin.ext same
      exact ready.1 (eventEq ▸ completed)
    · have isPredecessor : event ∈ graph.order.predecessors other :=
        relaxed other event ((mem_barrierOrder graph.outputLayout event other).2
          ⟨later, EventField.barrierRelated_symm _ _
            (EventCode.barrierRelated_of_visible (graph.nodes event) who actor _
              (graph.nodes other) visible)⟩) notAfter
      exact ready.1 (cut.predecessor_closed completed isPredecessor)
  · intro earlier
    exact ready.2 (relaxed event other ((mem_barrierOrder graph.outputLayout other event).2
      ⟨earlier, EventCode.barrierRelated_of_visible (graph.nodes event) who actor _
        (graph.nodes other) visible⟩) notBefore)

/-- At a ready strategic event that is not a reveal, the visible fields are
exactly the source-prefix fields. -/
theorem ready_fields_exact (relaxed : graph.RevealRelaxedOrdered) (cut : graph.order.Cut)
    {event : graph.EventId} {who : Player}
    (ready : cut.Ready event) (actor : graph.actor? event = some who)
    (notPublication : ¬ (graph.outputLayout event).IsPublication) :
    graph.visibleFields who cut = graph.prefixSchema.fields event := by
  ext field
  simp only [prefixSchema, actor, prefixFields, visibleFields, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases field with
  | inl => simp [FieldAvailable]
  | inr prior =>
      change (prior ∈ cut.completed ∧ (graph.outputLayout prior).VisibleTo who) ↔
        (graph.outputLayout prior).VisibleTo who ∧ prior.val < event.val
      have exact := fun (visible : (graph.outputLayout prior).VisibleTo who) =>
        relaxed.ready_visible_iff cut ready actor visible
        (IndependentReveals.not_of_not_publication_right notPublication)
        (IndependentReveals.not_of_not_publication_left notPublication)
      constructor
      · rintro ⟨completed, visible⟩
        exact ⟨visible, (exact visible).mp completed⟩
      · rintro ⟨visible, earlier⟩
        exact ⟨(exact visible).mpr earlier, visible⟩

/-- At every ready strategic event, reveals included, the actor's completed own
events are exactly its rank-earlier events. -/
theorem ready_own_history_exact (relaxed : graph.RevealRelaxedOrdered)
    (cut : graph.order.Cut) {event : graph.EventId} {who : Player}
    (ready : cut.Ready event) (actor : graph.actor? event = some who) :
    (graph.prefixSchema.ownHistory event).toFinset = graph.completedOwnEvents who cut := by
  ext prior
  simp only [prefixSchema, actor, List.mem_toFinset, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq, completedOwnEvents,
    Finset.mem_filter]
  have exact := fun (owned : graph.actor? prior = some who) =>
    relaxed.ready_visible_iff cut ready actor
      (EventCode.output_visible_of_actor (graph.nodes prior) who owned)
      (IndependentReveals.not_of_actor_eq (by rw [owned, actor]))
      (IndependentReveals.not_of_actor_eq (by rw [owned, actor]))
  constructor
  · rintro ⟨earlier, owned⟩
    exact ⟨(exact owned).mpr earlier, owned⟩
  · rintro ⟨completed, owned⟩
    exact ⟨(exact owned).mp completed, owned⟩

end RevealRelaxedOrdered

end Vegas.EventGraph
