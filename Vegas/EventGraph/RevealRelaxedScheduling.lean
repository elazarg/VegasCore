/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SchedulerErasure

/-! # Scheduling reveal-relaxed graphs

On a reveal-relaxed graph two simultaneously ready events are either bindings
of different owners, each hidden from the other's actor, or independent
reveals, each of whose outputs is public. A reveal kernel may therefore see a
foreign reveal of its block complete before it acts. For a profile whose reveal
kernels ignore the observation, for example one that always opens, that is
invisible: such a profile is ready-independent
(`Vegas.EventGraph.RevealRelaxedOrdered.readyIndependent`).
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A profile whose kernel at every reveal ignores the observation, as one that
always opens does. -/
def ObliviousAtPublications (profile : graph.BehavioralProfile) : Prop :=
  ∀ who event (actor : graph.actor? event = some who),
    (graph.outputLayout event).IsPublication →
      ∀ left right : graph.PlayerObservation who,
        profile who event actor left = profile who event actor right

/-- On a reveal-relaxed graph every profile that ignores observations at reveals
is ready independent: a simultaneously ready foreign binding is hidden, and a
simultaneously ready foreign reveal meets a reveal kernel that ignores it. -/
theorem RevealRelaxedOrdered.readyIndependent (relaxed : graph.RevealRelaxedOrdered)
    {profile : graph.BehavioralProfile} (oblivious : ObliviousAtPublications profile) :
    graph.ReadyIndependent profile where
  ready_pair_not_actor leftReady rightReady different who leftActor rightActor := by
    obtain ⟨leftOwner, rightOwner, leftOwned, rightOwned, ownersNe⟩ :=
      relaxed.ready_pair_actors leftReady rightReady different
    exact ownersNe ((Option.some.inj (leftOwned.symm.trans leftActor)).trans
      (Option.some.inj (rightOwned.symm.trans rightActor)).symm)
  normalizedAction_complete config event other eventReady otherReady different action value := by
    obtain ⟨who, foreign, actor, otherActor, differentOwner⟩ :=
      relaxed.ready_pair_actors eventReady otherReady different
    have differentOwner : foreign ≠ who := differentOwner.symm
    rw [normalizedAction_of_actor _ _ _ who actor,
      normalizedAction_of_actor _ _ _ who actor]
    by_cases publication : (graph.outputLayout event).IsPublication
    · exact oblivious who event actor publication _ _
    · have otherPrivate : ¬ (graph.outputLayout other).IsPublic := by
        intro otherPublic
        exact publication (relaxed.ready_public_pair_publications config.cut eventReady
          otherReady different (Or.inr otherPublic)).1
      have hidden : ¬ graph.fieldVisibleTo who (.inr other) := by
        intro visible
        change (graph.outputLayout other).VisibleTo who at visible
        have visibleForeign : (graph.outputLayout other).VisibleTo foreign :=
          EventCode.output_visible_of_actor (graph.nodes other) foreign otherActor
        cases kind : graph.outputLayout other <;>
          simp_all [EventField.IsPublic, EventField.VisibleTo]
      have storeEq := graph.playerStore_complete_of_hidden who config other otherReady
        action value hidden
      have notOwned : graph.actor? other ≠ some who := by
        rw [otherActor]
        simpa using differentOwner
      have actionsEq := graph.ownCompletions_complete_of_not_actor who config other
        otherReady action value notOwned
      apply congrArg (profile who event actor)
      apply PlayerObservation.ext graph
      · rfl
      · exact storeEq
      · exact actionsEq

end Vegas.EventGraph
