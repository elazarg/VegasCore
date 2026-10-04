/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMenuRestriction
import Interaction.ReactiveOwnPlay
import GameTheory.Protocol.RestrictionExecution
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Nested response menus retain communication and arbitrary policy laws

The smaller menu permits silence and one packet; the larger additionally
permits a different packet. Both use the same passive observation rule. The
regression quantifies over all smaller-menu policies and continuation histories.
-/

noncomputable section

namespace InteractionTests.ReactiveMenuRestriction

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

private abbrev app : ReactiveApplication Bool where
  State := Unit
  Payload := Bool
  Submission := Bool
  EnvironmentCommand := Empty
  LocalObservation := Unit
  PublicObservation := Unit
  packet := fun _ _ _ => id
  submit state _ _ := state
  handle state _ := some state
  environment _ command := nomatch command
  observePlayer _ _ := ()
  observePublic _ := ()
  observePending _ pending := (PMF.uniformOfFintype Bool).map fun observed =>
    if observed then (pending.map Message.id).toFinset else ∅

private def silent : app.Action := ⟨none⟩
private def send (value : Bool) : app.Action := ⟨some (.submit value)⟩

open Classical in
private def smaller : app.ResponseMenu where
  actions _ _ _ := {silent, send false}
  nonempty _ _ _ := ⟨silent, by simp⟩

open Classical in
private def larger : app.ResponseMenu where
  actions _ _ _ := {silent, send false, send true}
  nonempty _ _ _ := ⟨silent, by simp⟩

private theorem included : smaller.IncludedIn larger := by
  classical
  intro who past view response member
  change response ∈ ({silent, send false, send true} : Finset app.Action)
  change response ∈ ({silent, send false} : Finset app.Action) at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member ⊢
  rcases member with rfl | rfl <;> simp

private def scheduler : app.Scheduler := fun past _ =>
  PMF.pure (if past.length = 0 then .activate false else .activate true)

private abbrev source := smaller.information (PMF.pure ()) 2 scheduler
private abbrev target := larger.information (PMF.pure ()) 2 scheduler
private abbrev restriction := included.actionRestriction (PMF.pure ()) 2 scheduler

private def embed (profile : ∀ who, source.BehavioralPolicy who) :
    ∀ who, target.BehavioralPolicy who := fun who info =>
  (profile who info).map (included.choice (PMF.pure ()) 2 scheduler who info)

/-- The extension genuinely permits a packet excluded by the smaller game. -/
theorem extra_packet (who : Bool) (past : List app.PlayerEntry) (view : app.PlayerView) :
    send true ∉ smaller.actions who past view ∧ send true ∈ larger.actions who past view := by
  classical
  simp [smaller, larger, send, silent]

/-- Every source policy, including randomized withholding, has the same complete continuation. -/
theorem arbitrary_policy_continuation (profile : ∀ who, source.BehavioralPolicy who)
    (fuel : Nat) (history : (smaller.protocol (PMF.pure ()) 2 scheduler).History) :
    (source.runBehavioralFrom profile fuel history).map restriction.history =
      target.runBehavioralFrom (embed profile) fuel (restriction.history history) := by
  apply restriction.runFrom_law profile (embed profile) _ fuel history
  intro who site
  rfl

/-- The initialized full state law also agrees, with no equilibrium premise. -/
theorem arbitrary_policy_state_law (profile : ∀ who, source.BehavioralPolicy who)
    (fuel : Nat) :
    (source.runBehavioral profile fuel).map History.state =
      (target.runBehavioral (embed profile) fuel).map History.state := by
  have law := restriction.initialized_law profile (embed profile) (by intro who site; rfl) fuel
  have projected := congrArg (PMF.map History.state) law
  rw [PMF.map_comp] at projected
  exact projected

/-- A pending-message observation is retained verbatim at every legal smaller-menu history. -/
theorem passive_read_retained
    (history : (smaller.protocol (PMF.pure ()) 2 scheduler).History)
    (who : Bool) (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : source.infoOf who history.trace = some (past, view))
    (packet : Message Bool Bool) (received : packet ∈ view.messages.leaked) :
    ∃ targetView, target.infoOf who (restriction.history history).trace =
      some (past, targetView) ∧ packet ∈ targetView.messages.leaked := by
  refine ⟨view, ?_, received⟩
  exact (restriction.observed who history).trans observed

/-- Both strict menu instances use ordinary decision recall, including off-path sites. -/
theorem both_have_decision_recall : source.DecisionRecall ∧ target.DecisionRecall :=
  ⟨smaller.decisionRecall (PMF.pure ()) 2 scheduler,
    larger.decisionRecall (PMF.pure ()) 2 scheduler⟩

end InteractionTests.ReactiveMenuRestriction
