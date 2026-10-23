/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.LateLeak.SettleLateIntended
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Decision recall and equilibrium existence in the settle-late game

Every state records the path that reached it, and the joint action into a
state is determined by the state (`Vegas.settleLate_step_parent`). Each
player's own play is therefore a function of the state (`Vegas.settleLatePlay`).
At a decision it is a function of the player's view: the sender's views name
its earlier packets, and the listener's report names its raw packet. So the
game has decision recall, and, being finite, a sequential equilibrium.
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol

/-- What a player has played on the way to a state: its views when it moved and
its moves, latest first. -/
def settleLatePlay : LateLeakRole → SettleLateState → List (SettleLateView × SettleLateMove)
  | .sender, .afterProtected secret => [(.protectedTurn secret, .emit .opening)]
  | .sender, .protectedAnswer secret talk | .sender, .protectedDone secret talk _ =>
      [(.afterProtected secret, .emit (settleLateTalkPacket talk)),
        (.protectedTurn secret, .emit .opening)]
  | .sender, .firstLate secret early =>
      [(.protectedTurn secret, .emit (settleLateTalkPacket early))]
  | .sender, .watching secret early first | .sender, .secondLate secret early first _ =>
      [(.firstTurn secret early, .emit first.packet),
        (.protectedTurn secret, .emit (settleLateTalkPacket early))]
  | .sender, .answering record | .sender, .finished record _ =>
      [(.secondTurn record.secret record.early record.first.packet record.ping,
          .emit record.second),
        (.firstTurn record.secret record.early, .emit record.first.packet),
        (.protectedTurn record.secret, .emit (settleLateTalkPacket record.early))]
  | .listener, .protectedDone secret talk answer =>
      [(.protectedAsked secret.1 talk, .reply answer)]
  | .listener, .secondLate secret early first ping =>
      [(.watching early (first.glimpse secret.1), .ping ping)]
  | .listener, .answering record =>
      [(.watching record.early (record.first.glimpse record.secret.1), .ping record.ping)]
  | .listener, .finished record answer =>
      [(.asked record.report, .reply answer),
        (.watching record.early (record.first.glimpse record.secret.1), .ping record.ping)]
  | _, _ => []

/-- A player's own play along a trace is the play recorded by the state it
reaches. -/
theorem settleLate_ownPlay (G : SettleLateParameters) (late : Bool) (who : LateLeakRole) :
    ∀ {state : SettleLateState} (trace : (settleLateExecution G late).Trace state),
      (settleLateModel G late).ownPlay who trace = settleLatePlay who state
  | _, .start => by cases who <;> rfl
  | _, .extend (source := source) (target := target) prior joint legal realized => by
      have reached := settleLate_initial_not_reached source joint legal
      have earlier := settleLate_ownPlay G late who prior
      obtain ⟨rfl, rfl⟩ := settleLate_step_parent legal realized
      rw [InfoSignals.ownPlay_extend, earlier]
      cases target with
      | initial => exact (reached realized).elim
      | _ =>
          cases who <;>
            simp [settleLateLastJoint, settleLateLastMove, settleLateParent,
              SettleLateState.actor, settleLate_infoOf, settleLateView, settleLatePlay]

/-- At a decision, the play recorded by a state is determined by the player's
view of it. -/
theorem settleLatePlay_eq_of_view (late : Bool) {who : LateLeakRole}
    {first second : SettleLateState} {move : SettleLateMove}
    (menu : some move ∈ settleLateMenu late (settleLateView who first))
    (same : settleLateView who first = settleLateView who second) :
    settleLatePlay who first = settleLatePlay who second := by
  cases who <;> cases first <;> cases second <;>
    simp_all [settleLateView, settleLateMenu, settleLatePlay, SettleLateRecord.report]

/-- Each player's earlier views and moves are determined by its view at every
decision. -/
theorem settleLate_decisionRecall (G : SettleLateParameters) (late : Bool) :
    (settleLateModel G late).DecisionRecall := by
  intro who site first second
  obtain ⟨_, _, move, menu⟩ := site.2
  have firstView : settleLateView who first.1.state = site.1 := by
    rw [← settleLate_infoOf G late who first.1.trace]
    exact first.2
  have secondView : settleLateView who second.1.state = site.1 := by
    rw [← settleLate_infoOf G late who second.1.trace]
    exact second.2
  rw [settleLate_ownPlay, settleLate_ownPlay]
  rw [← firstView] at menu
  exact settleLatePlay_eq_of_view late menu (firstView.trans secondView.symm)

/-- The intended and the late settle-late game each have a sequential
equilibrium. -/
theorem settleLate_exists_sequentialEquilibrium (G : SettleLateParameters) (late : Bool) :
    ∃ A : (settleLateModel G late).BehavioralAssessment,
      A.IsSequentialEquilibrium (settleLate_antichain G late) (settleLate_terminates G late)
        (settleLatePayoff G late) := by
  let fallback : ∀ who, (settleLateModel G late).Policy who :=
    fun _ _ => Classical.choice inferInstance
  obtain ⟨A, rational, consistent⟩ := (settleLateModel G late).exists_sequentialEquilibrium
    (settleLate_decisionRecall G late) fallback (settleLatePayoff G late)
    (settleLate_terminates G late)
  exact ⟨A, rational, consistent⟩

end Vegas
