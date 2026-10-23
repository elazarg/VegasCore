/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredPolicy
import Vegas.Game.SourceServiceDecidedCompletion

/-! # First-turn clients from executions reached by any players

The first-turn clients of a source profile on the default runtime
(`Vegas.firstTurnClients`) can continue an execution that any players reached
through the anchored profile, which replays the reaching players up to the
anchor and is the clients from there on
(`Interaction.ReactiveApplication.anchoredPolicy`). An execution continues an
anchor when every recall extends the anchor's and every own submission was made
at its author's turn (`Vegas.ContinuesAnchor`). Rounds of the anchored
first-turn clients keep an execution continuing its anchor
(`Vegas.ContinuesAnchor.runRounds`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The first-turn clients of a source profile on the default runtime. -/
abbrev firstTurnClients (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) : Player → (application setup leaks).Policy :=
  serviceTurnPolicy setup .sequential (rankDeadline setup .sequential) leaks bound turns
    (firstTurnTiming setup turns .sequential) profile

variable (setup leaks) in
/-- An execution continuing an anchor: every recall extends the anchor's, and
every own submission was made at its author's turn. -/
def ContinuesAnchor (anchor execution : (application setup leaks).Execution) : Prop :=
  (∀ who, anchor.recall who <+: execution.recall who) ∧
    ∀ who, OwnSubmissionsAtTurn setup leaks execution who

/-- A round of the anchored first-turn clients keeps an execution continuing
its anchor. -/
theorem ContinuesAnchor.round {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat} {profile : BehavioralProfile setup.program}
    {anchor execution next : (application setup leaks).Execution}
    (holds : ContinuesAnchor setup leaks anchor execution)
    (moved : next ∈ ((application setup leaks).round scheduler
      (ReactiveApplication.anchoredPolicy anchor (firstTurnClients setup leaks bound turns profile))
      execution).support) :
    ContinuesAnchor setup leaks anchor next := by
  let app := application setup leaks
  obtain ⟨command, _, middle, stepped, cases⟩ := round_cases setup leaks moved
  have recallEq := app.environmentStep_recall execution middle command stepped
  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
  · refine ⟨fun who => ?_, fun who entry member => ?_⟩
    · rw [recallEq]
      exact holds.1 who
    · rw [recallEq] at member
      exact holds.2 who entry member
  · have follows : ReactiveApplication.anchoredPolicy anchor
        (firstTurnClients setup leaks bound turns profile) responder (middle.recall responder)
        (middle.observe app responder) =
        firstTurnClients setup leaks bound turns profile responder (middle.recall responder)
          (middle.observe app responder) :=
      ReactiveApplication.anchoredPolicy_of_extends anchor _ responder _ _
        (by rw [recallEq]; exact holds.1 responder)
    rw [follows] at chosen
    refine ⟨fun who => ?_, fun who entry member event submitted => ?_⟩
    · by_cases same : who = responder
      · subst same
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
        rw [recalled, recallEq]
        exact (holds.1 who).trans (List.prefix_append _ _)
      · rw [app.respond_recall_other middle responder who same response, recallEq]
        exact holds.1 who
    · by_cases same : who = responder
      · subst same
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
        rw [recalled] at member
        rcases List.mem_append.mp member with prior | fresh
        · rw [recallEq] at prior
          exact holds.2 who entry prior event submitted
        · rw [List.mem_singleton] at fresh
          subst fresh
          exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns _ profile who _ _
            response chosen event submitted
      · rw [app.respond_recall_other middle responder who same response, recallEq] at member
        exact holds.2 who entry member event submitted

/-- Rounds of the anchored first-turn clients keep an execution continuing its
anchor. -/
theorem ContinuesAnchor.runRounds {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {turns : Nat} {profile : BehavioralProfile setup.program}
    {anchor : (application setup leaks).Execution} :
    ∀ (count : Nat) (execution : (application setup leaks).Execution),
      ContinuesAnchor setup leaks anchor execution →
      ∀ final ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (firstTurnClients setup leaks bound turns profile)) count execution).support,
        ContinuesAnchor setup leaks anchor final := by
  intro count
  induction count with
  | zero =>
      intro execution holds final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact holds
  | succ count ih =>
      intro execution holds final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (holds.round moved) final rest

end Vegas
