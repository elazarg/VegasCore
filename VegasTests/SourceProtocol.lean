/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolEvaluation
import Vegas.Expr.Simple
import GameTheory.Protocol.SubgamePerfect

/-! # Mixed commitment admission on the actual source protocol

Alice binds a Boolean and Bob binds an integer; both are then disclosed.
The same program admits four commitment interfaces, without changing either
its instructions or its observation functions.
-/

noncomputable section

namespace VegasTests.SourceProtocol

open Vegas Vegas.SourceProgram GameTheory.Protocol GameTheory.Math.Probability

private def acceptAll {Γ : SourceCtx Bool simpleExpr} (owner : Bool)
    (name : VarId) (payload : simpleExpr.Ty) : SourceGuard simpleExpr Γ owner name payload where
  schema := []
  schemaNames := by simp
  subjectFresh := by simp
  code := .constBool true
  reads := fun member => nomatch member

def program : SourceProgram Bool simpleExpr [] ∅ :=
  .commit 0 false (by decide) (acceptAll false 0 .bool) <|
  .commit 1 true (by decide) (acceptAll true 1 .int) <|
  .reveal 2 false 0 (by decide) (.there .here) (by decide) <|
  .reveal 3 true 1 (by decide) (.there .here) (by decide) <|
  .ret []

def interface (alice bob : CommitmentAdmission) : CommitmentInterface program
  | none => alice
  | some none => bob
  | some (some impossible) => nomatch impossible

private def initial : Config Bool simpleExpr [] :=
  ⟨Env.empty _, [], Revelations.initial [], fun _ => []⟩

def game (alice bob : CommitmentAdmission) :=
  executionProtocol program (interface alice bob) initial

private def afterA (choice : PublicationResult Bool) : ProtocolState program :=
  Sum.inr (Sum.inl (commitSuccessor 0 (acceptAll false 0 .bool) initial choice))

private def submitA (choice : PublicationResult Bool) : Bool → Option (OwnAction Bool simpleExpr)
  | false => some (.commit false 0 .bool choice)
  | true => none

theorem legal_first (alice bob : CommitmentAdmission) (choice : PublicationResult Bool)
    (admitted : alice.Admits choice) :
    (game alice bob).Legal (game alice bob).init (submitA choice) := by
  refine ⟨by simp [game, executionProtocol, ProtocolState.entry,
    ProtocolState.terminal, program], ?_⟩
  intro who
  cases who with
  | false =>
      exact ⟨rfl, choice, admitted, rfl⟩
  | true => simp [game, executionProtocol, ProtocolState.entry, ProtocolState.observe,
      ProtocolView.actor, program, submitA]

theorem first_step (alice bob : CommitmentAdmission) (choice : PublicationResult Bool)
    (admitted : alice.Admits choice) :
    (game alice bob).step (game alice bob).init
        ⟨submitA choice, legal_first alice bob choice admitted⟩ =
      FinDist.pure (afterA choice) := by
  simp [game, executionProtocol, program, ProtocolState.entry, ProtocolState.step,
    submitA, afterA]

def firstHistory (alice bob : CommitmentAdmission) (choice : PublicationResult Bool)
    (admitted : alice.Admits choice) : (game alice bob).Trace (afterA choice) :=
  .extend .start (submitA choice) (legal_first alice bob choice admitted)
    (by rw [first_step alice bob choice admitted]; exact FinDist.mem_support_pure.mpr rfl)

/-- Forfeiture at A is an actual legal history when that site admits it. -/
example : Nonempty ((game .forfeiture .values).Trace (afterA .failure)) :=
  ⟨firstHistory .forfeiture .values .failure rfl⟩

/-- The same packet is excluded by the value-only interface at A. -/
example : ¬ (game .values .forfeiture).Legal
    (game .values .forfeiture).init (submitA .failure) := by
  intro legal
  have available := (game .values .forfeiture).legalOption_of_legal legal false
  simp [LegalOption, game, executionProtocol, program, ProtocolState.entry,
    ProtocolState.observe, ProtocolView.actor, ProtocolView.available, submitA, interface,
    CommitmentAdmission.Admits] at available

/-- Changing Alice's hidden choice does not change Bob's source information. -/
theorem hidden_from_bob (first second : PublicationResult Bool) :
    ProtocolState.observe true program (afterA first) =
      ProtocolState.observe true program (afterA second) := by
  change Sum.inr (Sum.inl _) = Sum.inr (Sum.inl _)
  congr 2
  apply Prod.ext
  · change SourceObservation.mk _ = SourceObservation.mk _
    congr 1
    funext name cell member
    cases member with
    | here => rfl
    | there impossible => nomatch impossible
  · rfl

private def historyAfterA (choice : PublicationResult Bool) :
    (game .forfeiture .values).History :=
  ⟨afterA choice, firstHistory .forfeiture .values choice
    (by cases choice <;> simp [CommitmentAdmission.Admits])⟩

/-- A complete machine state is not automatically a proper subgame root.
Bob's decision information set crosses the boundary of this hidden-failure
prefix, so canonical SPE does not impose a separate optimum there. -/
theorem failed_prefix_not_subgame :
    ¬ (informationModel program (interface .forfeiture .values) initial).IsSubgameRoot
      (historyAfterA .failure) := by
  intro proper
  have indistinguishable :
      (protocolSignals program (interface .forfeiture .values) initial).infoOf true
          (historyAfterA .failure).trace =
        (protocolSignals program (interface .forfeiture .values) initial).infoOf true
          (historyAfterA (.success false)).trace :=
    hidden_from_bob .failure (.success false)
  have reached := proper true (historyAfterA .failure) (historyAfterA (.success false))
    (ExecutionProtocol.HistoryReaches.refl _ _) (by intro impossible; exact impossible)
    rfl (by intro impossible; exact impossible) rfl indistinguishable
  obtain ⟨fuel, path⟩ := reached
  have equal := path.eq_of_trace_length_eq rfl
  have states := congrArg ExecutionProtocol.History.state equal
  have configs := Sum.inl.inj (Sum.inr.inj states)
  have bindings := congrArg
    (fun config : Config Bool simpleExpr [(0, .commitment false .bool)] => config.state.get .here)
    configs
  cases bindings

/-- Bob cannot infer forfeiture from a changed menu either. -/
example (alice bob : CommitmentAdmission) (first second : PublicationResult Bool)
    (action : Option (OwnAction Bool simpleExpr)) :
    ProtocolView.menu true program (interface alice bob)
        (ProtocolState.observe true program (afterA first)) action ↔
      ProtocolView.menu true program (interface alice bob)
        (ProtocolState.observe true program (afterA second)) action := by
  rw [hidden_from_bob first second]

/-- The second site's admission is independent of the first site's choice. -/
example (alice : CommitmentAdmission) (first : PublicationResult Bool) :
    ¬ (game alice .values).Legal (afterA first)
      (fun who => if who then some (.commit true 1 .int .failure) else none) := by
  intro legal
  have available := (game alice .values).legalOption_of_legal legal true
  simp [LegalOption, game, executionProtocol, program, ProtocolState.observe,
    ProtocolView.actor, ProtocolView.available, afterA, interface,
    CommitmentAdmission.Admits] at available

example (alice bob : CommitmentAdmission) : (game alice bob).BoundedHorizon 4 :=
  protocol_bounded program (interface alice bob) initial

example (alice bob : CommitmentAdmission) : (game alice bob).WellFoundedPlay :=
  protocol_terminates program (interface alice bob) initial

end VegasTests.SourceProtocol
