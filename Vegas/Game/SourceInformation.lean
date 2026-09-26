/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ObservationRecall
import Vegas.Source.SetupProtocolBehavioral
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Source decision depths and finite revelation histories

The existing source view identifies its instruction position. Thus every
decision information set has a common depth and is a history antichain,
without adding observations or requiring independent initial types.

For reveal-only programs, a fair Boolean policy has full support at every
source choice. Bounded execution then gives finitely many legal histories,
even when the ambient type or configuration carriers are infinite.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

/-- The existing public program position, with one step for the setup draw. -/
def decisionDepth (setup : Setup (Player := Player) (L := L)) (who : Player) :
    setup.ProtocolView who → Nat
  | none => 0
  | some view => SourceProgram.ProtocolView.position who setup.program view + 1

theorem decisionDepth_trace (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    {state : setup.ProtocolState} (trace : (setup.executionProtocol admission).Trace state) :
    setup.decisionDepth who ((setup.informationModel admission).infoOf who trace) =
      trace.length := by
  rw [show (setup.informationModel admission).infoOf who trace =
    setup.protocolObserve who state from setup.protocol_info admission who trace]
  have length := setup.protocol_history_length admission trace
  cases state with
  | none =>
      simp only [protocolRemaining] at length
      change 0 = trace.length
      omega
  | some state =>
      have position := SourceProgram.ProtocolView.position_add_remaining who setup.program state
      change SourceProgram.ProtocolView.position who setup.program
        (SourceProgram.ProtocolState.observe who setup.program state) + 1 = trace.length
      change trace.length + SourceProgram.ProtocolState.remaining setup.program state =
        instructionCount setup.program + 1 at length
      omega

theorem common_decision_depth (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (site : (setup.informationModel admission).InformationSite who) :
    InformationModel.InformationSite.CommonDepth (setup.informationModel admission) site
      (setup.decisionDepth who site.1) := by
  intro history
  exact (setup.decisionDepth_trace admission who history.1.trace).symm.trans
    (congrArg (setup.decisionDepth who) history.2)

theorem decision_antichain (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    (setup.informationModel admission).DecisionInformationAntichain := by
  intro who site first second joint legal next realized fuel path
  have lengths := path.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at lengths
  rw [setup.common_decision_depth admission who site first,
    setup.common_decision_depth admission who site second] at lengths
  omega

end Setup

namespace RevealOnly

/-- A fair legal policy for every reveal, including choices off equilibrium. -/
def uniformPolicy (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → program.RevealOnly → BehavioralPolicy who program
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample .., impossible => impossible.elim
  | _, _, .commit .., impossible => impossible.elim
  | _, _, .reveal _ _ _ _ _ _ next, reveals =>
      (fun _ _ => FinDist.uniformOfFintype (α := Bool), uniformPolicy who next reveals)

theorem uniformPolicy_admitted (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (reveals : program.RevealOnly) →
    (admission : CommitmentInterface program) →
      (uniformPolicy who program reveals).Admitted program admission
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample .., impossible, _ => impossible.elim
  | _, _, .commit .., impossible, _ => impossible.elim
  | _, _, .reveal _ _ _ _ _ _ next, reveals, admission =>
      uniformPolicy_admitted who next reveals admission

theorem uniformPolicy_support (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (reveals : program.RevealOnly) →
    (admission : CommitmentInterface program) → (view : ProtocolView who program) →
    (choice : Option (OwnAction Player L)) → ProtocolView.menu who program admission view choice →
      choice ∈ ((uniformPolicy who program reveals).protocolAction program view).support
  | _, _, .ret _, _, _, _, none, _ => FinDist.mem_support_pure.mpr rfl
  | _, _, .ret _, _, _, _, some _, legal => by
      have impossible : (none : Option Player) = some who := legal.1
      cases impossible
  | _, _, .sample .., impossible, _, _, _, _ => impossible.elim
  | _, _, .commit .., impossible, _, _, _, _ => impossible.elim
  | _, _, .reveal _ owner name _ _ _ next, reveals, admission, view, choice, legal => by
      cases view with
      | inr later => exact uniformPolicy_support who next reveals admission later choice legal
      | inl current =>
          by_cases own : owner = who
          · cases choice with
            | none =>
                simp only [ProtocolView.menu, ProtocolView.actor, Sum.elim_inl, own] at legal
                exact (legal rfl).elim
            | some action =>
                obtain ⟨_actor, disclose, rfl⟩ := legal
                simp only [uniformPolicy, BehavioralPolicy.protocolAction, Sum.elim_inl,
                  dite_eq_left own, FinDist.support_map, Set.mem_image]
                exact ⟨disclose, FinDist.mem_support_uniformOfFintype _, rfl⟩
          · cases choice with
            | none =>
                simp only [uniformPolicy, BehavioralPolicy.protocolAction, Sum.elim_inl,
                  dite_eq_right own, FinDist.mem_support_pure]
            | some action => exact (own (Option.some.inj legal.1)).elim

end RevealOnly

namespace Setup

def revealReference (setup : Setup (Player := Player) (L := L))
    (reveals : setup.program.RevealOnly) (admission : CommitmentInterface setup.program) :
    (setup.informationModel admission).BehavioralAssessment :=
  .ofStrategy fun who => setup.toProtocolBehavioralPolicy admission who
    (RevealOnly.uniformPolicy who setup.program reveals)
    (RevealOnly.uniformPolicy_admitted who setup.program reveals admission)

theorem revealReference_fullyMixed (setup : Setup (Player := Player) (L := L))
    (reveals : setup.program.RevealOnly) (admission : CommitmentInterface setup.program) :
    (setup.revealReference reveals admission).IsFullyMixed := by
  intro who site choice
  suffices choice.1 ∈ (((setup.revealReference reveals admission).strategy who site.1).map
      Subtype.val).support by
    obtain ⟨other, supported, same⟩ := FinDist.support_map .. ▸ this
    exact (Subtype.ext same) ▸ supported
  change choice.1 ∈ ((setup.toProtocolBehavioralPolicy admission who _ _ site.1).map
    Subtype.val).support
  rw [setup.toProtocolBehavioralPolicy_map_val]
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      change choice.1 ∈ (FinDist.pure none).support
      exact FinDist.mem_support_pure.mpr choice.2
  | some view =>
      exact RevealOnly.uniformPolicy_support who setup.program reveals admission view choice.1
        choice.2

/-- Finiteness includes every legal source history, regardless of the support
of a later chosen equilibrium. Correlated private initialization is retained. -/
theorem reveal_finite_history [Finite Player] (setup : Setup (Player := Player) (L := L))
    (reveals : setup.program.RevealOnly) (admission : CommitmentInterface setup.program) :
    Finite (setup.executionProtocol admission).History :=
  (setup.revealReference_fullyMixed reveals admission).finite_history
    (setup.protocol_bounded admission)

end Setup

end Vegas.SourceProgram
