/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Pending.ReactiveOwnerWindow
import GameTheoryExtensions.Math.Probability.ObservedChoice

/-! # The deviator's choice in its own phase

In a phase of its own binding or guarded disclosure, a deviator within the
permitted menu chooses at some roster visit, from its complete native input.
Every other player is silent. The phase leaves the decoded source
configuration at a source successor of the phase's entry configuration, and the
deviator's native traffic at the end of the phase determines its new source
view. Its traffic at the end of the phase has a law that depends on the native
execution only through its traffic at the start.

Together with an entry factorization of that traffic through the deviator's
source view, this makes the deviator's source choice a behavioral choice of
its source view, and restores the factorization at the successor.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The owner's view after its commitment determines its view before and its
choice. -/
theorem commit_owner_view_reflects {Γ : SourceCtx Player L} {who : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ who name payload)
    (left right : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view who =
      (commitSuccessor name guard right second).view who) :
    left.view who = right.view who ∧ first = second := by
  constructor
  · calc left.view who = ((commitSuccessor name guard left first).view who).back
            (decide (who = who)) := (back_commit_view who name guard left first).symm
      _ = ((commitSuccessor name guard right second).view who).back (decide (who = who)) :=
          congrArg _ same
      _ = right.view who := back_commit_view who name guard right second
  · have cell := congrArg (fun view : DecisionView who ((name, .commitment who payload) :: Γ) =>
      view.1.cells.get .here) same
    simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons, ite_true] at cell
    exact Option.some.inj cell

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The owner's view after its guarded disclosure determines its view before
and its choice, which it records in its own history. -/
theorem reveal_owner_view_reflects {Γ : SourceCtx Player L} {name : VarId}
    {who : Player} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (left right : Config Player L Γ) (first second : Bool)
    (same : (revealSuccessor published selected left first).view who =
      (revealSuccessor published selected right second).view who) :
    left.view who = right.view who ∧ first = second := by
  refine ⟨reveal_view_reflects who published selected left right first second same, ?_⟩
  have last := congrArg (fun view : DecisionView who ((published, .publication payload) :: Γ) =>
    view.2.getLast?) same
  simp only [Config.view, revealSuccessor, Function.update_self, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, Option.some.injEq, OwnAction.reveal.injEq,
    true_and] at last
  exact last

omit [Fintype Player] in
/-- Equal deviator traffic gives equal deviator observations. -/
private theorem observe_eq_of_traffic (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (left right : (application setup leaks).Execution)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right) :
    left.observe (application setup leaks) who = right.observe (application setup leaks) who := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks]
  exact congrArg₂ (fun view evidence =>
    (⟨right.network.observe who, view, evidence⟩ : (application setup leaks).PlayerView))
    views receipts

end Vegas
