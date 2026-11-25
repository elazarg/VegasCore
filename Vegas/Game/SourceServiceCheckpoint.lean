module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphCheckpoint
public import Vegas.Game.RevealService
public import Vegas.Pending.ExclusionCompletion

@[expose] public section

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Automatic service of a defaulted binding performs its existing typed source successor. -/
theorem SourceCheckpoint.commitAutomatic
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {owner : Player} {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ owner name payload)
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (eligible : native.AutomaticReady event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload)))) =
      some (.commit owner name payload none)) :
    SourceCheckpoint setup (commitSuccessor name guard source none)
      (refs.cons (name := name) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.completeAutomatic event eligible).config := by
  have next := checkpoint.commit (native := native.config) name guard event eventRank eligible.1
    outputEq before none decoded
  have output : (commitSuccessor name guard source none).state.get .here = .failure := by
    simp only [commitSuccessor, Env.get, Env.cons, ite_self, Option.getD_none]
  rw [output] at next
  simpa only [State.completeAutomatic, State.completeFailure, State.complete,
    nodeView_eq_bind outputEq codeEq]
    using next

/-- Automatic service of a defaulted publication performs its existing typed source successor. -/
theorem SourceCheckpoint.revealAutomatic
    {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
    {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup deps).layout Γ} {rank : Nat}
    {native : EventGraphRuntime.State (serviceGraph setup deps)}
    (checkpoint : SourceCheckpoint setup source refs rank native.config)
    {name : VarId} {owner : Player} {payload : L.Ty} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (event : (serviceGraph setup deps).EventId) (eventRank : event.val = rank)
    (eligible : native.AutomaticReady event)
    (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (decoded : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false) =
      some (.reveal owner name false)) :
    SourceCheckpoint setup (revealSuccessor published binding source false)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1)
      (native.completeAutomatic event eligible).config := by
  have next := checkpoint.reveal (native := native.config) published binding event eventRank
    eligible.1 outputEq before false decoded
  rw [disclosureResult_false] at next
  simpa only [State.completeAutomatic, State.completeFailure, State.complete,
    nodeView_eq_resolve outputEq codeEq]
    using next


end Vegas
