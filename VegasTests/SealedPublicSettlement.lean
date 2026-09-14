/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicOutcome

/-! # Public settlement after a sealed timeout

This checked source pays from its public reveal.  The concrete native state
retains a different private registration when the reveal deadline expires, so
settlement must use the public default rather than inspect that registration.
-/

noncomputable section

namespace VegasTests.SealedPublicSettlement

open Vegas Vegas.EventGraph Interaction

abbrev Player := Fin 1
abbrev Value := Option Bool

def payoff : Expr [(1, .option .bool)] .int :=
  .ite (.isSome (.var 1 .here)) (.constInt 7) (.constInt (-3))

theorem payoff_depends_on_public_value :
    evalExpr payoff (Env.cons none (Env.empty Val)) = -3 ∧
      evalExpr payoff (Env.cons (some true) (Env.empty Val)) = 7 := by
  exact ⟨rfl, rfl⟩

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.reveal 1 0 0 .here (.ret [(0, payoff)]))

def source : WFProgram Player simpleExpr where
  core := {
    Γ := []
    prog := core
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [core, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete core
    (by simp [core, FreshBindings, Fresh]) [] (by simp) (by decide)
  legal := by
    unfold core
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · trivial

abbrev compiled := ToEventGraph.compile source.core
abbrev graph := compiled.graph

def node (index : Fin 2) : Fin graph.nodeCount := index

theorem supported : SealedFragment graph (.option .bool) where
  graphWF := compiled.graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by
    fin_cases node <;> cases hsem
    rfl
  commitGuard node who guard hsem value env := by
    fin_cases node <;> cases hsem
    cases value <;> rfl
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩

theorem compilation : SealedCompilation source (.option .bool) := ⟨supported⟩

abbrev runtime := supported.resolvingRuntime none 2

def registered : SealedResolution.ApplicationState Player Value :=
  { runtime.initial with
    service := (runtime.initial.service.sealValue 0 0 (some true)).state }

def accepted :=
  (runtime.handle registered ⟨(0, 0), .commitment 0 (0, 0)⟩).getD registered

def settled := runtime.tick (runtime.tick accepted)

theorem acceptance :
    runtime.handle registered ⟨(0, 0), .commitment 0 (0, 0)⟩ = some accepted := rfl

/-- The accepted commitment retains `some true`, while its reveal times out to
public `none`. -/
theorem concrete_timeout_settlement :
    settled.service.lookup (0, 0) = some (some true) ∧
      settled.visible.timeouts = [1] ∧
      settled.visible.events = [.accepted 0 (0, 0), .opened 1 none] ∧
      runtime.complete settled.visible = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem public_store_default :
    Store.getAs (graph.publicSealedStore (.option .bool) settled.visible.events)
      1 (.option .bool) = some none := by
  have hevents : settled.visible.events = [.accepted 0 (0, 0), .opened 1 none] := rfl
  have htarget : graph.nodeTarget 1 = 1 := rfl
  rw [hevents]
  simp [Graph.publicSealedStore, Graph.replayPublicOpenings, Store.getAs, Store.set,
    TypedValue.as?, htarget]

private def defaultTerminalEnv : VEnv simpleExpr compiled.terminalCtx :=
  VEnv.cons none (VEnv.cons (some true) (VEnv.empty simpleExpr))

/-- The public evaluator follows the opened default, not the retained private
registration, and selects the programmed `-3` branch. -/
theorem public_payout_uses_default :
    (compilation.publicPayout? settled.visible.events).map (fun payout => payout 0) =
      some (-3) := by
  let store := graph.publicSealedStore (.option .bool) settled.visible.events
  have hinvariant : SealedResolution.EventInvariant runtime settled :=
    (((SealedResolution.EventInvariant.initial (runtime := runtime)).register
      0 0 (some true)).handle _ acceptance).tick.tick
  have hcomplete : runtime.complete settled.visible = true := rfl
  have hpayoff :
      evalPayoffs? compiled.payoffs store =
        some (evalPayoffs compiled.sourcePayoffs defaultTerminalEnv) := by
    rw [compiled.payoffs_eq]
    apply ToEventGraph.evalPayoffs?_compilePayoffs_eq_source
    intro entry hentry
    change entry ∈ [(0, payoff)] at hentry
    simp only [List.mem_singleton] at hentry
    subst entry
    let eventPayoff := ToEventGraph.eventPayoffOf compiled.terminalState payoff
    have hmem : (0, eventPayoff) ∈ compiled.payoffs := by
      rw [compiled.payoffs_eq]
      change (0, eventPayoff) ∈
        ToEventGraph.compilePayoffs compiled.terminalState [(0, payoff)]
      simp [ToEventGraph.compilePayoffs, eventPayoff]
    have available : ∀ ref, ref ∈ eventPayoff.reads →
        ∃ value, Store.getAs store ref.field ref.ty = some value := by
      intro ref href
      exact supported.publicSealedStore_available_of_complete none 2 settled hinvariant
        hcomplete ref (compiled.payoffsWF (0, eventPayoff) hmem ref href).1
    let readEnv := ReadEnv.ofStore store eventPayoff.reads available
    refine ⟨readEnv, ?_, ?_⟩
    · unfold ReadEnv.ofStore?
      rw [dif_pos available]
    · intro name ty hvar hdependency
      cases hvar with
      | here =>
          have hread := ReadEnv.ofStore_read store eventPayoff.reads available
            (ToEventGraph.exprReadRefs_mem compiled.terminalState payoff .here hdependency)
          change Store.getAs store 1 (.option .bool) = some
            (ToEventGraph.sourceValuePub compiled.terminalState readEnv .here _) at hread
          change ToEventGraph.sourceValuePub compiled.terminalState readEnv .here _ = none
          exact Option.some.inj (hread.symm.trans public_store_default)
      | there htail => cases htail
  unfold SealedCompilation.publicPayout?
  change Option.map (fun payout => payout 0) (evalPayoffs? compiled.payoffs store) = _
  rw [hpayoff]
  rfl

/-- Public timeout settlement is the payout of a legal written-source run,
without asking settlement to decode the retained private registration. -/
theorem timeout_settlement_has_source_execution :
    ∃ terminalEnv : VEnv simpleExpr compiled.terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      compilation.publicPayout? settled.visible.events =
        some (evalPayoffs compiled.sourcePayoffs terminalEnv) := by
  have hinvariant : SealedResolution.EventInvariant runtime settled :=
    (((SealedResolution.EventInvariant.initial (runtime := runtime)).register
      0 0 (some true)).handle _ acceptance).tick.tick
  obtain ⟨terminalEnv, hsource, hpayout⟩ :=
    compilation.publicPayout?_eq_source_of_complete none 2 settled hinvariant rfl
  exact ⟨terminalEnv, hsource, hpayout⟩

end VegasTests.SealedPublicSettlement

/-- info: 'VegasTests.SealedPublicSettlement.timeout_settlement_has_source_execution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPublicSettlement.timeout_settlement_has_source_execution
