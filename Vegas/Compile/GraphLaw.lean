/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphPolicy
import Vegas.Compile.GraphStepLaw
import Vegas.Compile.GraphStateLaw

/-! # Exact execution law for source-to-graph compilation

One induction covers all source constructs and arbitrary observation-local
policies. The policy retraction then gives deviation correspondence without
another execution induction.
-/

noncomputable section
namespace Vegas.SourceProgram

open Interaction GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

@[simp] theorem decodeDecisionView_observe {who : Player} {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (env : VEnv L (graphCtx Γ))
    (history : Graph.History Player L) :
    decodeDecisionView map (Graph.observe who env, history who) =
      (sourceObserve who (decodeState map env), decodeHistory history who) := by
  simp [decodeDecisionView, decode_observe, decodeHistory]

/-- Exact law at every compiler checkpoint, including arbitrary retained
guards, private bindings, publication references, and own-action histories. -/
theorem compileGraph_runWith {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (unique : (Γ.map Prod.fst).Nodup) (map : PublicationMap (R := R) Γ)
      (registry : Registry Γ) (profile : BehavioralProfile program)
      (env : VEnv L (graphCtx Γ)) (history : Graph.History Player L),
    (Graph.runWith (compileGraph program unique map registry)
      (fun who => compileGraphPolicy program unique map registry who (profile who))
      env history).map (decodeState (terminalMap program unique map)) =
    runWith program profile (decodeState map env) registry (decodeHistory history) := by
  induction program with
  | ret payoffs =>
      intro unique map registry profile env history
      simp [compileGraph, Graph.runWith, terminalMap, runWith]
  | sample name fresh law next ih =>
      intro unique map registry profile env history
      dsimp only [terminalCtx]
      simp only [compileGraph, Graph.runWith, compileGraphPolicy, terminalMap,
        runWith, FinDist.map_bind, compilePublicDist_eval law map env]
      unfold Graph.afterSample afterSample
      apply FinDist.bind_congr
      intro value _
      simpa only [decodeState_sample] using
        ih (by simp [fresh, unique]) (weakenMap map) registry.weaken
          (fun who => profile who) (VEnv.cons value env) history
  | commit name owner fresh guard next ih =>
      intro unique map registry profile env history
      dsimp only [terminalCtx]
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      simp only [compileGraph, Graph.runWith, compileGraphPolicy, terminalMap,
        runWith, FinDist.map_bind, Graph.bindKernel, commitKernel,
        decodeDecisionView_observe, FinDist.bind_map]
      unfold Graph.afterBind afterCommit
      apply FinDist.bind_congr
      intro choice _
      simpa only [decodeState_bind, decodeHistory_update_append, decodeOwnAction,
        Equiv.symm_apply_apply, obligation] using
        ih (by simp [fresh, unique]) (weakenMap map)
          (obligation :: registry.weaken)
          (fun who => (profile who).2)
          (VEnv.cons ((R.valueEquiv _).symm (BoundValue.resultEquiv _ choice)) env)
          (Function.update history owner
            (history owner ++
              [Graph.OwnAction.bind owner name _ (BoundValue.resultEquiv _ choice)]))
  | reveal published owner name fresh source unresolved next ih =>
      intro unique map registry profile env history
      dsimp only [terminalCtx]
      simp only [compileGraph, Graph.runWith, compileGraphPolicy, terminalMap,
        runWith, FinDist.map_bind, Graph.resolveKernel, revealKernel,
        decodeDecisionView_observe]
      unfold Graph.afterResolve afterReveal
      apply FinDist.bind_congr
      intro disclose _
      have law := ih (by simp [fresh, unique]) (resolveMap map unique source) registry.weaken
          (fun who => (profile who).2)
          (VEnv.cons ((R.valueEquiv _).symm
            (Graph.acceptedResult (outputName := published) (fieldRef source)
              (registry.weaken.map (compileGuard (resolveMap map unique source)))
              env disclose)) env)
          (Function.update history owner
            (history owner ++ [Graph.OwnAction.resolve owner name disclose]))
      rw [decodeState_resolve, decodeHistory_update_append] at law
      simpa only [compile_acceptedResult, decodeOwnAction] using law

def Initial.compileGraphProfile (source : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile source.program) : Graph.BehavioralProfile source.graph :=
  fun who => compileGraphPolicy source.program source.namesNodup initialMap [] who (profile who)

/-- Full terminal-state law for every checked source program and every profile. -/
theorem Initial.graph_honest_law (source : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile source.program) :
    (Graph.run source.graph (source.compileGraphProfile profile) source.graphInputs).map
      source.decodeGraph = source.run profile := by
  change (Graph.runWith (compileGraph source.program source.namesNodup initialMap [])
    (fun who => compileGraphPolicy source.program source.namesNodup initialMap [] who (profile who))
    (encodeState source.state) (fun _ => [])).map
    (decodeState (terminalMap source.program source.namesNodup initialMap)) =
      runWith source.program profile source.state [] (fun _ => [])
  have law := compileGraph_runWith source.program source.namesNodup initialMap [] profile
    (encodeState source.state) (fun _ => [])
  rw [decodeState_encodeState_initial source.state source.privatePending] at law
  exact law

/-- Payout compilation follows from the full state law and checked expression
lowering; payout is a projection, not the definition of game utility. -/
theorem Initial.graph_payoff_law (source : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile source.program) :
    (Graph.run source.graph (source.compileGraphProfile profile) source.graphInputs).map
        (Graph.evaluatePayoffs source.graph) =
      (source.run profile).map source.program.evaluatePayoffs := by
  have law := congrArg (FinDist.map source.program.evaluatePayoffs)
    (source.graph_honest_law profile)
  rw [FinDist.map_comp] at law
  rw [← law]
  congr 1
  funext env
  exact compileGraph_evaluatePayoffs source.program source.namesNodup initialMap [] env

end Vegas.SourceProgram
