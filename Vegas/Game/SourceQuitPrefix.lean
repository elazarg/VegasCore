/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Core.SourceQuitPrefix
import Vegas.Compile.SourceOutcomeExecution
import Vegas.Compile.SourceQuitPrefix
import Vegas.Game.SourceGraph

/-! # Source prefix dominance for public graph utilities

The source condition compares legal terminal continuations at one source
decision.  Source/graph correspondence supplies the continued source support,
while compiler field allocation turns agreement on public graph choice reads
into agreement on the recorded public source prefix.
-/

noncomputable section

namespace Vegas.WFProgram

open EventGraph ToEventGraph GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Prefix-relative source quitting dominance bounds the corresponding pair of
terminal graph utilities under a proved source interpretation. The compared
stores need agree only on public references in the decision's choice footprint. -/
theorem graphUtility_le_of_source_quitPrefix
    (source : WFProgram P L) {ty : L.Ty} (nullValue : L.Val ty)
    (sourceUtility : VEnv L (sourceTerminalCtx source.core.prog) → P → ℝ)
    (graphUtility : (compile source.core).graph.PublicUtility)
    (hterminalUtility : ∀ (cfg : ReachableConfig (compile source.core).graph)
      (hterminal : Terminal (compile source.core).graph cfg.1) (who : P),
      graphUtility.eval cfg.1.store who = sourceUtility
        (decodeSourceOutcome source.core.prog source.core.fresh
          (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
          cfg hterminal) who)
    (sourceProfile : SourceBehavioralProfile source.core.prog)
    (hdominance : source.core.prog.QuitPrefixDominanceAgainst
      source.core.env nullValue sourceUtility sourceProfile)
    (who : P) (alternative : CommitPolicy (compile source.core).graph who)
    (quitting continued : ReachableConfig (compile source.core).graph)
    (hcontinued : continued ∈
      ((policyGame (compile source.core).graph (compile source.core).graphWF
        (compile_guardLive source.core source.legal)).play
        (Profile.update (source.sourceGraphSimulation.compileProfile sourceProfile)
          who alternative)).support)
    (hquittingTerminal : Terminal (compile source.core).graph quitting.1)
    (producer : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hproducer : ((compile source.core).graph.nodeRow producer).sem =
      .commit who guard)
    (hquitValue : quitting.1.store ((compile source.core).graph.nodeTarget producer) =
      some (⟨ty, nullValue⟩ : TypedValue L))
    (hagrees : ∀ ref, ref ∈ guard.choiceReads →
      (compile source.core).graph.fieldRefPublic ref →
      Store.getAs quitting.1.store ref.field ref.ty =
        Store.getAs continued.1.store ref.field ref.ty) :
    graphUtility.eval quitting.1.store who ≤ graphUtility.eval continued.1.store who := by
  let state := BuildState.fromInitial
    (initialState source.core.Γ source.core.env source.core.wctx)
  have hcontinuedTerminal := runPolicyNodes_terminal (compile source.core).graphWF
    (compile_guardLive source.core source.legal)
    (Profile.update (source.sourceGraphSimulation.compileProfile sourceProfile)
      who alternative)
    ⟨Config.initial _, .initial⟩ (compile source.core).graph.nodeOrder
    (compile source.core).graph.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) continued hcontinued
  obtain ⟨actor, Δ, name, choiceTy, sourceGuard, site, hindex, hrow⟩ :=
    compileCore_commitNode_covered source.core.prog source.core.fresh state producer
      (by simp [state])
      ⟨_, who, guard, (compile source.core).graph.nodes_get?_nodeRow producer, hproducer⟩
  have hrowEq := Option.some.inj
    (((compile source.core).graph.nodes_get?_nodeRow producer).symm.trans hrow)
  have hcommit : NodeSem.commit who guard =
      NodeSem.commit actor
        (eventGuardOf (decisionSiteState site source.core.fresh state) actor sourceGuard) :=
    hproducer.symm.trans (congrArg EventNode.sem hrowEq)
  have hactor := (NodeSem.commit.inj hcommit).1
  subst actor
  have hguard := (NodeSem.commit.inj hcommit).2
  subst guard
  let quittingFinal := decodeSourceOutcome source.core.prog source.core.fresh state
    quitting hquittingTerminal
  let continuedFinal := decodeSourceOutcome source.core.prog source.core.fresh state
    continued hcontinuedTerminal
  have hrecord := decisionSite_recorded_value site source.core.fresh state
    quitting hquittingTerminal
  rw [← decisionSite_nodeTarget site source.core.fresh state producer hindex] at hrecord
  have htyped := Option.some.inj (hrecord.symm.trans hquitValue)
  have htype : choiceTy = ty := congrArg TypedValue.ty htyped
  subst ty
  have hquit : (site.recorded quittingFinal).get .here = nullValue := by
    exact eq_of_heq (TypedValue.mk.inj htyped).2
  have hobservation : observeSourceOutcome source.core continued ∈
      ((denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) sourceProfile who
          (backtranslateCommitPolicy source.core who alternative))
        source.core.env).map some).support :=
    (runPolicyNodes_source_deviation source.core source.legal sourceProfile who alternative) ▸
      ((FinDist.support_map _ _).symm ▸ ⟨continued, hcontinued, rfl⟩)
  rw [observeSourceOutcome_of_terminal source.core continued hcontinuedTerminal]
    at hobservation
  simp only [FinDist.support_map, Set.mem_image, Option.some.injEq] at hobservation
  obtain ⟨sourceFinal, hsourceFinal, heq⟩ := hobservation
  have hcontinuedSource : continuedFinal ∈
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) sourceProfile who
          (backtranslateCommitPolicy source.core who alternative))
        source.core.env).support := by
    simpa only [continuedFinal, state] using heq ▸ hsourceFinal
  have hprefix : (site.recorded quittingFinal).tail.erasePubEnv =
      (site.recorded continuedFinal).tail.erasePubEnv := by
    exact site.recorded_tail_erasePubEnv_eq_of_choiceReads_eq source.core.fresh state
      quitting continued hquittingTerminal hcontinuedTerminal hagrees
  have hsourceBound := hdominance who Δ name sourceGuard site
    (backtranslateCommitPolicy source.core who alternative)
    quittingFinal continuedFinal
    (decodeSourceOutcome_reachable source.core quitting hquittingTerminal)
    hquit hcontinuedSource hprefix
  rw [hterminalUtility quitting hquittingTerminal who,
    hterminalUtility continued hcontinuedTerminal who]
  exact hsourceBound

end Vegas.WFProgram

/-- info: 'Vegas.WFProgram.graphUtility_le_of_source_quitPrefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.graphUtility_le_of_source_quitPrefix
