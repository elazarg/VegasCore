/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateSettlement
import Vegas.Compile.SealedSettlement
import Vegas.Compile.SourceOutcomeExecution

/-! # Source settlement for arbitrary candidate-host executions

The public settlement proof depends on event provenance and completed reveals,
not on a private candidate table. It therefore applies to competing candidates,
accepted unopenable handles, malformed traffic, and timeout defaults in the
same generated program. This source witness need not preserve private choices
or the opponents' policy law; it is not a deviation simulation.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Every completed candidate-host policy run has exactly the programmed payout
of a legal written-source execution. All player and environment policies are
arbitrary; completion is an explicit premise and does not assert fairness. -/
theorem candidate_publicPayout_source
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (next :
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
        players environment schedule
        (PolicyExecution.initial _ (State.initial _
          (compilation.supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      compilation.publicPayout? next.native.application.visible.events =
        some (evalPayoffs (compile source.core).sourcePayoffs terminalEnv) := by
  apply compilation.publicPayout?_eq_source_of_complete nullValue window
    next.native.application.visible _ hcomplete
  exact (compilation.supported.resolvingRuntime nullValue window).runPolicies_candidate_publicEvents
    players environment schedule _ next (SealedResolution.PublicEventInvariant.initial _) hnext

/-- If an owned site times out in a completed candidate-host run, its actual
public payout has a legal source witness in which that owner chose the default.
The same witness establishes both facts; no openability or service premise is
assumed. This is a settlement witness, not an unchanged-opponents source law. -/
theorem candidate_publicPayout_source_choice
    (compilation : SealedCompilation source ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (next :
      (compilation.supported.resolvingRuntime
        nullValue window).candidateApplication.PolicyExecution)
    (hnext : next ∈
      ((compilation.supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
        players environment schedule
        (PolicyExecution.initial _ (State.initial _
          (compilation.supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (hcomplete : (compilation.supported.resolvingRuntime nullValue window).complete
      next.native.application.visible = true)
    (node : Fin (compile source.core).graph.nodeCount) (who : Player)
    (htimeout : node.val ∈ next.native.application.visible.timeouts)
    (howned : (∃ guard, ((compile source.core).graph.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L),
        ((compile source.core).graph.nodeRow node).sem =
          .reveal ((compile source.core).graph.nodeTarget producer) ∧
        ((compile source.core).graph.nodeRow producer).sem = .commit who guard) :
    ∃ final : VEnv L (sourceTerminalCtx source.core.prog),
      SmallStep.Star ⟨source.core.Γ, source.core.env, source.core.prog⟩
        ⟨sourceTerminalCtx source.core.prog, final, .ret (sourceTerminalPayoffs source.core.prog)⟩ ∧
      source.core.prog.Chooses who nullValue final ∧
      compilation.publicPayout? next.native.application.visible.events =
        some (evalPayoffs (sourceTerminalPayoffs source.core.prog) final) := by
  have hpublic :=
    (compilation.supported.resolvingRuntime nullValue window).runPolicies_candidate_publicEvents
      players environment schedule _ next (SealedResolution.PublicEventInvariant.initial _) hnext
  have hsettlement :=
    SealedResolution.runPolicies_candidate_settlementInvariant
      (compilation.supported.resolvingRuntime nullValue window)
      players environment schedule _ next (SealedResolution.SettlementInvariant.initial _) hnext
  obtain ⟨cfg, hterminal, hchoice, hpayout⟩ :=
    compilation.publicPayout_source_choice_of_timeout nullValue window
      next.native.application.visible hpublic hsettlement hcomplete node who htimeout howned
  exact ⟨_, decodeSourceOutcome_reachable source.core cfg hterminal, hchoice, hpayout⟩

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.candidate_publicPayout_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_publicPayout_source

/-- info: 'Vegas.SealedCompilation.candidate_publicPayout_source_choice' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.candidate_publicPayout_source_choice
