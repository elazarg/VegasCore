/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReplay
import Vegas.Compile.SealedDisclosureRun

/-! # Written-source policies extracted from accepted candidates

One fixed pair of native response functions determines a legal source policy
at every source decision. The compiler's declared source reads supply the
earlier disclosed values used by acceptance replay. At matching source views,
the action is exactly the selected candidate's opening, or the legal fallback
if no opening is available. Complete source realizations discharge that
input-agreement premise while retaining the original opponent policies. Their
replayed native executions do not yet have a proved joint deviation law.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (MessageApplication.EnvironmentEntry
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication) →
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).candidateApplication)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- A legal written-source replacement constructed from acceptance replay.
Native histories, clocks, and pending pools are not source-policy inputs. -/
def extractedCandidateSourcePolicy : SourceBehavioralPolicy source.core.prog focal :=
  compilation.sourcePolicyOfDisclosures focal fun decision visible =>
    compilation.supported.extractedCandidateChoice nullValue window focal deviator environment
      schedule decision visible fallback

/-- At matching declared source observations, the compiled source replacement
chooses the opening of the candidate actually selected at acceptance. Missing
or unopenable selections use the supplied fallback. No runtime preparation or
submission discipline is assumed of the deviator. -/
theorem extractedCandidateSourcePolicy_law
    (values : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : compilation.disclosureInputs focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal
      (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
        schedule fallback) decision guard hdecision reads).map
        (fun value => cast
          (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure (SealedFragment.candidateValue
        (compilation.supported.candidateSelection nullValue window values focal
          deviator environment schedule decision) fallback) := by
  unfold extractedCandidateSourcePolicy
  rw [compile_sourcePolicyOfDisclosures]
  simp only [commitPolicyOfDisclosures, FinDist.map_pure, cast_cast, cast_eq, hinputs]
  rw [compilation.supported.extractedCandidateChoice_eq_selection nullValue window values focal
    deviator environment schedule decision guard hdecision fallback]

variable [Fintype Player]

/-- Complete source execution with the extracted candidate policy replacing
only the focal player. Opponent kernels are unchanged. -/
def extractedCandidateSourceRun (profile : SourceBehavioralProfile source.core.prog) :
    FinDist (ReachableConfig (compile source.core).graph) :=
  compilation.sourceRunOfDisclosures focal
    (fun decision visible => compilation.supported.extractedCandidateChoice nullValue window
      focal deviator environment schedule decision visible fallback) profile

theorem extractedCandidateSourceRun_source (profile : SourceBehavioralProfile source.core.prog) :
    (compilation.extractedCandidateSourceRun nullValue window focal deviator environment schedule
      fallback profile).map (observeSourceOutcome source.core) =
      (denoteSource source.core.prog
        (Profile.update (sig := sourceGameSignature source.core.prog) profile focal
          (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
            schedule fallback)) source.core.env).map some :=
  compilation.sourceRunOfDisclosures_source focal _ profile

/-- Every supported complete source realization agrees with the candidate
selected by replay of its honest values. The source-input agreement premise
of the local action law is discharged by the source execution itself. This
does not yet identify the probability law of the replayed native executions. -/
theorem extractedCandidateSourceRun_consistent (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator
      environment schedule fallback profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard) :
    cfg.1.nodeValues fallback decision = SealedFragment.candidateValue
      (compilation.supported.candidateSelection nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule decision) fallback := by
  have hchoice := compilation.sourceRunOfDisclosures_consistent focal
    (fun index visible => compilation.supported.extractedCandidateChoice nullValue window
      focal deviator environment schedule index visible fallback)
    profile fallback cfg hcfg decision guard hdecision
  exact hchoice.trans (compilation.supported.extractedCandidateChoice_eq_selection nullValue
    window (cfg.1.nodeValues fallback) focal deviator environment schedule decision guard
      hdecision fallback)

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourcePolicy_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourcePolicy_law

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_source

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_consistent
