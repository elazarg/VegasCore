/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateRealization
import Vegas.Compile.SealedDisclosureRun

/-! # Written-source policies extracted from accepted candidates

One fixed pair of native response functions determines a legal source policy
at every source decision. The compiler's declared source reads supply the
earlier disclosed values used by acceptance replay. At matching source views,
the action is exactly the selected candidate's opening, or the legal fallback
if no opening is available. Complete source realizations discharge that
input-agreement premise while retaining the original opponent policies.
`Vegas.Compile.SealedCandidateNativeLikelihood` identifies their replay law
with the actual native prefix through first timeout. Completed-round deviation
utility comparison is a separate theorem obligation.
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
  backtranslateCommitPolicy source.core focal
    (compilation.supported.extractedCandidateCommitPolicy
      (compile_publicPrefixReadable source.core) nullValue window focal deviator environment
      schedule fallback)

/-- At matching declared source observations, the compiled source replacement
chooses the opening of the candidate actually selected at acceptance. Missing
or unopenable selections use the supplied fallback. No runtime preparation or
submission discipline is assumed of the deviator. -/
theorem extractedCandidateSourcePolicy_law
    (values : Fin (compile source.core).graph.nodeCount → L.Val ty)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : compilation.supported.disclosureInputs (compile_publicPrefixReadable source.core)
      focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    (compileSourcePolicy source.core.prog source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
      rfl focal
      (compilation.extractedCandidateSourcePolicy nullValue window focal deviator environment
        schedule fallback) decision guard hdecision reads).map
        (fun value => cast
          (congrArg L.Val (compilation.supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure (SealedShape.candidateValue
        (compilation.supported.candidateSelection nullValue window values focal
          deviator environment schedule decision) fallback) := by
  unfold extractedCandidateSourcePolicy
  rw [compile_backtranslateCommitPolicy]
  exact compilation.supported.extractedCandidateCommitPolicy_law
    (compile_publicPrefixReadable source.core) nullValue window focal deviator environment
    schedule fallback values decision guard hdecision reads hinputs

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


end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourcePolicy_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourcePolicy_law

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_source
