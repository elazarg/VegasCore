/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReplay
import Vegas.Compile.SealedDisclosurePolicy

/-! # Candidate-runtime deviations as graph policies

Fixed native response functions and the graph's public-prefix information
condition determine one legal graph policy. It uses declared graph reads to
replay acceptance and select the accepted opening or a legal fallback.
The construction and its local law do not compile a source policy or invoke
a source backtranslation. Global execution-law comparison is a further result.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (hinfo : G.PublicPrefixReadable)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)

/-- One graph policy for all decisions of the focal player, with the same
native responses used throughout replay. -/
def extractedCandidateCommitPolicy : CommitPolicy G focal :=
  supported.commitPolicyOfDisclosures hinfo focal fun decision visible =>
    supported.extractedCandidateChoice nullValue window focal deviator environment
      schedule decision visible fallback

/-- The graph policy directly realizes the opening selected by native
acceptance replay when its declared disclosure inputs match the assignment. -/
theorem extractedCandidateCommitPolicy_law
    (values : Fin G.nodeCount → L.Val ty)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads)
    (hinputs : supported.disclosureInputs hinfo focal decision guard hdecision reads =
      fun coordinate => values coordinate.val) :
    ((supported.extractedCandidateCommitPolicy hinfo nullValue window focal deviator environment
      schedule fallback) decision guard hdecision reads).map
        (fun value => cast (congrArg L.Val (supported.commitType decision focal guard hdecision))
          value.1) =
      FinDist.pure (SealedShape.candidateValue
        (supported.candidateSelection nullValue window values focal deviator environment
          schedule decision) fallback) := by
  simp only [extractedCandidateCommitPolicy, commitPolicyOfDisclosures, FinDist.map_pure,
    cast_cast, cast_eq, hinputs]
  rw [supported.extractedCandidateChoice_eq_selection nullValue window values focal deviator
    environment schedule decision guard hdecision fallback]

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.extractedCandidateCommitPolicy_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.extractedCandidateCommitPolicy_law
