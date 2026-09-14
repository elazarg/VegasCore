/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReplay
import Vegas.Compile.SealedDisclosureRun
import Vegas.Compile.SealedCandidateValues

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

/-- The complete legal source realization retains every openable focal
candidate accepted by the common timeout checkpoint. Unaccepted preparations
do not constrain the source choice. -/
theorem extractedCandidateSourceRun_locked (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator
      environment schedule fallback profile).support)
    (decision : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hdecision : ((compile source.core).graph.nodeRow decision).sem = .commit focal guard)
    (slot : Nat) (value : L.Val ty)
    (haccepted : SealedProgram.accepted?
      (compilation.supported.candidateStop nullValue window (cfg.1.nodeValues fallback) focal
        deviator environment schedule).native.application.visible.events decision.val =
          some (focal, slot))
    (hvalue : (compilation.supported.candidateStop nullValue window (cfg.1.nodeValues fallback)
      focal deviator environment schedule).native.application.service.lookup (focal, slot) =
        .openable value) : cfg.1.nodeValues fallback decision = value := by
  have hchoice := compilation.extractedCandidateSourceRun_consistent nullValue window focal
    deviator environment schedule fallback profile cfg hcfg decision guard hdecision
  rw [SealedFragment.candidateSelection_eq_stop _ _ _ _ _ _ _ _ decision guard hdecision] at hchoice
  simpa only [SealedFragment.selectedCandidate, haccepted, Option.bind_some, ↓reduceIte,
    hvalue, SealedFragment.candidateValue] using hchoice

/-- Every focal acceptance at a checkpoint of the pre-timeout replay has its
complete source value whenever that candidate is openable. Arbitrary other
preparations and permanently unopenable acceptances remain permitted. -/
theorem extractedCandidateSourceRun_focal_accepted
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let stopped := ((compilation.supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (compilation.supported.resolvingRuntime
          nullValue window).candidateApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    ∀ index slot value,
      SealedProgram.Event.accepted index (focal, slot) ∈
        stopped.native.application.visible.events →
      stopped.native.application.service.lookup (focal, slot) = .openable value →
      cfg.1.store ((compile source.core).graph.nodeTarget index) =
        some (⟨ty, value⟩ : TypedValue L) := by
  intro stopped index slot value haccepted hvalue
  let runtime := compilation.supported.resolvingRuntime nullValue window
  obtain ⟨before, after, hbefore, hafter⟩ := compilation.supported.candidateReplay_prefix_support
    nullValue window (cfg.1.nodeValues fallback) focal deviator environment schedule release
  have hacceptance := runtime.runPolicies_candidate_acceptance _ _ before _ stopped
    SealedResolution.CandidateAcceptanceInvariant.initial hbefore
  obtain ⟨hselected, requires, hrule⟩ := hacceptance index (focal, slot) haccepted
  obtain ⟨node, guard, rfl, hsem⟩ := compilation.supported.ruleAt_commit hrule rfl
  have hsource := compilation.extractedCandidateSourceRun_locked nullValue window focal
    deviator environment schedule fallback profile cfg hcfg node guard hsem slot value
    (runtime.runPolicies_candidate_accepted? _ _ after stopped _ node.val (focal, slot)
      hselected hafter)
    ((runtime.runPolicies_candidate_lookup_of_not_fresh _ _ after stopped _ (focal, slot)
      (by rw [hvalue]; simp) hafter).trans hvalue)
  have hterminal := compilation.sourceRunOfDisclosures_terminal focal _ profile cfg hcfg
  rw [cfg.1.store_nodeValues (reachable_storeCoherent compilation.supported.graphWF cfg.2)
    fallback node (compilation.supported.rowType node) (hterminal node), hsource]

/-- Every openable acceptance in a pre-timeout replay has its complete source
value. Focal candidates use acceptance-time extraction; honest candidates use
the unchanged generated policies and their actual retained-message provenance. -/
theorem extractedCandidateSourceRun_accepted
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let stopped := ((compilation.supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : (compilation.supported.resolvingRuntime
          nullValue window).candidateApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    ∀ index handle value,
      SealedProgram.Event.accepted index handle ∈ stopped.native.application.visible.events →
      stopped.native.application.service.lookup handle = .openable value →
      cfg.1.store ((compile source.core).graph.nodeTarget index) =
        some (⟨ty, value⟩ : TypedValue L) := by
  intro stopped index handle value haccepted hvalue
  by_cases howner : handle.1 = focal
  · have hhandle : handle = (focal, handle.2) := Prod.ext howner rfl
    rw [hhandle] at haccepted hvalue
    exact compilation.extractedCandidateSourceRun_focal_accepted nullValue window focal
      deviator environment schedule fallback profile cfg hcfg release index handle.2 value
      haccepted hvalue
  · let runtime := compilation.supported.resolvingRuntime nullValue window
    obtain ⟨before, _after, hbefore, _hafter⟩ :=
      compilation.supported.candidateReplay_prefix_support nullValue window
        (cfg.1.nodeValues fallback) focal deviator environment schedule release
    have hacceptance := runtime.runPolicies_candidate_acceptance _ _ before _ stopped
      SealedResolution.CandidateAcceptanceInvariant.initial hbefore
    obtain ⟨_hselected, requires, hrule⟩ := hacceptance index handle haccepted
    obtain ⟨node, guard, rfl, _hsem⟩ := compilation.supported.ruleAt_commit hrule rfl
    have hhandle := compilation.supported.candidatePolicy_accepted_slot nullValue window handle.1
      (compilation.supported.valuePolicy (cfg.1.nodeValues fallback) handle.1) _ _
      (by rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ howner])
      before stopped hbefore node.val handle haccepted rfl
    rw [hhandle] at hvalue
    have hsource := compilation.supported.runPolicies_candidateValues_lookup nullValue window
      (cfg.1.nodeValues fallback) focal _ _ before stopped hbefore handle.1 howner node value hvalue
    have hterminal := compilation.sourceRunOfDisclosures_terminal focal _ profile cfg hcfg
    rw [cfg.1.store_nodeValues (reachable_storeCoherent compilation.supported.graphWF cfg.2)
      fallback node (compilation.supported.rowType node) (hterminal node), ← hsource]

/-- At every fresh honest preparation in pre-timeout replay, the original
source policy is evaluated at its exact declared source inputs. No agreement
of caches, accepted values, or local read environments is assumed by the caller. -/
theorem extractedCandidateSourceRun_registration_kernel
    (profile : SourceBehavioralProfile source.core.prog)
    (cfg : ReachableConfig (compile source.core).graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun nullValue window focal deviator
      environment schedule fallback profile).support)
    (release : (compilation.supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution → Bool) :
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := ((compilation.supported.candidateReplay nullValue window
      (cfg.1.nodeValues fallback) focal deviator environment schedule).prefixThrough
        (fun execution : runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.candidateValuePlayers nullValue window (cfg.1.nodeValues fallback)
          focal (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who) (State.observe _ stopped.native who)).support →
      ∀ policy : SourceBehavioralPolicy source.core.prog who,
      ∃ (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = .fresh ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileCandidatePolicy nullValue window who policy
          (stopped.principalHistory who) (State.observe _ stopped.native who) =
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who policy) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro runtime stopped hclear who hwho slot value hcommand policy
  obtain ⟨before, _after, hbefore, _hafter⟩ := compilation.supported.candidateReplay_prefix_support
    nullValue window (cfg.1.nodeValues fallback) focal deviator environment schedule release
  have hplayer := Profile.update_of_ne
    (sig := MessageApplication.policySignature Player runtime.candidateApplication)
    (fun owner => runtime.candidatePlayerPolicy (compilation.supported.resolvingPolicy nullValue
      window owner (compilation.supported.valuePolicy (cfg.1.nodeValues fallback) owner)))
    (fun history view => FinDist.pure (deviator history view)) hwho
  rw [SealedFragment.candidateValuePlayers, Profile.update_of_ne _ _ hwho] at hcommand
  exact compilation.supported.candidate_registration_kernel cfg
    (compilation.sourceRunOfDisclosures_terminal focal _ profile cfg hcfg) nullValue window
    _ _ before stopped hbefore hclear who _ _ hplayer
    (compilation.extractedCandidateSourceRun_accepted nullValue window focal deviator environment
      schedule fallback profile cfg hcfg release) slot value hcommand

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

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_focal_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_focal_accepted

/-- info: 'Vegas.SealedCompilation.extractedCandidateSourceRun_registration_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.extractedCandidateSourceRun_registration_kernel
