/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReadBound
import Interaction.SealedCandidateBinding
import Interaction.SealedCandidateAcceptance

/-! # Source-local selection from candidate acceptance

Fixing the native response functions gives one replay of the actual candidate
runner. Extraction reads the accepted handle's meaning, not the first private
preparation. The acceptance information bound makes this choice a function of
earlier non-focal reference disclosures. The same response functions are used at
every source decision. Fallback totalizes missing or unopenable commitments;
it does not assert a timeout payoff comparison or a joint deviation law.
-/

noncomputable section

namespace Vegas.EventGraph.SealedShape

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedShape G ty) (nullValue : L.Val ty) (window : Nat)
variable (values : Fin G.nodeCount → L.Val ty) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

private theorem candidateReplay_exists :
    ∃ trace, (supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
      (supported.candidateValuePlayers nullValue window values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).candidateInitial)) = FinDist.pure trace := by
  apply MessageApplication.tracePolicies_pure _ _ _ ?_
    (fun _ _ => ⟨_, rfl⟩) (fun _ _ => ⟨_, rfl⟩)
  intro who history view
  by_cases hwho : who = focal
  · subst who
    exact ⟨deviator history view, by
      simp only [candidateValuePlayers, GameTheory.Profile.update_same]⟩
  · rw [candidateValuePlayers, GameTheory.Profile.update_of_ne _ _ hwho,
      SealedResolution.candidatePlayerPolicy]
    exact supported.resolvingProposalPolicy_assigned_pure nullValue window values who _ _

/-- The unique trace of the existing candidate runner with fixed native
responses and assigned reference proposals. It includes execution after timeouts. -/
def candidateReplay :
    (supported.resolvingRuntime nullValue window).candidateApplication.PolicyTrace :=
  Classical.choose (supported.candidateReplay_exists nullValue window values focal
    deviator environment schedule)

theorem candidateReplay_law :
    (supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
      (supported.candidateValuePlayers nullValue window values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _
        (supported.resolvingRuntime nullValue window).candidateInitial)) =
      FinDist.pure (supported.candidateReplay nullValue window values focal
        deviator environment schedule) :=
  Classical.choose_spec (supported.candidateReplay_exists nullValue window values focal
    deviator environment schedule)

/-- Read the meaning of the accepted owner-scoped handle from the public log
and the owner's catalog. Absence, unopenability, and an openable nullable value
remain distinct. Authentication is checked even on unreachable readouts. -/
def selectedCandidate (decision : Fin G.nodeCount)
    (events : List (SealedProgram.Event Player (L.Val ty)))
    (catalog : Nat → CommitmentCandidate (L.Val ty)) : Option (CommitmentCandidate (L.Val ty)) :=
  (SealedProgram.accepted? events decision.val).bind fun handle =>
    if handle.1 = focal then some (catalog handle.2) else none

/-- Accepted meaning at first source-site acceptance, first timeout, or the
finite horizon. Merely preparing a candidate does not select it. -/
def candidateSelection (decision : Fin G.nodeCount) : Option (CommitmentCandidate (L.Val ty)) :=
  let execution := (supported.candidateReplay nullValue window values focal
    deviator environment schedule).firstRelease
      (supported.candidateAcceptanceCut nullValue window decision)
  selectedCandidate focal decision execution.native.application.visible.events
    (fun slot => execution.native.application.service.lookup (focal, slot))

theorem candidateSelection_law (decision : Fin G.nodeCount) :
    (supported.candidateAcceptanceLaw nullValue window
      (supported.resolvingRuntime nullValue window).candidateHandle values focal decision
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule).map
        (fun input => selectedCandidate focal decision input.2.1.application.events input.2.2) =
      FinDist.pure (supported.candidateSelection nullValue window values focal
        deviator environment schedule decision) := by
  have hlaw := congrArg (fun law =>
    (law.map (PolicyTrace.firstRelease
      (app := (supported.resolvingRuntime nullValue window).candidateApplication)
      (supported.candidateAcceptanceCut nullValue window decision))).map fun execution =>
        selectedCandidate focal decision execution.native.application.visible.events
          (fun slot => execution.native.application.service.lookup (focal, slot)))
    (supported.candidateReplay_law nullValue window values focal deviator environment schedule)
  simpa only [candidateAcceptanceLaw, candidateSelection, FinDist.map_comp,
    Function.comp_def, FinDist.map_pure, State.observe,
    SealedResolution.candidateApplication, SealedResolution.candidateHost,
    SealedResolution.host] using hlaw

/-- The common checkpoint immediately after first timeout, or the final
snapshot when there is no timeout. Execution itself is not stopped here. -/
def candidateStop :=
  (supported.candidateReplay nullValue window values focal
    deviator environment schedule).firstRelease (fun execution :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution =>
        !execution.native.application.visible.timeouts.isEmpty)

/-- Acceptance-time extraction can be read at a common checkpoint without
changing the selected candidate, including an unopenable one. -/
theorem candidateSelection_eq_stop (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard) :
    let stopped := supported.candidateStop nullValue window values focal
      deviator environment schedule
    supported.candidateSelection nullValue window values focal deviator environment schedule
        decision =
      selectedCandidate focal decision stopped.native.application.visible.events
        (fun slot => stopped.native.application.service.lookup (focal, slot)) := by
  intro stopped
  let runtime := supported.resolvingRuntime nullValue window
  let trace := supported.candidateReplay nullValue window values focal deviator environment schedule
  have htrace : trace ∈ (runtime.candidateApplication.tracePolicies
      (supported.candidateValuePlayers nullValue window values focal
        (fun history view => FinDist.pure (deviator history view)))
      (fun history view => FinDist.pure (environment history view)) schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support := by
    rw [candidateReplay_law, FinDist.mem_support_pure]
  have hrule : runtime.program.rules[decision.val]? =
      some ⟨.commit focal, G.messagePrerequisites decision⟩ := by
    change supported.compile.rules[decision.val]? = _
    rw [supported.compile_rule]
    exact congrArg some (G.sealedRule_commit_eq decision focal guard hdecision)
  obtain ⟨hread, hmeaning⟩ := runtime.tracePolicies_candidate_acceptance_checkpoint
    runtime.candidateHandle_sound _ _
    schedule trace htrace decision.val focal _ hrule
  let selected := trace.firstRelease (supported.candidateAcceptanceCut nullValue window decision)
  change SealedProgram.accepted? selected.native.application.visible.events decision.val =
    SealedProgram.accepted? stopped.native.application.visible.events decision.val at hread
  change ∀ handle, SealedProgram.accepted? selected.native.application.visible.events decision.val =
    some handle → selected.native.application.service.lookup handle =
      stopped.native.application.service.lookup handle at hmeaning
  change selectedCandidate focal decision selected.native.application.visible.events
    (fun slot => selected.native.application.service.lookup (focal, slot)) = _
  unfold selectedCandidate
  rw [hread]
  cases haccepted : SealedProgram.accepted?
      stopped.native.application.visible.events decision.val with
  | none => rfl
  | some handle =>
      simp only [Option.bind_some]
      split
      next howner =>
        apply congrArg some
        have heq := hmeaning handle (hread.trans haccepted)
        have hhandle : handle = (focal, handle.2) := Prod.ext howner rfl
        rw [hhandle] at heq
        exact heq
      next => rfl

/-- Each checkpoint of the pre-timeout replay has actual unchanged-policy
execution both before it and from it to the common timeout checkpoint. -/
theorem candidateReplay_prefix_support
    (release : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution →
      Bool) :
    let trace := (supported.candidateReplay nullValue window values focal deviator environment
      schedule).prefixThrough (fun execution :
        (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    ∃ before after,
      trace.firstRelease release ∈
        ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
          (supported.candidateValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) before
          (PolicyExecution.initial _ (State.initial _
            (supported.resolvingRuntime nullValue window).candidateInitial))).support ∧
      supported.candidateStop nullValue window values focal deviator environment schedule ∈
        ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
          (supported.candidateValuePlayers nullValue window values focal
            (fun history view => FinDist.pure (deviator history view)))
          (fun history view => FinDist.pure (environment history view)) after
          (trace.firstRelease release)).support := by
  intro trace
  have hfull : supported.candidateReplay nullValue window values focal
      deviator environment schedule ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.tracePolicies
        (supported.candidateValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)))
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support := by
    rw [candidateReplay_law, FinDist.mem_support_pure]
  exact MessageApplication.tracePolicies_prefixThrough_firstRelease_split _ _ _
    (fun execution : (supported.resolvingRuntime
        nullValue window).candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty) release schedule _ _ hfull

/-- Every selected candidate has a nonfresh meaning that persists to the end
of this same native replay. In particular, extraction cannot select a fresh
handle, and later preparation cannot repair an accepted unopenable candidate. -/
theorem candidateSelection_frozen (decision : Fin G.nodeCount)
    (meaning : CommitmentCandidate (L.Val ty))
    (hselection : supported.candidateSelection nullValue window values focal
      deviator environment schedule decision = some meaning) :
    let trace := supported.candidateReplay nullValue window values focal
      deviator environment schedule
    let selected := trace.firstRelease (supported.candidateAcceptanceCut nullValue window decision)
    ∃ slot, SealedProgram.accepted?
        selected.native.application.visible.events decision.val = some (focal, slot) ∧
      trace.last.native.application.service.lookup (focal, slot) = meaning ∧ meaning ≠ .fresh := by
  intro trace selected
  let release := supported.candidateAcceptanceCut nullValue window decision
  change selectedCandidate focal decision
    (trace.firstRelease release).native.application.visible.events
    (fun slot => (trace.firstRelease release).native.application.service.lookup (focal, slot)) =
      some meaning at hselection
  unfold selectedCandidate at hselection
  cases haccepted : SealedProgram.accepted?
      (trace.firstRelease release).native.application.visible.events decision.val with
  | none => simp only [haccepted, Option.bind_none] at hselection; contradiction
  | some handle =>
      simp only [haccepted, Option.bind_some] at hselection
      split at hselection
      next howner =>
        have hmeaning := Option.some.inj hselection
        have htrace : trace ∈ (MessageApplication.tracePolicies
            (supported.resolvingRuntime nullValue window).candidateApplication
            (supported.candidateValuePlayers nullValue window values focal
              (fun history view => FinDist.pure (deviator history view)))
            (fun history view => FinDist.pure (environment history view)) schedule
            (PolicyExecution.initial _ (State.initial _
              (supported.resolvingRuntime nullValue window).candidateInitial))).support := by
          rw [candidateReplay_law, FinDist.mem_support_pure]
        obtain ⟨hfixed, hfrozen⟩ :=
          (supported.resolvingRuntime nullValue window).tracePolicies_candidate_accepted_frozen
            (supported.resolvingRuntime nullValue window).candidateHandle_sound
            _ _ schedule trace htrace release decision.val handle haccepted
        have hhandle : handle = (focal, handle.2) := Prod.ext howner rfl
        rw [hhandle] at haccepted hfixed hfrozen
        exact ⟨handle.2, congrArg some hhandle, hfrozen.trans hmeaning, hmeaning ▸ hfixed⟩
      next => contradiction

/-- With the same native seed, selected candidate meanings depend only on
earlier non-focal reference disclosures, despite competing pending commitments. -/
theorem candidateSelection_read_bound (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (rightValues : Fin G.nodeCount → L.Val ty)
    (hvalues : ∀ who, who ≠ focal → ∀ node,
      supported.knownBefore focal decision (who, node.val) → values node = rightValues node) :
    supported.candidateSelection nullValue window values focal
        deviator environment schedule decision =
      supported.candidateSelection nullValue window rightValues focal
        deviator environment schedule decision := by
  have hlaw := congrArg (fun law => law.map (fun input =>
    selectedCandidate focal decision input.2.1.application.events input.2.2))
    (supported.candidateAcceptanceLaw_read_bound nullValue window
      (supported.resolvingRuntime nullValue window).candidateHandle_knowledge focal decision guard
      hdecision values rightValues hvalues
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule)
  rw [candidateSelection_law, candidateSelection_law] at hlaw
  apply FinDist.mem_support_pure.mp
  rw [← hlaw]
  exact FinDist.mem_support_pure.mpr rfl

/-- Preserve an openable value, including a source null value. Other candidate
statuses select the explicitly supplied fallback. -/
def candidateValue (selection : Option (CommitmentCandidate (L.Val ty)))
    (fallback : L.Val ty) : L.Val ty :=
  match selection with
  | some (.openable value) => value
  | _ => fallback

/-- A decision-local reference choice: replay receives only earlier non-focal disclosures;
all other coordinates are filled with a fixed value. -/
def extractedCandidateChoice (decision : Fin G.nodeCount)
    (visible : supported.priorHonestCoordinates focal decision → L.Val ty)
    (fallback : L.Val ty) : L.Val ty := by
  classical
  exact candidateValue (supported.candidateSelection nullValue window
    (fun node => if h : node ∈ supported.priorHonestCoordinates focal decision then
      visible ⟨node, h⟩ else fallback) focal deviator environment schedule decision) fallback

/-- The source-local choice equals the meaning actually selected at native
acceptance, with fallback only when that selection has no opening. -/
theorem extractedCandidateChoice_eq_selection (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard) (fallback : L.Val ty) :
    supported.extractedCandidateChoice nullValue window focal deviator environment schedule
        decision (fun node => values node.val) fallback =
      candidateValue (supported.candidateSelection nullValue window values focal
        deviator environment schedule decision) fallback := by
  classical
  unfold extractedCandidateChoice
  apply congrArg (fun selection => candidateValue selection fallback)
  apply supported.candidateSelection_read_bound nullValue window _ focal
    deviator environment schedule decision guard hdecision values
  intro who hwho node hknown
  exact dif_pos ⟨who, hwho, hknown⟩

end Vegas.EventGraph.SealedShape

/-- info: 'Vegas.EventGraph.SealedShape.extractedCandidateChoice_eq_selection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.extractedCandidateChoice_eq_selection

/-- info: 'Vegas.EventGraph.SealedShape.candidateSelection_frozen' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedShape.candidateSelection_frozen
