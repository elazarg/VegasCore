/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReadBound
import Vegas.Compile.SealedCandidateSourceExtraction
import Vegas.Compile.SealedCandidateInputs
import Vegas.Compile.SealedCandidateSourceLikelihood
import Vegas.Compile.SealedCandidateSourceFactors
import Vegas.Compile.SealedCandidateNativeLikelihood
import Vegas.Compile.SealedCandidateRandomizedCoupling
import VegasTests.PendingSource

/-! # Native registration and acceptance hiding for a checked two-player source

The source's first two choices precede every disclosure. The second player's
arbitrary randomized native policy therefore has the same stopped registration
law for all assignments to the honest player's choice, under any randomized
full-pool environment and finite invocation sequence. The same independence
holds for its complete local input through public acceptance, including the
interval after private registration.
-/

noncomputable section

namespace VegasTests.SealedResolutionReadBound

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingSource

abbrev Value := Option Bool
abbrev runtime := sealedFragment.resolvingRuntime none 3
abbrev app := runtime.messageApplication

private theorem no_honest_known_before_second (who : PendingSource.Player) (hwho : who ≠ 1)
    (index : Fin graph.nodeCount)
    (hknown : sealedFragment.knownBefore 1 (node 1) (who, index.val)) :
    False := by
  rcases hknown with hwhoEq | ⟨opening, requires, hbefore, hrule⟩
  · exact hwho hwhoEq
  · have hopening : opening = 0 := by
      change opening < 1 at hbefore
      omega
    subst opening
    change some (SealedRule.mk (.commit 0) []) =
      some (SealedRule.mk (.reveal who index.val) requires) at hrule
    cases hrule

theorem hidden_first_choice (leftValues rightValues : Fin graph.nodeCount → Value)
    (deviator : app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    sealedFragment.resolvingBindingLaw none 3 leftValues 1 (node 1)
        deviator environment schedule =
      sealedFragment.resolvingBindingLaw none 3 rightValues 1 (node 1)
        deviator environment schedule := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  apply sealedFragment.resolvingBindingLaw_read_bound none 3 1 (node 1) guard hguard
    leftValues rightValues ?_ deviator environment schedule
  intro who hwho index hknown
  exact False.elim (no_honest_known_before_second who hwho index hknown)

/-- Independence holds through public acceptance, rather than ending at the
focal player's private preparation. The observation includes its full history. -/
theorem hidden_until_acceptance (leftValues rightValues : Fin graph.nodeCount → Value)
    (deviator : app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    sealedFragment.resolvingAcceptanceLaw none 3 leftValues 1 (node 1)
        deviator environment schedule =
      sealedFragment.resolvingAcceptanceLaw none 3 rightValues 1 (node 1)
        deviator environment schedule := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  apply sealedFragment.resolvingAcceptanceLaw_read_bound none 3 1 (node 1) guard hguard
    leftValues rightValues ?_ deviator environment schedule
  intro who hwho index hknown
  exact False.elim (no_honest_known_before_second who hwho index hknown)

/-- Private preparation does not close the acceptance cut or release a later
opening. Public acceptance is a distinct transition. -/
theorem registration_is_not_acceptance :
    let initial := PolicyExecution.initial app (State.initial app runtime.initial)
    let prepared : app.PolicyExecution := { initial with
      native.application.service := (IdealCommitments.empty.sealValue 1 1 (some true)).state }
    sealedFragment.bindingCut none 3 1 (node 1) prepared = true ∧
      sealedFragment.acceptanceCut none 3 (node 1) prepared = false ∧
      sealedFragment.compile.openingReady prepared.native.application.visible.events 0 2 = false :=
  ⟨rfl, rfl, rfl⟩

private def prepareThenSubmit : app.PlayerPolicy := fun history _ =>
  FinDist.pure (if history.isEmpty then .privateCommand ⟨(1, some true)⟩
    else .submit (.commitment 1 (1, 1)))

/-- The cut actually waits past private preparation and pending submission,
and retains the two commands and the accepted event in the player's input. -/
theorem acceptance_retains_preparation_and_submission :
    (sealedFragment.resolvingAcceptanceLaw none 3 (fun _ => some false) 1 (node 1)
      prepareThenSubmit (fun _ _ => FinDist.pure (.include (1, 0)))
      [.player 1, .player 1, .environment]).map
        (fun input => (input.1.length, input.2.application.events)) =
      FinDist.pure (2, [.accepted 1 (1, 1)]) := by
  simp only [SealedFragment.resolvingAcceptanceLaw, tracePolicies, invoke,
    SealedFragment.resolvingValuePlayers, GameTheory.Profile.update_same,
    prepareThenSubmit, playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.map_pure, PolicyExecution.initial, List.isEmpty_nil, List.isEmpty_cons,
    List.nil_append, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- This witness actually submits and delivers an opaque pending commitment
before the focal registration; there is no inclusion or opening in the trace. -/
theorem registration_after_pending_delivery :
    sealedFragment.resolvingBindingLaw none 3 (fun _ => some false) 1 (node 1)
        (fun _ _ => FinDist.pure (.privateCommand ⟨(1, some true)⟩))
        (fun _ _ => FinDist.pure (.deliver 1 (0, 0)))
        [.player 0, .player 0, .environment, .player 1] = FinDist.pure (some (some true)) := by
  let initial := PolicyExecution.initial app (State.initial app runtime.initial)
  let registered : app.PolicyExecution :=
    { initial with
      native := { initial.native with
        application.service := (IdealCommitments.empty.sealValue 0 0 (some false)).state }
      principalHistory := fun who => if who = 0 then
        [⟨State.observe app initial.native 0, .privateCommand ⟨(0, some false)⟩⟩] else []
      nativeTrace := [.privateCommand 0 ⟨(0, some false)⟩] }
  have hfirst : sealedFragment.resolvingPolicy none 3 0
      (sealedFragment.valuePolicy (fun _ => some false) 0)
      [] (State.observe app initial.native 0) =
        FinDist.pure (.privateCommand ⟨(0, some false)⟩ : app.PlayerCommand) := by
    change sealedFragment.commitCommand 0 (sealedFragment.valuePolicy (fun _ => some false) 0)
      (node 0) _ rfl [] _ = _
    unfold SealedFragment.commitCommand
    simp only [ChoiceEncoding.cachedValue_nil]
    exact FinDist.map_pure _ _
  have hregistered : app.playerStep 0 initial (.privateCommand ⟨(0, some false)⟩) =
      FinDist.pure registered := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind]
    rfl
  have hsecond : sealedFragment.resolvingPolicy none 3 0
      (sealedFragment.valuePolicy (fun _ => some false) 0)
      (registered.principalHistory 0) (State.observe app registered.native 0) =
        FinDist.pure (.submit (.commitment 0 (0, 0)) : app.PlayerCommand) := rfl
  simp only [SealedFragment.resolvingBindingLaw, tracePolicies, invoke,
    SealedFragment.resolvingValuePlayers, GameTheory.Profile.update_same,
    GameTheory.Profile.update_of_ne _ _ (show (0 : PendingSource.Player) ≠ 1 by decide)]
  erw [hfirst]
  simp only [FinDist.pure_bind]
  erw [hregistered]
  simp only [FinDist.pure_bind]
  erw [hsecond]
  simp only [playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- The same checked source has the stronger acceptance read bound in the
candidate host, without any preparation-discipline restriction on the deviator. -/
theorem candidate_hidden_until_acceptance (leftValues rightValues : Fin graph.nodeCount → Value)
    (deviator : runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    sealedFragment.candidateAcceptanceLaw none 3 leftValues 1 (node 1)
        deviator environment schedule =
      sealedFragment.candidateAcceptanceLaw none 3 rightValues 1 (node 1)
        deviator environment schedule := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  apply sealedFragment.candidateAcceptanceLaw_read_bound none 3 1 (node 1) guard hguard
    leftValues rightValues ?_ deviator environment schedule
  intro who hwho index hknown
  exact False.elim (no_honest_known_before_second who hwho index hknown)

private def selectCommand (history : List runtime.candidateApplication.PlayerEntry)
    (_view : runtime.candidateApplication.View) : runtime.candidateApplication.PlayerCommand :=
  match history.length with
  | 0 => .privateCommand ⟨(10, some false)⟩
  | 1 => .privateCommand ⟨(11, some true)⟩
  | 2 => .submit (.commitment 1 (1, 11))
  | _ => .wait

private def prepareThenSelect : runtime.candidateApplication.PlayerPolicy :=
  fun history view => FinDist.pure (selectCommand history view)

/-- The readout permits two preparations and selects the second candidate at
public acceptance. It retains both preparations, the submission, the accepted
handle, and the immutable meanings, rather than cutting at the first preparation. -/
theorem candidate_acceptance_retains_selection :
    (sealedFragment.candidateAcceptanceLaw none 3 (fun _ => some false) 1 (node 1)
      prepareThenSelect (fun _ _ => FinDist.pure (.include (1, 0)))
      [.player 1, .player 1, .player 1, .environment]).map
        (fun input => (input.1.length, input.2.1.application.events,
          input.2.2 10, input.2.2 11)) =
      FinDist.pure (3, [.accepted 1 (1, 11)],
        CommitmentCandidate.openable (some false), CommitmentCandidate.openable (some true)) := by
  simp only [SealedFragment.candidateAcceptanceLaw, tracePolicies, invoke,
    SealedFragment.candidateValuePlayers, GameTheory.Profile.update_same,
    prepareThenSelect, selectCommand, playerStep, environmentPolicyStep, advance,
    PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.map_pure, PolicyExecution.initial, List.length_nil, List.length_append,
    List.length_cons, List.nil_append, ↓reduceIte]
  rfl

/-- Extraction selects the second candidate, even though the first preparation
has a different value and neither candidate identifier equals the source site. -/
theorem candidate_selection_second (values : Fin graph.nodeCount → Value) :
    sealedFragment.candidateSelection none 3 values 1 selectCommand
      (fun _ _ => .include (1, 0))
      [.player 1, .player 1, .player 1, .environment] (node 1) =
        some (.openable (some true)) := by
  have hlaw := sealedFragment.candidateSelection_law none 3 values 1 selectCommand
    (fun _ _ => .include (1, 0)) [.player 1, .player 1, .player 1, .environment] (node 1)
  have hcomputed : (sealedFragment.candidateAcceptanceLaw none 3 values 1 (node 1)
      (fun history view => FinDist.pure (selectCommand history view))
      (fun _ _ => FinDist.pure (.include (1, 0)))
      [.player 1, .player 1, .player 1, .environment]).map
        (fun input => SealedFragment.selectedCandidate 1 (node 1)
          input.2.1.application.events input.2.2) =
      FinDist.pure (some (.openable (some true))) := by
    simp only [SealedFragment.candidateAcceptanceLaw, tracePolicies, invoke,
      SealedFragment.candidateValuePlayers, GameTheory.Profile.update_same,
      selectCommand, playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
      EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
      FinDist.map_pure, PolicyExecution.initial, List.length_nil, List.length_append,
      List.length_cons, List.nil_append, ↓reduceIte]
    rfl
  rw [hcomputed] at hlaw
  exact FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)

/-- An accepted never-prepared handle is retained as unopenable rather than
confused with an absent commitment or an openable source decline value. -/
theorem candidate_selection_unopenable (values : Fin graph.nodeCount → Value) :
    sealedFragment.candidateSelection none 3 values 1
      (fun _ _ => .submit (.commitment 1 (1, 23))) (fun _ _ => .include (1, 0))
      [.player 1, .environment] (node 1) = some .unopenable := by
  have hlaw := sealedFragment.candidateSelection_law none 3 values 1
    (fun _ _ => .submit (.commitment 1 (1, 23))) (fun _ _ => .include (1, 0))
    [.player 1, .environment] (node 1)
  have hcomputed : (sealedFragment.candidateAcceptanceLaw none 3 values 1 (node 1)
      (fun _ _ => FinDist.pure (.submit (.commitment 1 (1, 23))))
      (fun _ _ => FinDist.pure (.include (1, 0))) [.player 1, .environment]).map
        (fun input => SealedFragment.selectedCandidate 1 (node 1)
          input.2.1.application.events input.2.2) = FinDist.pure (some .unopenable) := by
    simp only [SealedFragment.candidateAcceptanceLaw, tracePolicies, invoke,
      SealedFragment.candidateValuePlayers, GameTheory.Profile.update_same,
      playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
      EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
      FinDist.map_pure, PolicyExecution.initial]
    rfl
  rw [hcomputed] at hlaw
  exact FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)

private theorem compilation : SealedCompilation source (.option .bool) := ⟨sealedFragment⟩

/-- The selected second candidate inhabits the original source strategy type.
The source decision has no honest disclosed inputs; that premise is discharged. -/
theorem candidate_source_selects_second (guard : EventGuard simpleExpr)
    (hguard : (graph.nodeRow (node 1)).sem = .commit 1 guard)
    (reads : ReadEnv simpleExpr guard.choiceReads) (fallback : Value) :
    (Vegas.ToEventGraph.compileSourcePolicy core source.core.fresh
      (Vegas.ToEventGraph.BuildState.fromInitial
        (Vegas.ToEventGraph.initialState [] (VEnv.empty simpleExpr) (by simp))) rfl 1
      (compilation.extractedCandidateSourcePolicy none 3 1 selectCommand
        (fun _ _ => .include (1, 0)) [.player 1, .player 1, .player 1, .environment] fallback)
      (node 1) guard hguard reads).map
        (fun choice => cast (congrArg simpleExpr.Val
          (sealedFragment.commitType (node 1) 1 guard hguard)) choice.val) =
      FinDist.pure (some true) := by
  have hinputs : compilation.supported.disclosureInputs
      (Vegas.ToEventGraph.compile_publicPrefixReadable source.core)
      1 (node 1) guard hguard reads =
      fun _ => (none : Value) := by
    funext coordinate
    obtain ⟨who, hwho, hknown⟩ := coordinate.property
    exact (no_honest_known_before_second who hwho coordinate.val hknown).elim
  have hlaw := compilation.extractedCandidateSourcePolicy_law none 3 1 selectCommand
    (fun _ _ => .include (1, 0)) [.player 1, .player 1, .player 1, .environment] fallback
    (fun _ => none) (node 1) guard hguard reads hinputs
  rw [candidate_selection_second] at hlaw
  exact hlaw

/-- With an accepted unopenable candidate, every complete source realization
of the extracted replacement chooses the explicit nullable fallback. Opponent
source policies remain arbitrary, and source-input agreement is not assumed. -/
theorem candidate_source_unopenable_defaults (profile : SourceBehavioralProfile core)
    (cfg : ReachableConfig graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun none 3 1
      (fun _ _ => .submit (.commitment 1 (1, 23))) (fun _ _ => .include (1, 0))
      [.player 1, .environment] none profile).support) :
    cfg.1.nodeValues (L := simpleExpr) (ty := .option .bool) none (node 1) = none := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  have hchoice := compilation.extractedCandidateSourceRun_consistent none 3 1
    (fun _ _ => .submit (.commitment 1 (1, 23))) (fun _ _ => .include (1, 0))
    [.player 1, .environment] none profile cfg hcfg (node 1) guard hguard
  rw [candidate_selection_unopenable] at hchoice
  exact hchoice

/-- The source compiler supplies the preparation discipline for player zero;
the other player's entire native policy and the environment remain arbitrary. -/
theorem candidate_compiled_memory (profile : SourceBehavioralProfile core)
    (deviator : runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player))
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      (GameTheory.Profile.update
        (sig := policySignature PendingSource.Player runtime.candidateApplication)
        (fun who => compilation.compileCandidatePolicy none 3 who (profile who)) 1 deviator)
      environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (slot : Nat) :
    next.native.application.service.lookup (0, slot) =
      ((sealedFragment.compile.registrationEncoding slot).cachedValue runtime.candidateApplication
        (next.principalHistory 0) |>.map CommitmentCandidate.openable).getD .fresh := by
  have hmemory : SealedResolution.PreparedCandidateOwner runtime 0 next := by
    let original := Vegas.ToEventGraph.compileSourcePolicy core source.core.fresh
      (Vegas.ToEventGraph.BuildState.fromInitial
        (Vegas.ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx))
      rfl 0 (profile 0)
    exact sealedFragment.candidatePolicy_memory none 3 0 original _ environment
      (by rfl) schedule next hnext
  exact hmemory.memory slot

/-- A normal second-player opening in this checked source always uses its
actually accepted candidate, even for completely arbitrary native policies. -/
theorem candidate_opening_uses_selected_handle
    (players : PendingSource.Player → runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player))
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies players environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (hclear : next.native.application.visible.timeouts = []) (value : Value)
    (hopened : SealedProgram.Event.opened 3 value ∈ next.native.application.visible.events) :
    ∃ slot, SealedProgram.accepted? next.native.application.visible.events 1 = some (1, slot) ∧
      next.native.application.service.lookup (1, slot) = .openable value := by
  have hvalid := SealedResolution.runPolicies_candidate_openings players environment schedule
    _ next SealedResolution.CandidateOpeningInvariant.initial hnext
  obtain ⟨owner, sourceSlot, requires, handle, hrule, haccepted, howner, hvalue⟩ :=
    hvalid hclear 3 value hopened
  have hkind := congrArg (Option.map SealedRule.kind) hrule
  change some (SealedRuleKind.reveal (1 : PendingSource.Player) 1) =
    some (.reveal owner sourceSlot) at hkind
  simp only [Option.some.injEq, SealedRuleKind.reveal.injEq] at hkind
  obtain ⟨rfl, rfl⟩ := hkind
  have hhandle : handle = (1, handle.2) := Prod.ext howner rfl
  rw [hhandle] at haccepted hvalue
  exact ⟨handle.2, haccepted, hvalue⟩

/-- Competing candidates from player one cannot change the source-site
identity of a commitment accepted from the generated player-zero policy. -/
theorem candidate_compiled_acceptance_slot (profile : SourceBehavioralProfile core)
    (deviator : runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player))
    (next : runtime.candidateApplication.PolicyExecution)
    (hnext : next ∈ (runtime.candidateApplication.runPolicies
      (GameTheory.Profile.update
        (sig := policySignature PendingSource.Player runtime.candidateApplication)
        (fun who => compilation.compileCandidatePolicy none 3 who (profile who)) 1 deviator)
      environment schedule
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support)
    (index slot : Nat)
    (haccepted : SealedProgram.Event.accepted index (0, slot) ∈
      next.native.application.visible.events) : slot = index := by
  let original := Vegas.ToEventGraph.compileSourcePolicy core source.core.fresh
    (Vegas.ToEventGraph.BuildState.fromInitial
      (Vegas.ToEventGraph.initialState source.core.Γ source.core.env source.core.wctx))
    rfl 0 (profile 0)
  have hhandle := sealedFragment.candidatePolicy_accepted_slot none 3 0 original _ environment
    (by rfl) schedule next hnext index (0, slot) haccepted rfl
  exact congrArg Prod.snd hhandle

/-- In this checked two-player source, every openable accepted candidate of
either player has its extracted source value at every pre-timeout checkpoint.
The native response functions and pending-message schedule are unrestricted. -/
theorem candidate_replay_acceptances_match_source
    (profile : SourceBehavioralProfile core)
    (deviator : List runtime.candidateApplication.PlayerEntry →
      runtime.candidateApplication.View → runtime.candidateApplication.PlayerCommand)
    (environment : List runtime.candidateApplication.EnvironmentEntry →
      runtime.candidateApplication.EnvironmentObservation →
        runtime.candidateApplication.EnvironmentPolicyCommand)
    (schedule : List (@Invocation PendingSource.Player))
    (cfg : ReachableConfig graph)
    (hcfg : cfg ∈ (compilation.extractedCandidateSourceRun none 3 1 deviator environment
      schedule none profile).support)
    (release : runtime.candidateApplication.PolicyExecution → Bool) :
    let stopped := ((sealedFragment.candidateReplay none 3 (cfg.1.nodeValues none) 1
      deviator environment schedule).prefixThrough
        (fun execution : runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    ∀ index handle value,
      SealedProgram.Event.accepted index handle ∈ stopped.native.application.visible.events →
      stopped.native.application.service.lookup handle = .openable value →
      cfg.1.store (graph.nodeTarget index) =
        some (⟨.option .bool, value⟩ : TypedValue simpleExpr) :=
  compilation.extractedCandidateSourceRun_accepted none 3 1 deviator environment schedule none
    profile cfg hcfg release

/-- A reference realization exists even when its forced honest value had zero
probability under the original profile. The focal traffic prepares competing
candidates and selects the second, exactly as in the acceptance regression. -/
theorem candidate_reference_exists (profile : SourceBehavioralProfile core)
    (reference : Fin graph.nodeCount → Value) :
    let schedule : List (@Invocation PendingSource.Player) :=
      [.player 0, .player 1, .player 1, .player 1, .environment]
    let stopped := (sealedFragment.candidateReplay none 3 reference 1 selectCommand
      (fun _ _ => .include (1, 0)) schedule).prefixThrough (fun _ => false)
    let restriction := compilation.recordedChoiceRestriction (fun who => decide (who ≠ 1))
      (fun handle => (stopped.last.native.application.service.lookup handle).opening?)
    ∃ cfg ∈ (compilation.extractedCandidateSourceRun none 3 1 selectCommand
      (fun _ _ => .include (1, 0)) schedule none (restriction.apply profile)).support,
      (sealedFragment.candidateReplay none 3 (cfg.1.nodeValues none) 1 selectCommand
        (fun _ _ => .include (1, 0)) schedule).prefixThrough (fun _ => false) = stopped := by
  intro schedule stopped restriction
  obtain ⟨cfg, hcfg⟩ := (compilation.extractedCandidateSourceRun none 3 1 selectCommand
    (fun _ _ => .include (1, 0)) schedule none (restriction.apply profile)).support_nonempty
  exact ⟨cfg, hcfg, compilation.restrictedCandidateSourceRun_replay_prefix none 3 1 selectCommand
    (fun _ _ => .include (1, 0)) schedule none reference (fun _ => false) profile cfg hcfg⟩

/-- Correlating every assigned coordinate is permitted even with competing
focal preparations and a pending commitment. Only recorded honest preparation
coordinates constrain this replay event. -/
theorem candidate_correlated_cylinder (bits : FinDist Bool) (reference : Bool) :
    let schedule : List (@Invocation PendingSource.Player) :=
      [.player 0, .player 1, .player 1, .player 1, .environment]
    let assignments := bits.map (fun bit => fun _ : Fin graph.nodeCount => some bit)
    let replay := fun values => (sealedFragment.candidateReplay none 3 values 1 selectCommand
      (fun _ _ => .include (1, 0)) schedule).prefixThrough (fun _ => false)
    (assignments.map replay).prob (replay (fun _ => some reference)) =
      assignments.probOf {values | ∀ who (index : Fin graph.nodeCount) (value : Value),
        who ≠ 1 →
          (.privateCommand who ⟨(index.val, value)⟩ : runtime.candidateApplication.Action) ∈
            (replay (fun _ => some reference)).last.nativeTrace →
              some reference = values index} := by
  intro schedule assignments replay
  exact sealedFragment.candidateReplay_cylinder_probability none 3 1 selectCommand
    (fun _ _ => .include (1, 0)) schedule (fun _ => false) assignments (fun _ => some reference)

/-- The source probability for competing-candidate traffic is a product of
original honest preparation probabilities. The queried assignment need not
have positive probability under this profile. -/
theorem candidate_source_prefix_product (profile : SourceBehavioralProfile core)
    (reference : Fin graph.nodeCount → Value) :
    let schedule : List (@Invocation PendingSource.Player) :=
      [.player 0, .player 1, .player 1, .player 1, .environment]
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let replay := fun values => (sealedFragment.candidateReplay none 3 values 1 selectCommand
      (fun _ _ => .include (1, 0)) schedule).prefixThrough stop
    ((compilation.extractedCandidateSourceRun none 3 1 selectCommand
      (fun _ _ => .include (1, 0)) schedule none profile).map
        (fun cfg => replay (cfg.1.nodeValues none))).prob (replay reference) =
      (core.decisionPositions.map fun slot =>
        compilation.candidateReplayRegistrationFactor none 3 1 selectCommand
          (fun _ _ => .include (1, 0)) schedule reference profile slot.1 slot.2).prod := by
  intro schedule stop replay
  exact compilation.extractedCandidateSourceRun_replay_prob_eq_product none 3 1 selectCommand
    (fun _ _ => .include (1, 0)) schedule none reference profile

private def pendingReactiveCommand (history : List runtime.candidateApplication.PlayerEntry)
    (view : runtime.candidateApplication.View) : runtime.candidateApplication.PlayerCommand :=
  match history.length with
  | 0 => .privateCommand ⟨(10, some false)⟩
  | 1 => .privateCommand ⟨(11, some true)⟩
  | 2 => .submit (.commitment 1 (1, if view.messages.inbox.isEmpty then 10 else 11))
  | _ => .wait

/-- The two-player native prefix law includes a deviator choosing between
independently prepared candidates after receiving a still-pending commitment.
The environment delivers the honest packet before permitting focal acceptance;
the honest source policy remains arbitrary. -/
theorem candidate_source_native_pending_reaction (profile : SourceBehavioralProfile core) :
    let schedule : List (@Invocation PendingSource.Player) :=
      [.player 0, .player 0, .environment, .player 1, .player 1, .player 1, .environment]
    let environment := fun (history : List runtime.candidateApplication.EnvironmentEntry)
        (_ : runtime.candidateApplication.EnvironmentObservation) =>
      if history.isEmpty then .deliver 1 (0, 0) else .include (1, 0)
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let players := GameTheory.Profile.update
      (sig := policySignature PendingSource.Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy none 3 who (profile who)) 1
      (fun history view => FinDist.pure (pendingReactiveCommand history view))
    (compilation.extractedCandidateSourceRun none 3 1 pendingReactiveCommand environment schedule
      none profile).map (fun cfg =>
        (sealedFragment.candidateReplay none 3 (cfg.1.nodeValues none) 1 pendingReactiveCommand
          environment schedule).prefixThrough stop) =
      (runtime.candidateApplication.tracePolicies players
        (fun history view => FinDist.pure (environment history view)) schedule
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).map
          (PolicyTrace.prefixThrough stop) := by
  intro schedule environment stop players
  exact compilation.extractedCandidateSourceRun_native_prefix_law none 3 1 pendingReactiveCommand
    environment schedule none profile

/-- After both commitments time out, the actual native suffix still executes
the focal player's unrelated preparation. The retained source realization does
not replace this suffix with a replay of its assigned choices. -/
theorem candidate_coupling_retains_timeout_suffix (profile : SourceBehavioralProfile core) :
    let schedule : List (@Invocation PendingSource.Player) :=
      [.environment, .environment, .environment, .player 1]
    let coupled := compilation.extractedCandidateSourceCoupling none 3 1
      (fun _ _ => .privateCommand ⟨(99, some true)⟩) (fun _ _ => .application ⟨()⟩)
      schedule none profile
    coupled.map (fun pair =>
      (pair.2.last.native.application.visible.timeouts,
        pair.2.last.native.application.service.lookup (1, 99),
        (pair.2.last.principalHistory 1).length)) =
      FinDist.pure ([0, 1], CommitmentCandidate.openable (some true), 1) := by
  intro schedule coupled
  let project := fun trace : runtime.candidateApplication.PolicyTrace =>
    (trace.last.native.application.visible.timeouts,
      trace.last.native.application.service.lookup (1, 99),
      (trace.last.principalHistory 1).length)
  change coupled.map (project ∘ Prod.snd) = _
  rw [← FinDist.map_comp, compilation.extractedCandidateSourceCoupling_native]
  simp only [schedule, tracePolicies, invoke, GameTheory.Profile.update_same,
    environmentPolicyStep, playerStep, advance, EnvironmentPolicyCommand.toAction,
    PlayerCommand.toAction, MessageApplication.step, SealedResolution.candidateApplication,
    SealedResolution.host, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Arbitrary randomized focal behavior and randomized pending-message delivery
admit a single ex-ante response mixture with the complete native law. -/
theorem candidate_randomized_native_mixture (profile : SourceBehavioralProfile core)
    (replacement : runtime.candidateApplication.PlayerPolicy)
    (environment : runtime.candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    let players := GameTheory.Profile.update
      (sig := policySignature PendingSource.Player runtime.candidateApplication)
      (fun who => compilation.compileCandidatePolicy none 3 who (profile who)) 1 replacement
    ∃ responsePairs : FinDist
        ((List runtime.candidateApplication.PlayerEntry → runtime.candidateApplication.View →
            runtime.candidateApplication.PlayerCommand) ×
          (List runtime.candidateApplication.EnvironmentEntry →
            runtime.candidateApplication.EnvironmentObservation →
            runtime.candidateApplication.EnvironmentPolicyCommand)),
      (responsePairs.bind fun responses => compilation.extractedCandidateSourceCoupling none 3 1
        responses.1 responses.2 schedule none profile).map Prod.snd =
        runtime.candidateApplication.tracePolicies players environment schedule
          (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) := by
  obtain ⟨responses, _, _, hnative, _⟩ := compilation.exists_randomized_candidate_source_coupling
    none 3 1 environment schedule none profile replacement
  exact ⟨responses, hnative⟩

end VegasTests.SealedResolutionReadBound

/-- info: 'VegasTests.SealedResolutionReadBound.hidden_first_choice' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolutionReadBound.hidden_first_choice
