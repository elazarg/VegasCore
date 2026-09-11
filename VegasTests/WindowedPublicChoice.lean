/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPublicChoicePrivacy
import Vegas.Compile.WindowedPublicChoiceInversion
import Vegas.Compile.WindowedPublicChoiceLaw
import VegasTests.ApplicationImage

/-! # Generated guarded public choice with arbitrary opposing traffic -/

noncomputable section

namespace VegasTests.WindowedPublicChoice

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage

abbrev TestPlayer := VegasTests.ApplicationImage.Player

def noBinding (code : BindingCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) := none

def noChoice (code : PublicChoiceCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.guard.ty) := none

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed (fun _ => 0) noBinding noChoice (fun _ => 10)

def initial : runtime.application.PolicyExecution :=
  applicationPlan.windowedInitialExecution (fun _ => 0) noBinding noChoice (fun _ => 10)

def players (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile (fun _ => 0) noBinding noChoice (fun _ => 10) 1
    replacement

theorem initial_reads_public : applicationPlan.InitialControllerReadsPublic := by
  apply applicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
  apply (compileCore source.prog source.fresh compilerInitial).allInitialFieldsPublic_of_owners
  intro field hfield
  change field ∈ [⟨.bool, none, true⟩] at hfield
  simp only [List.mem_singleton] at hfield
  subst field
  rfl

/-- The real first service slot accepts the guarded choice after the focal
opponent's arbitrary randomized traffic. This instance has no timeout handler;
normal generated submission alone establishes resolution. -/
theorem initial_publicChoice_inclusion
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (polled included : runtime.application.PolicyExecution)
    (hpolled : polled ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.blockEnvironment [1, 0])
      [.player 1, .player 1, .player 0, .player 0] initial).support)
    (hincluded : included ∈ (runtime.application.invoke (players profile replacement)
      (runtime.blockEnvironment [1, 0]) polled .environment).support) :
    included ∈ (runtime.application.environmentPolicyStep polled (.include (0, 0))).support ∧
      runtime.image.activeAddress? included.native.application.base.memory ≠ some 1 := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1 replacement
  obtain ⟨_, _, _, _, hinclude, hinactive⟩ :=
    checkpoint.publicChoice_ordinary_inclusion initial_reads_public
      (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide))
      polled included hpolled hincluded
  exact ⟨hinclude, hinactive⟩

/-- The pending packet comes from the source kernel and is submitted once,
even with arbitrary preceding opposing polls. -/
theorem initial_publicChoice_submission
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (polled : runtime.application.PolicyExecution)
    (hpolled : polled ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.blockEnvironment [1, 0])
      [.player 1, .player 1, .player 0, .player 0] initial).support) :
    ∃ chosen ∈ (profile 0 firstSite.decision ((source.env.toView 0).eraseEnv)).support,
      polled.native.pool.nextSerial 0 = 1 ∧
      polled.native.pool.lookup (0, 0) = some ⟨(0, 0), .choice 1 ⟨.bool, chosen.1⟩⟩ := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1 replacement
  exact checkpoint.publicChoice_ordinary_submission initial_reads_public
    (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide)) polled hpolled

def fixedDrawPolls (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) (value : Bool) :
    FinDist runtime.application.PolicyExecution :=
  (runtime.application.runPolicies (players profile replacement) (runtime.blockEnvironment [1, 0])
    [.player 1, .player 1] initial).bind fun middle =>
      (runtime.application.playerStep 0 middle (.submit (.choice 1 ⟨.bool, value⟩))).bind
        fun submitted => runtime.application.playerStep 0 submitted .wait

/-- The entire initial block, including inclusion and the normal suffix, is the
original guarded source kernel bound to its fixed-draw native branch. The
unchanged owner needs no public-choice timeout selector. -/
theorem initial_publicChoice_block_source_factorization
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    runtime.application.runPolicies (players profile replacement)
        (runtime.blockEnvironment [1, 0])
        (WindowedApplication.blockInvocations [1, 0]) initial =
      (profile 0 firstSite.decision ((source.env.toView 0).eraseEnv)).bind fun chosen =>
        (fixedDrawPolls profile replacement chosen.1).bind fun polled =>
          runtime.application.runPolicies (players profile replacement)
            (runtime.blockEnvironment [1, 0])
            [.environment, .environment, .player 1, .environment,
              .player 0, .environment] polled := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1 replacement
  have hlaw := ApplicationPlan.WindowedCheckpoint.publicChoice_block_source_factorization
    first_publicly_validatable _ profile _ initial checkpoint initial_reads_public
    (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide)) [1] [] rfl
  have haddress : compilerInitial.nodes.length + 1 = 1 := rfl
  dsimp only [compiledInitialCoupled, initialCoupledAt, checked] at hlaw
  simpa only [runtime, players, fixedDrawPolls, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append, List.cons_append, FinDist.bind_bind, haddress,
    firstSite] using hlaw

/-- A supported fixed legal source draw propagated through the complete native
branch is stored in the generated public field. -/
theorem initial_publicChoice_fixed_branch_publication
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (chosen : { value : Bool // evalGuard firstGuard value
      ((source.env.toView 0).eraseEnv) = true })
    (hchosen : chosen ∈ (profile 0 firstSite.decision
      ((source.env.toView 0).eraseEnv)).support)
    (final : runtime.application.PolicyExecution)
    (hbranch : final ∈ ((fixedDrawPolls profile replacement chosen.1).bind fun polled =>
      runtime.application.runPolicies (players profile replacement)
        (runtime.blockEnvironment [1, 0])
        [.environment, .environment, .player 1, .environment,
          .player 0, .environment] polled).support) :
    Store.getAs final.native.application.base.memory.store 2 .bool = some chosen.1 := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1 replacement
  apply checkpoint.publicChoice_fixed_branch_publication
    first_publicly_validatable _ profile _ initial final initial_reads_public
    (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide))
    [1] [] rfl chosen hchosen
  have haddress : compilerInitial.nodes.length + 1 = 1 := rfl
  simpa only [runtime, players, fixedDrawPolls, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.nil_append, List.cons_append, FinDist.bind_bind, haddress] using hbranch

/-- Actual ordinary polling determines a supported source draw and a branch
of the explicit submit/wait execution, even for a randomized raw opponent. -/
theorem initial_publicChoice_draw
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (polled : runtime.application.PolicyExecution)
    (hpolled : polled ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.blockEnvironment [1, 0])
      [.player 1, .player 1, .player 0, .player 0] initial).support) :
    ∃ value, value ∈ ((profile 0 firstSite.decision
      ((source.env.toView 0).eraseEnv)).map Subtype.val).support ∧
      polled ∈ (fixedDrawPolls profile replacement value).support := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1 replacement
  obtain ⟨value, hvalue, hbranch⟩ :=
    ApplicationPlan.WindowedCheckpoint.publicChoice_ordinary_support_value
      first_publicly_validatable _ profile _ initial polled checkpoint
      initial_reads_public (by decide) (by simp)
      (checkpoint.referenceOwner_of_ne 0 (by decide)) [1] [] rfl hpolled
  refine ⟨value, hvalue, ?_⟩
  have haddress : compilerInitial.nodes.length + 1 = 1 := rfl
  simpa only [fixedDrawPolls, runtime, players, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, MessageApplication.runPolicies, FinDist.bind_pure, haddress] using hbranch

/-- The same supported source choice gives agreeing complete native blocks
against any fixed pure raw opponent. The theorem also proves that the explicit
fixed-draw branches belong to the actual generated execution law. -/
theorem initial_publicChoice_block_agreement
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (value : Bool)
    (hvalue : value ∈ ((profile 0 firstSite.decision
      ((source.env.toView 0).eraseEnv)).map Subtype.val).support)
    (polledLeft polledRight finalLeft finalRight : runtime.application.PolicyExecution)
    (hleft : polledLeft ∈
      (fixedDrawPolls profile (fun history view => FinDist.pure (command history view))
        value).support)
    (hright : polledRight ∈
      (fixedDrawPolls profile (fun history view => FinDist.pure (command history view))
        value).support)
    (hfinalLeft : finalLeft ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [1, 0])
      [.environment, .environment, .player 1, .environment, .player 0, .environment]
      polledLeft).support)
    (hfinalRight : finalRight ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [1, 0])
      [.environment, .environment, .player 1, .environment, .player 0, .environment]
      polledRight).support) :
    WindowedApplication.PolicyAgreement runtime 1 finalLeft finalRight ∧
      finalLeft ∈ (runtime.application.runPolicies
        (players profile (fun history view => FinDist.pure (command history view)))
        (runtime.blockEnvironment [1, 0])
        (WindowedApplication.blockInvocations [1, 0]) initial).support ∧
      finalRight ∈ (runtime.application.runPolicies
        (players profile (fun history view => FinDist.pure (command history view)))
        (runtime.blockEnvironment [1, 0])
        (WindowedApplication.blockInvocations [1, 0]) initial).support := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1
    (fun history view => FinDist.pure (command history view))
  have agreement : WindowedApplication.PolicyAgreement runtime 1 initial initial :=
    ⟨⟨Vegas.ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  have haddress : compilerInitial.nodes.length + 1 = 1 := rfl
  refine ApplicationPlan.WindowedCheckpoint.publicChoice_block_agreement_of_same_draw
    first_publicly_validatable _ profile _ _ initial initial checkpoint checkpoint agreement
    initial_reads_public command rfl (by decide) (by simp) (by decide) [1] [] rfl value
    hvalue hvalue polledLeft polledRight ?_ ?_ finalLeft finalRight hfinalLeft hfinalRight
  · simpa only [fixedDrawPolls, runtime, players, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, MessageApplication.runPolicies, FinDist.bind_pure, haddress] using hleft
  · simpa only [fixedDrawPolls, runtime, players, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, MessageApplication.runPolicies, FinDist.bind_pure, haddress] using hright

def firstSuccessorState : BuildState TestPlayer simpleExpr FirstPublishedContext :=
  (((compilerInitial.addCommitEvent 1 0 firstGuard source.fresh.1).1).addRevealEvent
    2 0 .here source.fresh.2.1).1

/-- The checked mixed-type program uses an initial public field, so its node
addresses and stored field indices differ. Source-indexed comparison derives
the actual submitted Boolean without assuming a fixed execution branch. -/
theorem initial_publicChoice_block_agreement_at_source
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (value : Bool)
    (recordedLeft recordedRight : CoupledAt compiled.graph firstSuccessorState)
    (hsourceLeft : recordedLeft.current.source = (source.env.cons value).cons value)
    (hsourceRight : recordedRight.current.source = (source.env.cons value).cons value)
    (finalLeft finalRight : runtime.application.PolicyExecution)
    (hrefinesLeft : finalLeft.native.application.base.Refines recordedLeft.current.graph.1)
    (hrefinesRight : finalRight.native.application.base.Refines recordedRight.current.graph.1)
    (hfinalLeft : finalLeft ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [1, 0])
      (WindowedApplication.blockInvocations [1, 0]) initial).support)
    (hfinalRight : finalRight ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [1, 0])
      (WindowedApplication.blockInvocations [1, 0]) initial).support) :
    WindowedApplication.PolicyAgreement runtime 1 finalLeft finalRight := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked applicationPlan profile
    (fun _ => 0) noBinding noChoice (fun _ => 10) [1, 0] 1
    (fun history view => FinDist.pure (command history view))
  have agreement : WindowedApplication.PolicyAgreement runtime 1 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  exact ApplicationPlan.WindowedCheckpoint.publicChoice_block_agreement_at_source
    first_publicly_validatable _ profile _ _ initial initial finalLeft finalRight
    checkpoint checkpoint agreement initial_reads_public command rfl
    (by decide) (by simp) (by decide) value recordedLeft recordedRight
    hsourceLeft hsourceRight hrefinesLeft hrefinesRight hfinalLeft hfinalRight

end VegasTests.WindowedPublicChoice

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPublicChoice.initial_publicChoice_inclusion

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_submission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPublicChoice.initial_publicChoice_submission

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_block_source_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedPublicChoice.initial_publicChoice_block_source_factorization

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_fixed_branch_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedPublicChoice.initial_publicChoice_fixed_branch_publication

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPublicChoice.initial_publicChoice_draw

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_block_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPublicChoice.initial_publicChoice_block_agreement

/-- info: 'VegasTests.WindowedPublicChoice.initial_publicChoice_block_agreement_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPublicChoice.initial_publicChoice_block_agreement_at_source
