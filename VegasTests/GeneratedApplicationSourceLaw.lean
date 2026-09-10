/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationTimeoutForwardLaw
import Vegas.Compile.ApplicationOrderPrefix
import VegasTests.ApplicationBindingOrigins
import VegasTests.GeneratedPersistentDisclosure

/-! # Whole generated application source law

The existing persistent-disclosure plan exercises every implemented image
constructor: opaque binding, ordinary public choice, fixed chance, accounted
conditional publication, and a later conditional copy.  For an arbitrary
source behavioral profile, its actual generated invocation script and serial
service have exactly the independent source law, including completion.
-/

noncomputable section

namespace VegasTests.GeneratedApplicationSourceLaw

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

def deadlineOf : Nat → Nat := fun _ => 10

theorem initial_reads_public : applicationPlan.InitialControllerReadsPublic := by
  apply applicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
  apply (compileCore source.prog source.fresh compilerInitial).allInitialFieldsPublic_of_owners
  intro initial hinitial
  change initial ∈ [] at hinitial
  cases hinitial

/-- The exact joint completion and public-terminal law of the full generated
reference execution, for every original source behavioral profile. -/
theorem generated_source_public_law
    (profile : SourceBehavioralProfile source.prog) :
    ((((applicationPlan.image deadlineOf).application.runPolicies
      (applicationPlan.liftProfile deadlineOf profile)
      (applicationPlan.image deadlineOf).serialService
      (applicationPlan.image deadlineOf).serviceInvocations
      (applicationPlan.initialExecution deadlineOf)).map fun out =>
        (out.native.application.memory.finished (compile source).graph.nodeCount,
          (compile source).readPublicTerminal? out.native.application.memory))) =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  exact applicationPlan.service_source_public_law
    DisclosureAccounting.persistentChecked deadlineOf profile initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins

/-- Ordered admission preserves the exact randomized source law for the full
persistent-disclosure reference execution. The application uses the same
lifted profile and serial service as the unordered generated runtime. -/
theorem generated_ordered_source_public_law
    (profile : SourceBehavioralProfile source.prog) :
    ((((applicationPlan.image deadlineOf).orderedApplication.runPolicies
      (applicationPlan.liftProfile deadlineOf profile)
      (applicationPlan.image deadlineOf).serialService
      (applicationPlan.image deadlineOf).serviceInvocations
      (applicationPlan.initialExecution deadlineOf)).map fun out =>
        (out.native.application.memory.finished (compile source).graph.nodeCount,
          (compile source).readPublicTerminal? out.native.application.memory))) =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  exact applicationPlan.ordered_service_source_public_law
    DisclosureAccounting.persistentChecked deadlineOf profile initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins

/-- Both optional fallback families coexist with ordered admission on the
generated persistent-disclosure program, for arbitrary source randomization. -/
theorem generated_ordered_timeout_source_public_law
    (binding : (code : BindingCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.ty))
    (choice : (code : PublicChoiceCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.guard.ty))
    (profile : SourceBehavioralProfile source.prog) :
    (((((applicationPlan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).orderedApplication.runPolicies
      (applicationPlan.liftProfile deadlineOf profile)
      (applicationPlan.image deadlineOf).serialService
      (applicationPlan.image deadlineOf).serviceInvocations
      (applicationPlan.initialExecution deadlineOf)).map fun out =>
        (out.native.application.memory.finished (compile source).graph.nodeCount,
          (compile source).readPublicTerminal? out.native.application.memory)) =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  exact applicationPlan.ordered_timeout_service_source_public_law
    DisclosureAccounting.persistentChecked deadlineOf binding choice profile initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins

/-- The same generated program's completion and binding invariants apply to
arbitrary policies, including expiry traffic and unsuccessful submissions. -/
theorem generated_ordered_timeout_invariants
    (binding : (code : BindingCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.ty))
    (choice : (code : PublicChoiceCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.guard.ty))
    (players : Fin 2 → (applicationPlan.image deadlineOf).application.PlayerPolicy)
    (environment : (applicationPlan.image deadlineOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation (Fin 2)))
    (after : (applicationPlan.image deadlineOf).application.PolicyExecution)
    (hafter : after ∈
      ((((applicationPlan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
        choice).orderedApplication.runPolicies players environment schedule
          (applicationPlan.initialExecution deadlineOf)).support) :
    (∃ bound ≤ (compile source).graph.nodeCount,
      ∀ node, after.native.application.memory.done node = true ↔ node < bound) ∧
    (((applicationPlan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).ResolvedBindings after.native.application := by
  exact applicationPlan.ordered_timeout_runPolicies_invariants
    DisclosureAccounting.persistentChecked deadlineOf binding choice players environment
    schedule after hafter

end VegasTests.GeneratedApplicationSourceLaw

/--
info: 'VegasTests.GeneratedApplicationSourceLaw.generated_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationSourceLaw.generated_source_public_law

/-- info:
'VegasTests.GeneratedApplicationSourceLaw.generated_ordered_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationSourceLaw.generated_ordered_source_public_law

/-- info:
'VegasTests.GeneratedApplicationSourceLaw.generated_ordered_timeout_source_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationSourceLaw.generated_ordered_timeout_source_public_law

/-- info:
'VegasTests.GeneratedApplicationSourceLaw.generated_ordered_timeout_invariants' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationSourceLaw.generated_ordered_timeout_invariants
