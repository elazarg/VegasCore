/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.WindowedForwardLaw
import VegasTests.GeneratedApplicationSourceLaw

/-! # Generated windowed application source law

The mixed-feature persistent-disclosure plan instantiates the activation-relative
windowed reference law for an arbitrary source behavioral profile and window
policy.
-/

noncomputable section

namespace VegasTests.WindowedForwardLaw

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

/-- The actual compiler-generated windowed runtime for the mixed-feature fixture
has the exact joint completion and public-terminal source law. -/
theorem generated_windowed_source_public_law
    (binding : (code : BindingCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.ty))
    (choice : (code : PublicChoiceCode (Fin 2) simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.guard.ty))
    (windowOf : Nat → Nat)
    (profile : SourceBehavioralProfile source.prog) :
    let runtime := applicationPlan.windowed
      GeneratedApplicationSourceLaw.deadlineOf binding choice windowOf
    let players := applicationPlan.liftProfile
      GeneratedApplicationSourceLaw.deadlineOf profile
    let environment :=
      (applicationPlan.image GeneratedApplicationSourceLaw.deadlineOf).serialService
    let execution := PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application
        (runtime.initial (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (compile source).graph))))
    (runtime.application.runPolicies
      (fun who => runtime.liftPlayerPolicy (players who))
      (runtime.liftEnvironmentPolicy environment)
      (applicationPlan.image
        GeneratedApplicationSourceLaw.deadlineOf).serviceInvocations execution).map
        (fun out =>
          (out.native.application.base.memory.finished (compile source).graph.nodeCount,
            (compile source).readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource source.prog profile source.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv simpleExpr)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.prog source.fresh
            compilerInitial).symm) terminal).erasePubEnv) := by
  exact applicationPlan.windowed_service_source_public_law
    DisclosureAccounting.persistentChecked GeneratedApplicationSourceLaw.deadlineOf
    binding choice windowOf profile GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins

end VegasTests.WindowedForwardLaw

/-- info:
'VegasTests.WindowedForwardLaw.generated_windowed_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedForwardLaw.generated_windowed_source_public_law
