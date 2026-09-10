/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.BindingImageExecution
import Vegas.Compile.WindowedPolicyProjection
import Vegas.Compile.WindowedBlockService

/-! # Source sampling by the actual windowed binding controller

The two consecutive ordinary owner polls privately register one source draw
and submit its fixed opaque handle. This statement retains the full native
execution and assumes no message admission or pending-pool restriction.
-/

noncomputable section

namespace Vegas.SourceDecisionSite

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {who : P} {Γ Δ : VCtx P L} {prog : VegasCore P L Γ}
variable {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}

/-- Local source/readout and service prerequisites for the two ordinary
binding polls. These are conditions on the actual initial execution, not
assumptions about either command or the resulting probability law. -/
structure WindowedBindingPollsReady
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L) (runtime : WindowedApplication P L)
    (instruction : ApplicationInstruction P L)
    (execution : runtime.application.PolicyExecution) (env : VEnv L Δ) : Prop where
  unresolved : (site.bindingCode fresh build (site.compiledField fresh build)).resolved
    execution.native.application.base.memory = false
  requires : (site.bindingCode fresh build (site.compiledField fresh build)).requires.all
    execution.native.application.base.memory.done = true
  registrationCache : image.registrationCache (site.compiledField fresh build)
    ((runtime.eraseExecution execution).principalHistory who) = none
  submissionCache : ChoiceEncoding.cachedValue image.application
    ((site.bindingCode fresh build (site.compiledField fresh build)).encoding.submission
      image.application) ((runtime.eraseExecution execution).principalHistory who) = none
  readout : ∃ reads,
    image.ownerReadout? who
      (eventGuardOf (decisionSiteState site fresh build) who guard).choiceReads
      ((runtime.eraseExecution execution).principalHistory who)
      (State.observe image.application (runtime.eraseExecution execution).native who) =
        some reads ∧
      viewEnvOfReadEnv (decisionSiteState site fresh build) who reads = (env.toView who).eraseEnv
  index : runtime.image.instructions[(execution.principalHistory who).length / 3]? =
    some instruction
  active : runtime.image.activeAddress? execution.native.application.base.memory =
    some instruction.address
  slot : (execution.principalHistory who).length % 3 = 0
  owner : instruction.submitter = some who

/-- The actual block-gated binding controller samples once and emits its
opaque handle on the second poll. The unchanged source kernel may be
behavioral; no command or execution-law equality is an input hypothesis. -/
theorem windowedBinding_two_invocations_source_law
    (site : SourceDecisionSite who prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : BuildState P L Γ)
    (image : ApplicationImage P L) (runtime : WindowedApplication P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx who Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (base : image.application.PlayerPolicy)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (howner : players who = runtime.blockPlayer who (runtime.liftPlayerPolicy base))
    (instruction : ApplicationInstruction P L)
    (execution : runtime.application.PolicyExecution) (env : VEnv L Δ)
    (hdispatch : ∀ history,
      base history (State.observe image.application (runtime.eraseExecution execution).native who) =
        site.bindingPolicy fresh build image sourcePolicy history
          (State.observe image.application (runtime.eraseExecution execution).native who))
    (ready : site.WindowedBindingPollsReady fresh build image runtime instruction execution env) :
    runtime.application.runPolicies players environment [.player who, .player who] execution =
      (sourcePolicy ((env.toView who).eraseEnv)).bind fun chosen =>
        (runtime.application.playerStep who execution
          (.privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩))).bind
            fun registered => runtime.application.playerStep who registered
              (.submit (.binding
                (site.bindingCode fresh build (site.compiledField fresh build)).node
                (who, site.compiledField fresh build))) := by
  obtain ⟨reads, hreadout, hview⟩ := ready.readout
  have hsource := site.bindingPolicy_first_registration_source_law fresh build image sourcePolicy
    ((runtime.eraseExecution execution).principalHistory who)
    (State.observe image.application (runtime.eraseExecution execution).native who)
    env reads ready.unresolved ready.requires ready.registrationCache hreadout hview
  have hfirst : players who (execution.principalHistory who)
      (State.observe runtime.application execution.native who) =
        (sourcePolicy ((env.toView who).eraseEnv)).map fun chosen =>
          .privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩) := by
    rw [howner, runtime.blockPlayer_normal who _ _ _ instruction ready.index ready.active
      (by rw [ready.slot]; decide) ready.owner]
    change (base
      ((runtime.eraseExecution execution).principalHistory who)
      (State.observe image.application (runtime.eraseExecution execution).native who)).map
        runtime.liftPlayerCommand = _
    rw [hdispatch, hsource]
    simp only [FinDist.map_comp, Function.comp_def, WindowedApplication.liftPlayerCommand]
  simp only [MessageApplication.runPolicies, MessageApplication.invoke]
  rw [hfirst, FinDist.bind_map, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro chosen _
  apply FinDist.bind_congr
  intro registered hregistered
  have hobserve : State.observe runtime.application registered.native who =
      State.observe runtime.application execution.native who := by
    simp only [MessageApplication.playerStep, PlayerCommand.toAction,
      MessageApplication.advance, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hregistered
    subst registered
    rfl
  have hhistory := runtime.application.playerStep_history_self who execution
    (.privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩))
    registered hregistered
  have hlength : (registered.principalHistory who).length =
      (execution.principalHistory who).length + 1 := by
    rw [hhistory, List.length_append]
    rfl
  have hslot : (registered.principalHistory who).length % 3 < 2 := by
    rw [hlength]
    have hzero := ready.slot
    omega
  have hindex : runtime.image.instructions[(registered.principalHistory who).length / 3]? =
      some instruction := by
    rw [hlength, show ((execution.principalHistory who).length + 1) / 3 =
      (execution.principalHistory who).length / 3 by have hzero := ready.slot; omega]
    exact ready.index
  have hactive : runtime.image.activeAddress?
      (State.observe runtime.application registered.native who).application.1 =
        some instruction.address := by
    rw [hobserve]
    exact ready.active
  have hbaseStep := runtime.playerStep_erased_support image who execution registered
    (.privateCommand (.register (site.compiledField fresh build) ⟨ty, chosen.1⟩)) hregistered
  have hsecond := site.bindingPolicy_after_registration fresh build image sourcePolicy
    (runtime.eraseExecution execution) (runtime.eraseExecution registered) chosen.1
    ready.registrationCache ready.unresolved ready.requires ready.submissionCache hbaseStep
  have hprojectedObserve :
      State.observe image.application (runtime.eraseExecution registered).native who =
        State.observe image.application (runtime.eraseExecution execution).native who :=
    congrArg runtime.eraseView hobserve
  have hnextCommand : players who (registered.principalHistory who)
      (State.observe runtime.application registered.native who) = FinDist.pure
        (.submit (.binding (site.bindingCode fresh build (site.compiledField fresh build)).node
          (who, site.compiledField fresh build))) := by
    rw [howner, runtime.blockPlayer_normal who _ _ _ instruction hindex hactive hslot ready.owner]
    change (base
      ((runtime.eraseExecution registered).principalHistory who)
      (State.observe image.application (runtime.eraseExecution registered).native who)).map
        runtime.liftPlayerCommand = _
    rw [hprojectedObserve, hdispatch, ← hprojectedObserve, hsecond, FinDist.map_pure]
    rfl
  rw [hnextCommand]
  simp only [FinDist.pure_bind, FinDist.bind_pure]

end Vegas.SourceDecisionSite

/-- info: 'Vegas.SourceDecisionSite.windowedBinding_two_invocations_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionSite.windowedBinding_two_invocations_source_law
