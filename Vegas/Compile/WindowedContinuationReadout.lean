/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationContinuationReadout
import Vegas.Compile.WindowedApplicationCoverage
import Vegas.Compile.WindowedBlockProvenance

/-! # Source readout at a windowed structural continuation

An unchanged owner retains its executable source readout after an arbitrary
activation-windowed prefix. Other players and the environment remain arbitrary.
-/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At a ready coupled source checkpoint, the actual erased windowed history
and view recover the unchanged owner's complete source-visible environment. -/
theorem windowed_ownerReadout?_of_ready_source_view
    {rootContext Γ Δ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {plan : ApplicationPlan accounted fresh state}
    {rootProfile : SourceBehavioralProfile rootProg}
    {profile : SourceBehavioralProfile prog}
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (who : P)
    (players : P →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (hcommands : ∀ history view command, command ∈ (players who history view).support →
      (root.windowed deadlineOf binding choice windowOf).erasePlayerCommand command ∈
          (root.liftProfile deadlineOf rootProfile who
            (history.map (root.windowed deadlineOf binding choice windowOf).erasePlayerEntry)
            ((root.windowed deadlineOf binding choice windowOf).eraseView view)).support ∨
        (root.windowed deadlineOf binding choice windowOf).image.IdleOrExpiryCommand
          ((root.windowed deadlineOf binding choice windowOf).erasePlayerCommand command))
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (next : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnext : next ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        players environment schedule
        (PolicyExecution.initial
          (root.windowed deadlineOf binding choice windowOf).application
          (MessageApplication.State.initial
            (root.windowed deadlineOf binding choice windowOf).application
            ((root.windowed deadlineOf binding choice windowOf).initial
              (ApplicationImage.State.initial
                (ApplicationImage.Memory.initial
                  (compileCore rootProg rootFresh rootState).graph)))))).support)
    {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Δ)) L.bool}
    (site : SourceDecisionSite who prog Δ name ty guard)
    (cfg : Config (compileCore prog fresh state).graph)
    (hrefines : next.native.application.base.Refines cfg)
    (hready : Ready (compileCore prog fresh state).graph cfg
      (site.compiledNode fresh state))
    (hinitial : ∀ ref ∈
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      ∀ spec, (compileCore prog fresh state).graph.field? ref.field = some spec →
        ∀ value, spec.source = .initial value → spec.owner = none)
    (env : VEnv L Δ)
    (hagrees : (decisionSiteState site fresh state).ViewAgrees who cfg.store env) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    ∃ reads : ReadEnv L
        (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads,
      runtime.image.ownerReadout? who
          (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads
          ((next.principalHistory who).map fun entry =>
            show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
          (runtime.eraseView
            (MessageApplication.State.observe runtime.application next.native who)) =
        some reads ∧
      ReadEnv.ofStore? cfg.store
          (eventGuardOf (decisionSiteState site fresh state) who guard).choiceReads =
        some reads ∧
      viewEnvOfReadEnv (decisionSiteState site fresh state) who reads =
        (env.toView who).eraseEnv := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  have hcoversRoot := root.windowed_runPolicies_memory_covers deadlineOf binding choice
    windowOf players environment schedule next hnext
  have hcovers : next.native.application.base.memory.Covers
      (compileCore prog fresh state).graph.initialFields.length := by
    change next.native.application.base.memory.Covers
      (compileCore prog fresh state).initialFields.length
    rw [← continuation.compile_eq]
    simpa only [compileCore_initialFields] using hcoversRoot
  have hbindingsRoot := root.windowed_registeredBindings_of_source_commands deadlineOf binding
    choice windowOf rootProfile who players hcommands environment schedule next hnext
  have hbindings : runtime.image.RegisteredBindings who
      (fun slot typed => ∃ spec : FieldSpec P L,
        (compileCore prog fresh state).graph.field? slot = some spec ∧ typed.ty = spec.ty)
      ((next.principalHistory who).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      next.native.application.base := by
    rw [← continuation.compile_eq]
    exact hbindingsRoot
  obtain ⟨reads, hreadout, hview⟩ :=
    site.ownerReadout?_of_ready_source_view fresh state runtime.image
      ((next.principalHistory who).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      (runtime.eraseView
        (MessageApplication.State.observe runtime.application next.native who))
      next.native.application.base rfl cfg hrefines hcovers hbindings hready hinitial env hagrees
  refine ⟨reads, hreadout, ?_, hview⟩
  exact site.ownerReadout?_graph_reads fresh state runtime.image
    ((next.principalHistory who).map fun entry =>
      show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
    (runtime.eraseView
      (MessageApplication.State.observe runtime.application next.native who))
    next.native.application.base rfl cfg hrefines hbindings.registrationMatches reads hreadout

end Vegas.ApplicationPlan.ProfileContinuation

/-- info:
'Vegas.ApplicationPlan.ProfileContinuation.windowed_ownerReadout?_of_ready_source_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.ProfileContinuation.windowed_ownerReadout?_of_ready_source_view
