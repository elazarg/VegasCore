/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheoryExtensions.Core.MixtureSimulation
import Vegas.Language.Nullable
import Vegas.Compile.SealedCompiler
import Vegas.Compile.SealedTimeoutRefinement
import Vegas.Game.SealedMessages
import Vegas.Game.SealedRelease
import Vegas.Game.SealedStrategic

/-! # Paper theorem audit

This file is deliberately a thin audit surface. Every closed statement below
delegates directly to a theorem in the active source, graph, or sealed-message
tower. Strategic preservation is stated through the explicit
`StrategicCertificate`: the runtime must provide the honest law and the
finite-mixture law for its considered unilateral deviations.

The pending-message backtranslation for the concrete policy runtime is an open
research obligation. It is not represented here as a theorem with an
unjustified universal conclusion; the certificate interface records exactly
what that proof must construct.
-/

namespace Vegas.Paper

open GameTheory Vegas EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

theorem sealed_rule_count
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty) :
    compilation.program.rules.length =
      (ToEventGraph.compile source.core).graph.nodeCount :=
  compilation.program_rule_count

theorem sealed_source_prefix
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty)
    (actions : List (SealedProgram.Action Player (L.Val ty))) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (SealedProgram.run compilation.program
          (SealedProgram.State.empty Player (L.Val ty)) actions) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ := compilation.run_source actions
  exact ⟨cfg, hdecode, hreachable⟩

theorem sealed_policy_prefix
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (players : Player →
      (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment :
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution :
      (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmem : execution ∈
      ((MessageApplication.policyGame
        (supported.compile.messageApplication (Value := L.Val ty)) environment schedule
        (MessageApplication.State.initial
          (supported.compile.messageApplication (Value := L.Val ty))
          ⟨IdealCommitments.empty, []⟩)).play players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (supported.compile.eraseReceipts execution.native) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg := by
  obtain ⟨cfg, hdecode, hreachable, _⟩ :=
    WFProgram.sealed_policy_source source ty supported players environment schedule
      execution hmem
  exact ⟨cfg, hdecode, hreachable⟩

theorem sealed_cleartext_rejected
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (compilation : SealedCompilation source ty)
    (state : SealedProgram.State Player (L.Val ty))
    (message : Message Player (SealedProgram.Payload Player (L.Val ty)))
    (node : Nat) (value : L.Val ty)
    (hpayload : message.payload = .cleartext node value) :
    SealedProgram.handle compilation.program state message = state :=
  SealedProgram.handle_cleartext compilation.program state message node value hpayload

/-- The source surface has an explicit, always-legal nullable quit value. -/
theorem nullable_quit_is_legal
    {Γ : VCtx Player simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (guard : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (visible : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := Player) (L := simpleExpr)
        (Expr.nullableCommitGuard guard) Option.none visible = true :=
  VegasLang.nullableGuard_none_legal guard visible

theorem sealed_opening_prerequisites
    {source : WFProgram Player L} {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (owner : Player) (node : Fin (ToEventGraph.compile source.core).graph.nodeCount)
    (value : L.Val ty)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hnonwait : SealedProgram.openingCommand supported.compile owner node.val value view ≠
      .wait) :
    ∀ prior, prior ∈ (ToEventGraph.compile source.core).graph.prereqs node →
      SealedProgram.done view.application prior.val = true :=
  supported.openingCommand_prerequisites owner node value view hnonwait

theorem sealed_nash_preservation
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty)
    {Observation : Type}
    {target : GameForm Player}
    (sourceObserve :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (certificate : compilation.StrategicCertificate target sourceObserve targetObserve Considered)
    (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target (fun outcome who => value (targetObserve outcome) who) ε
        (certificate.simulation.compileProfile profile) ↔
      IsεNash (Vegas.sourceGameForm source.core.prog source.core.env)
        (fun outcome who => value (sourceObserve outcome) who) ε profile :=
  certificate.isεNash_compileProfile_iff value ε profile hall

theorem sealed_quit_dominance_transfer
    {source : WFProgram Player L} {ty : L.Ty}
    (compilation : SealedCompilation source ty)
    {Observation : Type}
    {target : GameForm Player}
    (sourceObserve :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop)
    (certificate : compilation.StrategicCertificate target sourceObserve targetObserve Considered)
    (value : Observation → Player → ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (who : Player)
    (quit preferred : SourceBehavioralPolicy source.core.prog who)
    (quitTarget : target.sig.Strategy who)
    (hquit :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) =
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who))
    (hstrict :
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who) <
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who preferred)).expect
          (fun outcome => value (sourceObserve outcome) who)) :
    ¬ IsNash target
      (euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget) :=
  certificate.compiled_quit_profile_not_isNash_of_quit_law
    value profile who quit preferred quitTarget hquit hstrict

end Vegas.Paper

/-- info: 'Vegas.Paper.sealed_rule_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_rule_count

/-- info: 'Vegas.Paper.sealed_source_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_source_prefix

/-- info: 'Vegas.Paper.sealed_policy_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_policy_prefix

/-- info: 'Vegas.Paper.sealed_cleartext_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_cleartext_rejected

/-- info: 'Vegas.Paper.nullable_quit_is_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.nullable_quit_is_legal

/-- info: 'Vegas.Paper.sealed_opening_prerequisites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_opening_prerequisites

/-- info: 'Vegas.Paper.sealed_nash_preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_nash_preservation

/-- info: 'Vegas.Paper.sealed_quit_dominance_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Paper.sealed_quit_dominance_transfer
