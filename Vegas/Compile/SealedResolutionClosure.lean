/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.SealedResolutionAdmission
import Vegas.Compile.SealedResolutionPolicy
import Interaction.SealedResolutionClosure

/-! # Default-propagation closure for compiled resolution

Compiler admission discharges the source-order premises of the native closure
law.  Consequently every supported execution from the canonical initial state
has propagated earlier commitment defaults to ready reveal nodes.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Arbitrary randomized native policies preserve default-propagation closure
for a compiled sealed fragment started from its canonical initial state. -/
theorem resolvingRuntime_runPolicies_resolutionClosed
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hnext : next ∈
      ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
        players environment schedule
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _
            (supported.resolvingRuntime nullValue window).initial))).support) :
    next.native.application.visible.ResolutionClosed
      (supported.resolvingRuntime nullValue window) := by
  let runtime := supported.resolvingRuntime nullValue window
  have hbackward : ∀ (node : Nat) (rule : SealedRule Player),
      runtime.program.rules[node]? = some rule →
      ∀ prerequisite ∈ rule.requires, prerequisite < node := by
    intro node rule hrule prerequisite hprerequisite
    exact supported.compile_rule_requires_lt hrule hprerequisite
  have hsource : ∀ (node : Nat) (owner : Player) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some { kind := .reveal owner source, requires } →
      source < node := by
    intro node owner source requires hrule
    exact supported.compile_reveal_source_lt hrule rfl
  apply runtime.runPolicies_resolutionClosed
    (fun (service : IdealCommitments Player Nat (L.Val ty)) owner slot value =>
      (service.sealValue owner slot value).state)
    runtime.handle runtime.handle_records hbackward hsource players environment schedule
    (MessageApplication.PolicyExecution.initial _
      (MessageApplication.State.initial _ runtime.initial)) next
    (Interaction.SealedResolution.PublicState.ResolutionClosed.initial hbackward hsource)
  exact hnext

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingRuntime_runPolicies_resolutionClosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraph.SealedFragment.resolvingRuntime_runPolicies_resolutionClosed
