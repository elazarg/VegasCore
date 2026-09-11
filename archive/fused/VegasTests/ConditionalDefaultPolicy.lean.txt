/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ConditionalImageController
import VegasTests.ConditionalDefaultApplication

/-! # Controller selection after a public binding default

The owner previously prepared `true`, while the accepted public fallback is
`false`.  The dynamic generated policy reads the authoritative disposition,
runs the unchanged source choice on `false`, and emits typed cleartext rather
than an opening or the private cached value.
-/

noncomputable section

namespace VegasTests.ConditionalDefaultPolicy

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalDefaultApplication

abbrev Player := ConditionalApplicationImage.Player

def sourcePolicy
    (visible : Env simpleExpr.Val
      (eraseVCtx (viewVCtx (0 : Player) OpeningContext))) :
    FinDist { value : Option Bool // evalGuard openingGuard value visible = true } :=
  FinDist.pure ⟨some (visible.get .here), by
    change decide (some (visible.get .here) = some (visible.get .here)) = true
    simp⟩

/-- The history is the real private command made before the binding expiry.
Its cached value conflicts with the later authoritative public default. -/
def ownerHistory : List timedImage.application.PlayerEntry :=
  [⟨MessageApplication.State.observe timedImage.application
      (MessageApplication.State.initial timedImage.application initialNative) 0,
    .privateCommand (.register 0 ⟨.bool, true⟩)⟩]

def policy : timedImage.application.PlayerPolicy :=
  conditionalSite.imagePolicy source.fresh compilerInitial 0 10 timedImage
    (timedImage.ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads)
    sourcePolicy (fun _ _ => false)

def defaultView : timedImage.application.View :=
  MessageApplication.State.observe timedImage.application defaultIncluded 0

def openingEnv : VEnv simpleExpr OpeningContext :=
  (VEnv.empty simpleExpr).cons false

/-- The actual accepted disposition selects the strict cleartext codec.  The
private registration is not substituted for the public fallback. -/
theorem policy_emits_public_default :
    policy ownerHistory defaultView =
      FinDist.pure (.submit (.conditional (conditionalCode 10).endpoint.publicationNode
        (.cleartext ⟨.bool, false⟩))) := by
  let store := timedImage.ownerReadStore 0 ownerHistory defaultView.application
  have hagrees : (conditionalSite.choice.siteState source.fresh compilerInitial).ViewAgrees
      0 store openingEnv := by
    intro name bindTy binding
    cases binding with
    | here => rfl
    | there impossible => cases impossible
  have havailable : ∀ ref,
      ref ∈ (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads →
        ∃ value, Store.getAs store ref.field ref.ty = some value := by
    intro ref href
    change ref ∈ ({({ field := 0, ty := .bool } : FieldRef simpleExpr)} :
      Finset (FieldRef simpleExpr)) at href
    have hrefEq : ref = ({ field := 0, ty := .bool } : FieldRef simpleExpr) := by
      simpa using href
    subst ref
    exact ⟨false, hagrees (.here)⟩
  let reads := ReadEnv.ofStore store
    (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads havailable
  have hreads : ReadEnv.ofStore? store
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads =
        some reads := by
    unfold ReadEnv.ofStore?
    rw [dif_pos havailable]
  have hreadout : timedImage.ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads
      ownerHistory defaultView = some reads :=
    ReadEnv.ofStoreExec?_eq_some_of_ofStore?_eq_some hreads
  have hlaw := conditionalSite.imagePolicy_first_submission_source_law
    source.fresh compilerInitial 0 10 timedImage (.publicDefault false)
    (timedImage.ownerReadout? 0
      (conditionalSite.choice.compiledGuard source.fresh compilerInitial).choiceReads)
    sourcePolicy (fun _ _ => false) ownerHistory defaultView store openingEnv reads
    (by rfl) (by rfl) (by rfl) (by rfl) hreadout hagrees hreads
  change policy ownerHistory defaultView = _ at hlaw
  rw [hlaw]
  simp only [sourcePolicy, FinDist.map_pure]
  rfl

theorem policy_does_not_emit_opening :
    .submit (.conditional (conditionalCode 10).endpoint.publicationNode
      (.opening (0, 0) ⟨.bool, true⟩)) ∉ (policy ownerHistory defaultView).support := by
  rw [policy_emits_public_default]
  simp only [FinDist.mem_support_pure]
  intro heq
  cases heq

def execution : timedImage.application.PolicyExecution where
  native := defaultIncluded
  principalHistory who := if who = 0 then ownerHistory else []
  environmentHistory := []
  nativeTrace := []

def players : Player → timedImage.application.PlayerPolicy := fun who =>
  if who = 0 then policy else fun _ _ => FinDist.pure .wait

def environment : timedImage.application.EnvironmentPolicy :=
  fun _ _ => FinDist.pure .wait

/-- The dynamic policy is exercised by the shared policy runner, producing
one real pending cleartext packet with the owner's next serial. -/
theorem player_invocation_submits_cleartext :
    timedImage.application.runPolicies players environment [.player 0] execution =
      timedImage.application.playerStep 0 execution
        (.submit (.conditional (conditionalCode 10).endpoint.publicationNode
          (.cleartext ⟨.bool, false⟩))) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, players, if_pos]
  have hpolicy : policy (execution.principalHistory 0)
      (MessageApplication.State.observe timedImage.application execution.native 0) =
      FinDist.pure (.submit (.conditional (conditionalCode 10).endpoint.publicationNode
        (.cleartext ⟨.bool, false⟩))) := by
    change policy ownerHistory defaultView = _
    exact policy_emits_public_default
  rw [hpolicy, FinDist.pure_bind, FinDist.bind_pure]

end VegasTests.ConditionalDefaultPolicy

/-- info: 'VegasTests.ConditionalDefaultPolicy.policy_emits_public_default' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultPolicy.policy_emits_public_default

/-- info: 'VegasTests.ConditionalDefaultPolicy.player_invocation_submits_cleartext'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDefaultPolicy.player_invocation_submits_cleartext
