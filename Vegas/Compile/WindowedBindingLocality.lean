/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyPrivacy
import Vegas.Compile.WindowedBindingExecution

/-! # Locality of an unchanged binding owner's two polls

This file isolates the privacy argument for the two consecutive ordinary
binding polls. The private registrations may contain different source values;
the subsequent public commands nevertheless agree because a binding packet
contains only the compiler-fixed owner and source slot.
-/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication
open GameTheory.Math.Probability
open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal owner : P}
variable {left right : runtime.application.PolicyExecution}

/-- Two ordinary polls of a nonfocal binding owner preserve the focal policy
input even when the owner's private source samples differ. This is the local
segment used after the emitted binding controller has established that its
first commands are registrations at `code.sourceSlot` and its second commands
are the common opaque binding submission.

No acceptance fact is needed here: player submission only appends the common
packet to the two equal pools. A later environment inclusion requires its own
admission/source-coupling proof. -/
private theorem binding_twoPoll_other (agreement : PolicyAgreement runtime focal left right)
    (howner : owner ≠ focal) (code : BindingCode P L)
    (leftValue rightValue : L.Val code.ty)
    (leftRegistered rightRegistered leftSubmitted rightSubmitted :
      runtime.application.PolicyExecution)
    (hleftRegister : leftRegistered ∈
      (runtime.application.playerStep owner left
        (.privateCommand (.register code.sourceSlot ⟨code.ty, leftValue⟩))).support)
    (hrightRegister : rightRegistered ∈
      (runtime.application.playerStep owner right
        (.privateCommand (.register code.sourceSlot ⟨code.ty, rightValue⟩))).support)
    (hleftSubmit : leftSubmitted ∈
      (runtime.application.playerStep owner leftRegistered
        (.submit (.binding code.node (owner, code.sourceSlot)))).support)
    (hrightSubmit : rightSubmitted ∈
      (runtime.application.playerStep owner rightRegistered
        (.submit (.binding code.node (owner, code.sourceSlot)))).support) :
    PolicyAgreement runtime focal leftSubmitted rightSubmitted := by
  have registered := agreement.playerStep_register_other owner howner
    code.sourceSlot code.sourceSlot (⟨code.ty, leftValue⟩ : TypedValue L)
    (⟨code.ty, rightValue⟩ : TypedValue L) leftRegistered rightRegistered
    hleftRegister hrightRegister
  exact registered.playerStep_submit_other owner howner
    (.binding code.node (owner, code.sourceSlot)) leftSubmitted rightSubmitted
    hleftSubmit hrightSubmit

/-- Behavioral source kernels may choose different private values in the two
runs. Once the actual generated two-invocation laws have been established,
every pair of supported outcomes still agrees at the focal player. The laws
are exactly the conclusions of `bindingPolicy_two_invocations_source_law`
(or its windowed dispatcher specialization); no pure source policy or command
equality is assumed. -/
private theorem binding_twoRunLaw_other
    (agreement : PolicyAgreement runtime focal left right)
    (howner : owner ≠ focal) (code : BindingCode P L)
    (leftChoices rightChoices : FinDist (L.Val code.ty))
    (leftPlayers rightPlayers : P → runtime.application.PlayerPolicy)
    (leftEnvironment rightEnvironment : runtime.application.EnvironmentPolicy)
    (leftSubmitted rightSubmitted : runtime.application.PolicyExecution)
    (hleftLaw : runtime.application.runPolicies leftPlayers leftEnvironment
      [.player owner, .player owner] left = leftChoices.bind fun value =>
        (runtime.application.playerStep owner left
          (.privateCommand (.register code.sourceSlot ⟨code.ty, value⟩))).bind fun registered =>
            runtime.application.playerStep owner registered
              (.submit (.binding code.node (owner, code.sourceSlot))))
    (hrightLaw : runtime.application.runPolicies rightPlayers rightEnvironment
      [.player owner, .player owner] right = rightChoices.bind fun value =>
        (runtime.application.playerStep owner right
          (.privateCommand (.register code.sourceSlot ⟨code.ty, value⟩))).bind fun registered =>
            runtime.application.playerStep owner registered
              (.submit (.binding code.node (owner, code.sourceSlot))))
    (hleft : leftSubmitted ∈ (runtime.application.runPolicies leftPlayers
      leftEnvironment [.player owner, .player owner] left).support)
    (hright : rightSubmitted ∈ (runtime.application.runPolicies rightPlayers
      rightEnvironment [.player owner, .player owner] right).support) :
    PolicyAgreement runtime focal leftSubmitted rightSubmitted := by
  rw [hleftLaw] at hleft
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleft
  obtain ⟨leftValue, hleftValue, leftRegistered, hleftRegister, hleftSubmit⟩ := hleft
  rw [hrightLaw] at hright
  simp only [FinDist.support_bind, Set.mem_iUnion] at hright
  obtain ⟨rightValue, hrightValue, rightRegistered, hrightRegister, hrightSubmit⟩ := hright
  clear hleftValue hrightValue
  exact agreement.binding_twoPoll_other howner code leftValue rightValue leftRegistered
    rightRegistered leftSubmitted rightSubmitted hleftRegister hrightRegister hleftSubmit
    hrightSubmit

/-- Actual generated binding polls preserve the observer's information for
every pair of supported source draws. Readiness and cache conditions concern
the two initial executions; both execution laws are derived internally from
the emitted controller. The two source inputs and sampled values may differ.
This stops before inclusion, where acceptance and public receipts need their
own source-indexed information comparison. -/
theorem binding_twoPolls_of_ready
    {Γ Δ : VCtx P L} {prog : VegasCore P L Γ} {name : VarId} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Δ)) L.bool}
    (agreement : PolicyAgreement runtime focal left right)
    (howner : owner ≠ focal)
    (site : SourceDecisionSite owner prog Δ name ty guard)
    (fresh : FreshBindings prog) (build : ToEventGraph.BuildState P L Γ)
    (image : ApplicationImage P L)
    (sourcePolicy : (visible : Env L.Val (eraseVCtx (viewVCtx owner Δ))) →
      FinDist { value : L.Val ty // evalGuard guard value visible = true })
    (base : image.application.PlayerPolicy)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (hpolicy : players owner = runtime.blockPlayer owner (runtime.liftPlayerPolicy base))
    (instruction : ApplicationInstruction P L) (leftEnv rightEnv : VEnv L Δ)
    (leftReady : site.WindowedBindingPollsReady fresh build image runtime instruction left leftEnv)
    (rightReady : site.WindowedBindingPollsReady fresh build image runtime instruction right
      rightEnv)
    (hleftDispatch : ∀ history,
      base history (State.observe image.application (runtime.eraseExecution left).native owner) =
        site.bindingPolicy fresh build image sourcePolicy history
          (State.observe image.application (runtime.eraseExecution left).native owner))
    (hrightDispatch : ∀ history,
      base history (State.observe image.application (runtime.eraseExecution right).native owner) =
        site.bindingPolicy fresh build image sourcePolicy history
          (State.observe image.application (runtime.eraseExecution right).native owner))
    (leftSubmitted rightSubmitted : runtime.application.PolicyExecution)
    (hleft : leftSubmitted ∈ (runtime.application.runPolicies players
      environment [.player owner, .player owner] left).support)
    (hright : rightSubmitted ∈ (runtime.application.runPolicies players
      environment [.player owner, .player owner] right).support) :
    PolicyAgreement runtime focal leftSubmitted rightSubmitted := by
  apply agreement.binding_twoRunLaw_other howner
    (site.bindingCode fresh build (site.compiledField fresh build))
    ((sourcePolicy ((leftEnv.toView owner).eraseEnv)).map Subtype.val)
    ((sourcePolicy ((rightEnv.toView owner).eraseEnv)).map Subtype.val)
    players players environment environment leftSubmitted rightSubmitted _ _ hleft hright
  · simpa only [FinDist.bind_map, SourceDecisionSite.bindingCode] using
      site.windowedBinding_two_invocations_source_law
      fresh build image runtime sourcePolicy base players environment hpolicy instruction left
        leftEnv hleftDispatch leftReady
  · simpa only [FinDist.bind_map, SourceDecisionSite.bindingCode] using
      site.windowedBinding_two_invocations_source_law
      fresh build image runtime sourcePolicy base players environment hpolicy instruction right
        rightEnv hrightDispatch rightReady

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.binding_twoPolls_of_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.binding_twoPolls_of_ready
