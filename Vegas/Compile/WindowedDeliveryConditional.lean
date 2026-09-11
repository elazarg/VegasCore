/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedHeadSourceCoupling
import Vegas.Compile.WindowedConditionalBlock
import Vegas.Compile.WindowedDeliveryProgress

/-! # Source coupling for resolved delivery conditional segments -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A resolving delivery-service segment at a conditional head carries the
source optional result to the source successor. The actual schedule and raw
player policies remain unrestricted; public validation is the compiler-side
certificate used by the handler coupling. -/
theorem runPolicies_delivery_conditional_source_coupling
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy) (schedule : List (@Invocation P))
    {Γ : VCtx P L} {name publicName : VarId} {owner : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ))
    (spec : ConditionalOpening guard)
    (fresh : FreshBindings
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh build).graph build)
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh build)
    (sourceSlot deadline : Nat)
    (execution final : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (recipients.length + roster.length + 2)]? =
        some (.conditional
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.code fresh build sourceSlot deadline)))
    (hlookup : runtime.image.lookup
      ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code
        fresh build sourceSlot deadline).endpoint.publicationNode = some (.conditional
      ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code
        fresh build sourceSlot deadline)))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code
        fresh build sourceSlot deadline).endpoint.publicationNode)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key =
      ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).choice
        |>.publicationNode fresh build))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec).code
        fresh build sourceSlot deadline).endpoint.publicationNode)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) fresh build).graph
        (((build.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
      evalGuard guard (spec.encoding.symm result)
        ((current.current.source.toView owner).eraseEnv) = true ∧
      sourceNext.current.source =
        (current.current.source.cons (spec.encoding.symm result)).cons
          (spec.encoding.symm result) ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation := by
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh build sourceSlot deadline
  let Witness := { pair : Option (L.Val spec.secretTy) × CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh build).graph
      (((build.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1 //
    (pair.1 = none ∨ pair.1 = some (current.current.source.get spec.binding)) ∧
      evalGuard guard (spec.encoding.symm pair.1)
        ((current.current.source.toView owner).eraseEnv) = true ∧
      pair.2.current.source =
        (current.current.source.cons (spec.encoding.symm pair.1)).cons
          (spec.encoding.symm pair.1) }
  let target : Witness → Config
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh build).graph := fun witness => witness.1.2.current.graph.1
  obtain ⟨witness, hnextRefines, hnextFresh, _⟩ :=
    runtime.runPolicies_head_source_witness players
      (runtime.deliveryBlockEnvironment roster recipients) schedule
      (fun index => runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some (.conditional code))
      code.endpoint.publicationNode current.current.graph.1 execution final activation
      Witness target (fun _ _ => True) hindex
      (fun state command hindex hcommand =>
        runtime.deliveryBlockEnvironment_command_not_sample roster recipients state
          (.conditional code) owner hindex rfl command hcommand)
      (by
        intro state message resolved hactivation hrefines hhandle
        obtain ⟨result, sourceNext, hresult, hlegal, hsource, hresolved⟩ :=
          runtime.handle_conditional_source_coupling guard tail spec fresh build
            sourceSlot deadline current publicGuard state resolved activation
            code.endpoint.publicationNode message hactivation hkey hlookup hrefines hhandle
        exact ⟨⟨(result, sourceNext), hresult, hlegal, hsource⟩, hresolved,
          runtime.handle_freshActivation state resolved _ hhandle, trivial⟩)
      (by
        intro witness before after suffix hindex hinactive hrefines hfresh hcertificate hafter
        have hinvariant := runtime.runPolicies_deliveryBlock_inactive_invariant roster recipients
          players suffix before after (.conditional code) hindex
          (fun state => state.base.Refines (target witness) ∧ state.FreshActivation ∧
            runtime.image.activeAddress? state.base.memory ≠ some code.endpoint.publicationNode)
          (fun _ actor command hstate => by
            cases command with
            | register slot value =>
                exact ⟨hstate.1.register actor slot value, hstate.2.1, hstate.2.2⟩)
          (fun _ hstate => hstate.2.2)
          ⟨hrefines, hfresh, hinactive⟩ hafter
        exact ⟨hinvariant.1, hinvariant.2.1, trivial⟩)
      hactive hactivation hrefines hinactive hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2.1, witness.2.2.1, witness.2.2.2,
    hnextRefines, hnextFresh⟩

end Vegas.WindowedApplication

/-! Axiom audit for the source-coupling edge. -/
/-- info: 'Vegas.WindowedApplication.runPolicies_delivery_conditional_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_delivery_conditional_source_coupling
