/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedHeadSourceCoupling
import Vegas.Compile.WindowedPublicChoiceBlock
import Vegas.Compile.WindowedDeliveryProgress

/-! # Source coupling for resolved delivery public-choice segments -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A resolving delivery-service segment at a public-choice head carries the
typed choice or the certified expiry value to the source successor. The actual
delivery schedule and raw player policies remain unrestricted; only the
constructor's public-validation certificate is used for the handler law. -/
theorem runPolicies_delivery_publicChoice_source_coupling
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy) (schedule : List (@Invocation P))
    {Γ : VCtx P L} {name publicName : VarId} {owner : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool)
    (tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (fresh : FreshBindings
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh build).graph build)
    (publicGuard : (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
      fresh build)
    (deadline : Nat)
    (execution final : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (recipients.length + roster.length + 2)]? =
         some (.publicChoice ((PublicChoiceSite.atHead name publicName owner guard tail).timeoutCode
          fallback fresh build deadline)))
    (hlookup : runtime.image.lookup
      ((PublicChoiceSite.atHead name publicName owner guard tail).code fresh build
        |>.endpoint.publicationNode) = some (.publicChoice
      ((PublicChoiceSite.atHead name publicName owner guard tail).timeoutCode
        fallback fresh build deadline)))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some ((PublicChoiceSite.atHead name publicName owner guard tail).code
        fresh build).endpoint.publicationNode)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key =
      (PublicChoiceCode.endpoint ((PublicChoiceSite.atHead name publicName owner guard tail).code
        fresh build)).publicationNode)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some ((PublicChoiceSite.atHead name publicName owner guard tail).code
        fresh build).endpoint.publicationNode)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment (roster) recipients) schedule execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) fresh build).graph
        (((build.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      evalGuard guard chosen ((current.current.source.toView owner).eraseEnv) = true ∧
      sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation := by
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let timed := site.timeoutCode fallback fresh build deadline
  let Witness := { pair : L.Val ty × CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh build).graph
      (((build.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1 //
    evalGuard guard pair.1 ((current.current.source.toView owner).eraseEnv) = true ∧
      pair.2.current.source = (current.current.source.cons pair.1).cons pair.1 }
  let target : Witness → Config
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh build).graph :=
    fun witness => witness.1.2.current.graph.1
  obtain ⟨witness, hnextRefines, hnextFresh, _⟩ :=
    runtime.runPolicies_head_source_witness players
      (runtime.deliveryBlockEnvironment roster recipients) schedule
      (fun index => runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some (.publicChoice timed))
      timed.endpoint.publicationNode current.current.graph.1 execution final activation
      Witness target (fun _ _ => True) hindex
      (fun state command hindex hcommand =>
        runtime.deliveryBlockEnvironment_command_not_sample roster recipients state
          (.publicChoice timed) owner hindex rfl command hcommand)
      (by
        intro state message resolved hactivation hrefines hhandle
        obtain ⟨chosen, sourceNext, hlegal, hsource, hresolved⟩ :=
          runtime.handle_publicChoice_or_expiry_source_coupling guard tail fallback fresh
            build
            deadline current publicGuard state resolved activation
            timed.endpoint.publicationNode message
            hactivation hkey hlookup hrefines hhandle
        exact ⟨⟨(chosen, sourceNext), hlegal, hsource⟩, hresolved,
          runtime.handle_freshActivation state resolved _ hhandle, trivial⟩)
      (by
        intro witness before after suffix hindex hinactive hrefines hfresh hcertificate hafter
        have hinvariant := runtime.runPolicies_deliveryBlock_inactive_invariant roster recipients
          players suffix before after (.publicChoice timed) hindex
          (fun state => state.base.Refines (target witness) ∧ state.FreshActivation ∧
            runtime.image.activeAddress? state.base.memory ≠ some timed.endpoint.publicationNode)
          (fun _ actor command hstate => by
            cases command with
            | register slot value =>
                exact ⟨hstate.1.register actor slot value, hstate.2.1, hstate.2.2⟩)
          (fun _ hstate => hstate.2.2)
          ⟨hrefines, hfresh, hinactive⟩ hafter
        exact ⟨hinvariant.1, hinvariant.2.1, trivial⟩)
      hactive hactivation hrefines hinactive hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2.1, witness.2.2,
    hnextRefines, hnextFresh⟩

end Vegas.WindowedApplication

/-! Axiom audit for the source-coupling edge. -/
/-- info: 'Vegas.WindowedApplication.runPolicies_delivery_publicChoice_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_delivery_publicChoice_source_coupling
