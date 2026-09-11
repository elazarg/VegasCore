/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedHeadSourceCoupling
import Vegas.Compile.WindowedBindingBlock
import Vegas.Compile.WindowedDeliveryProgress

/-! # Source coupling for resolved delivery binding segments -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A resolving delivery-service segment at a binding head has a legal source
successor determined by its actual disposition. Normal inclusion and expiry
use the same native handler theorem; no canonical focal policy is required.
This is the safety component of the complete block theorem, with settlement
kept explicit rather than inferred from a bounded amount of execution. -/
theorem runPolicies_delivery_binding_source_coupling
    (runtime : WindowedApplication P L) (roster recipients : List P)
    (players : P → runtime.application.PlayerPolicy) (schedule : List (@Invocation P))
    {Γ : VCtx P L} {name : VarId} {owner : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed owner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name owner guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution final : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (recipients.length + roster.length + 2)]? =
        some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hlookup : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients) schedule execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh build).graph
        (build.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation ∧
      chosen = (fallback.bindingTimeoutCode fresh build deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv)
        final.native.application.base := by
  let timed := fallback.bindingTimeoutCode fresh build deadline
  let Witness := { pair : L.Val ty ×
      CoupledAt (compileCore (.commit name owner guard tail) fresh build).graph
        (build.addCommitEvent name owner guard fresh.1).1 //
    pair.2.current.source = current.current.source.cons pair.1 }
  let target : Witness → Config (compileCore (.commit name owner guard tail) fresh build).graph :=
    fun witness => witness.1.2.current.graph.1
  let Certificate : WindowedApplication.State P L → Witness → Prop := fun result witness =>
    witness.1.1 = timed.resolvedValue
      (L.eval fallback.expr current.current.source.erasePubEnv) result.base
  obtain ⟨witness, hnextRefines, hnextFresh, hcertificate⟩ :=
    runtime.runPolicies_head_source_witness players
      (runtime.deliveryBlockEnvironment roster recipients) schedule
      (fun index => runtime.image.instructions[index /
        (recipients.length + roster.length + 2)]? = some (.bind timed))
      timed.node current.current.graph.1 execution final activation Witness target Certificate
      hindex
      (fun state command hindex hcommand => runtime.deliveryBlockEnvironment_command_not_sample
        roster recipients state (.bind timed) owner hindex rfl command hcommand)
      (by
        intro state message resolved hactivation hrefines hhandle
        obtain ⟨chosen, sourceNext, hsource, hresolved, hfresh, hchosen⟩ :=
          runtime.handle_binding_or_expiry_source_coupling guard tail fallback fresh build current
            unrestricted state resolved activation timed.node deadline message hactivation hkey
            hlookup hrefines hhandle
        exact ⟨⟨(chosen, sourceNext), hsource⟩, hresolved, hfresh, hchosen⟩)
      (by
        intro witness before after suffix hindex hinactive hrefines hfresh hcertificate
          hafter
        have hinvariant := runtime.runPolicies_deliveryBlock_inactive_invariant roster recipients
          players suffix before after (.bind timed) hindex
          (fun state => state.base.Refines (target witness) ∧ state.FreshActivation ∧
            Certificate state witness ∧
              runtime.image.activeAddress? state.base.memory ≠ some timed.node)
          (by
            intro state actor command hstate
            cases command with
            | register slot value =>
                exact ⟨hstate.1.register actor slot value, hstate.2.1, hstate.2.2.1,
                  hstate.2.2.2⟩)
          (fun _ hstate => hstate.2.2.2)
          ⟨hrefines, hfresh, hcertificate, hinactive⟩ hafter
        exact ⟨hinvariant.1, hinvariant.2.1, hinvariant.2.2.1⟩)
      hactive hactivation hrefines hinactive hfinal
  exact ⟨witness.1.1, witness.1.2, witness.2, hnextRefines, hnextFresh, hcertificate⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_delivery_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_delivery_binding_source_coupling
