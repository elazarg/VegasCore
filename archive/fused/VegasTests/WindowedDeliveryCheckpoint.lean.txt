/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedService
import Vegas.Compile.WindowedDeliveryReadiness
import VegasTests.WindowedSourceCoverage

/-! # Delivery-service initial checkpoint regression

The checked persistent-disclosure program uses the actual delivery-enabled
service with roster `[0, 1]` and recipient `[1]`. The canonical checkpoint and
source prefix remain available for every source profile and unrestricted raw
replacement at player zero. Generic checkpoint facts used below do not assume
that the service forbids delivery.
-/

noncomputable section

namespace VegasTests.WindowedDeliveryCheckpoint

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

def service : runtime.Service := runtime.deliveryService [0, 1] [1]

theorem initial_checkpoint
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    ApplicationPlan.WindowedCheckpoint applicationPlan profile (fun _ => 10)
      bindingSelector choiceSelector (fun _ => 10) service 0 replacement 0
      applicationPlan profile (compiledInitialCoupled source) initial :=
  ApplicationPlan.WindowedCheckpoint.initial DisclosureAccounting.persistentChecked
    applicationPlan profile (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
    service 0 replacement

theorem initial_source_prefix
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    ApplicationPlan.WindowedSourcePrefix applicationPlan profile (fun _ => 10)
      bindingSelector choiceSelector (fun _ => 10) service 0 replacement
      (compiledInitialCoupled source) 0 applicationPlan profile
      (compiledInitialCoupled source) initial :=
  .initial (initial_checkpoint profile replacement)

/-- Consistency is a generic checkpoint consequence for the delivery service,
not a no-delivery invariant. -/
theorem initial_consistent
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    runtime.Consistent initial.native.application :=
  (initial_checkpoint profile replacement).consistent

/-- The initial active instruction starts at the current public clock under
the delivery service. -/
theorem initial_active_origin_clock
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (instruction : ApplicationInstruction TestPlayer simpleExpr)
    (rest : List (ApplicationInstruction TestPlayer simpleExpr))
    (hhead : applicationPlan.instructions (fun _ => 10) = instruction :: rest) :
    ∃ activation,
      initial.native.application.active = some activation ∧
      activation.key = instruction.address ∧
      activation.since = initial.native.application.base.memory.clock :=
  (initial_checkpoint profile replacement).active_origin_clock instruction rest hhead

/-- An unchanged reference owner receives typed registration provenance from
the generic checkpoint API even though the selected service permits delivery. -/
theorem initial_registeredBindings_reference_owner
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    runtime.image.RegisteredBindings 1
      (fun slot typed => ∃ fieldSpec : FieldSpec TestPlayer simpleExpr,
        (compileCore source.prog source.fresh compilerInitial).graph.field? slot =
            some fieldSpec ∧
          typed.ty = fieldSpec.ty)
      ((initial.principalHistory 1).map fun entry =>
        show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
      initial.native.application.base := by
  let checkpoint := initial_checkpoint profile replacement
  have reference := checkpoint.referenceOwner_of_ne 1 (by decide)
  exact checkpoint.registeredBindings 1 reference.policy

/-- The actual delivery service retains the first opaque-binding source draw
jointly with every later native continuation. Player one is an unrestricted
raw replacement; the unchanged binding owner is player zero. The continuation
may contain delivery, reaction, inclusion, or arbitrary additional traffic. -/
theorem binding_first_poll_joint_source_law
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    let deliveryPlayers := service.players
      (applicationPlan.liftProfile (fun _ => 10) profile) 1 replacement
    let encoding := (ApplicationImage.registrationEncoding
      compilerInitial.nextField).privateCommand runtime.application
    let choices := profile 0 GeneratedBindingPolicy.site
      ((source.env.toView 0).eraseEnv)
    ∀ environment schedule,
      (runtime.application.runPolicies deliveryPlayers environment
        (.player 0 :: schedule) initial).map (fun next =>
          (encoding.cachedValue runtime.application (next.principalHistory 0), next)) =
        choices.bind fun chosen =>
          ((runtime.application.playerStep 0 initial
            (.privateCommand (.register compilerInitial.nextField
              ⟨.bool, chosen.1⟩))).bind
                (runtime.application.runPolicies deliveryPlayers environment schedule)).map
            (fun next => (some ⟨.bool, chosen.1⟩, next)) := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) service 1 replacement
  have reference := checkpoint.referenceOwner_of_ne 0 (by decide)
  exact (checkpoint.delivery_binding_first_poll_source_law
    GeneratedApplicationSourceLaw.initial_reads_public (by decide) (by simp)
    reference).2

end VegasTests.WindowedDeliveryCheckpoint

/-- info: 'VegasTests.WindowedDeliveryCheckpoint.initial_source_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliveryCheckpoint.initial_source_prefix

/-- info: 'VegasTests.WindowedDeliveryCheckpoint.initial_registeredBindings_reference_owner'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliveryCheckpoint.initial_registeredBindings_reference_owner

/-- info: 'VegasTests.WindowedDeliveryCheckpoint.binding_first_poll_joint_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliveryCheckpoint.binding_first_poll_joint_source_law
