/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryProvenance

/-! # Operational services for the windowed runtime

A service packages the concrete player gate, environment policy, and invocation
schedule used for one block.  It carries only command provenance for its
reference gate; source correspondence remains a property proved by the
compiler-specific checkpoint and block laws.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The operational choices which turn a windowed application into a repeated
block service. -/
structure Service (runtime : WindowedApplication P L) where
  referencePlayer : P → runtime.image.orderedApplication.PlayerPolicy →
    runtime.application.PlayerPolicy
  reference_supported : ∀ who base history view command,
    command ∈ (referencePlayer who base history view).support →
      runtime.erasePlayerCommand command ∈
          (base (history.map runtime.erasePlayerEntry) (runtime.eraseView view)).support ∨
        runtime.image.IdleOrExpiryCommand (runtime.erasePlayerCommand command)
  environment : runtime.application.EnvironmentPolicy
  invocations : List (@Invocation P)

namespace Service

variable {runtime : WindowedApplication P L}

/-- Apply the service's reference gate coordinatewise to a source-policy
profile already lifted to the ordered application. -/
def referencePlayers (service : runtime.Service)
    (profile : P → runtime.image.orderedApplication.PlayerPolicy) :
    P → runtime.application.PlayerPolicy :=
  fun who => service.referencePlayer who (profile who)

/-- Replace one coordinate of the service reference profile by an unrestricted
native player policy. -/
def players (service : runtime.Service)
    (profile : P → runtime.image.orderedApplication.PlayerPolicy) (focal : P)
    (replacement : runtime.application.PlayerPolicy) :
    P → runtime.application.PlayerPolicy :=
  Function.update (service.referencePlayers profile) focal replacement

end Service

/-- The three-turn windowed block service without delivery. -/
def blockService (runtime : WindowedApplication P L) (roster : List P) : runtime.Service where
  referencePlayer who base := runtime.blockPlayer who (runtime.liftPlayerPolicy base)
  reference_supported := runtime.blockPlayer_supported
  environment := runtime.blockEnvironment roster
  invocations := blockInvocations roster

/-- The delivery-enabled four-turn windowed block service. -/
def deliveryService (runtime : WindowedApplication P L) (roster recipients : List P) :
    runtime.Service where
  referencePlayer who base := runtime.deliveryBlockPlayer who (runtime.liftPlayerPolicy base)
  reference_supported := runtime.deliveryBlockPlayer_supported
  environment := runtime.deliveryBlockEnvironment roster recipients
  invocations := deliveryBlockInvocations roster recipients

end Vegas.WindowedApplication
