/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventCompilation
import Vegas.EventGraph.ExecutionMode
import Vegas.Pending.ReactivePolicy

/-! # Source policies for the reactive message protocol

Private initial inputs are sampled once by the protocol. The strategy compiler
composes source lowering, graph observation normalization, and the one-response
policy. These definitions specify the compilation edge; packet protection,
compiler outcome/deviation laws, and strategic correctness remain open.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def reactiveInitial (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode) :
    FinDist (EventGraphRuntime.State (setup.eventGraph.withMode mode)) :=
  setup.initialLaw.map fun initial =>
    EventGraphRuntime.State.initial (setup.eventInputs initial)

def compileReactiveStrategy (setup : Setup (Player := Player) (L := L))
    (mode : Vegas.EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (setup.eventGraph.withMode mode))
    (leaks : Interaction.MessageNetwork.ObservationRule Player
      (EventGraphRuntime.Payload (setup.eventGraph.withMode mode)))
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    (runtime.reactiveApplication leaks).Policy :=
  runtime.compileReactivePolicy leaks who
    (setup.eventGraph.toModePolicy mode who
      (EventLowering.compileEventPolicy setup.program who policy))

end Vegas.SourceProgram.Setup
