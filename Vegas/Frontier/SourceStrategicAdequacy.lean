/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Strategic
import Vegas.Frontier.SourceFrontier.Replay
import Vegas.Frontier.SourceFrontier.Checkpoint
import Vegas.Frontier.SourceFrontier.Query
import Vegas.Frontier.SourceFrontier.SourceCompletion
import Vegas.Frontier.SourceFrontier.Action
import Vegas.Frontier.SourceFrontier.Projected
import Vegas.Frontier.SourceFrontier.Strategy

/-!
# Source strategic adequacy

This umbrella exposes the proven source/frontier faithfulness layer: source-local
strategic games, replay facts, and checkpoint-aligned behavioral adequacy (the
checkpoint↔frontier bridge).

The unconditional source↔frontier strategic equivalence is deliberately absent:
the schedule a compiled event graph admits is a public correlation device, so
the source strategic game and the free-schedule event-graph game are not
strategically equivalent for correlated equilibrium.  The abandoned bridge
scaffolding (the `RawSourceFrontierNashDeviationBridge` API and the
`CheckpointBridge` reconstruction attempt, whose keystone was false for
multi-commit rounds) was removed; only the proven per-node faithfulness and the
checkpoint↔frontier kernel correspondence remain.
-/
