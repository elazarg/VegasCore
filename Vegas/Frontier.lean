/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile
import Vegas.Frontier.RoundView
import Vegas.Frontier.SourceAdequacy
import Vegas.Frontier.FiniteMachine
import Vegas.Frontier.Kuhn
import Vegas.Frontier.Games
import Vegas.Frontier.SourceFrontier
import Vegas.Frontier.SourceStrategicAdequacy
import Vegas.Frontier.SolutionConcepts
import Vegas.Frontier.Transport

/-!
# Frontier: canonical strategic semantics over compiled graphs

This layer consumes `Vegas.Compile` output and packages compiled event graphs
into strategic games: the canonical frontier round semantics, the pure and
behavioral kernel games, source adequacy, the raw source/frontier proof spine,
finite-machine presentations, and the solution-concept and game-morphism
transports.

Dependency direction is one-way: `Frontier` imports `Compile`; `Compile` never
imports `Frontier`.
-/
