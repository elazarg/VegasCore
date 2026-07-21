/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.Transport

/-!
# Frontier game transport facts

The canonical pure-to-behavioral embedding and program-to-program frontier
transports preserve expected utility and the corresponding Nash facts.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L L₁ L₂ : IExpr}

/-- The canonical pure-to-behavioral frontier embedding preserves expected
utility for every profile and player. -/
theorem pureToBehavioralFrontierMorphism_eu
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) (player : P) :
    program.behavioralFrontierGame.eu
        (fun who =>
          program.pureFrontierStrategyToBehavioral who (profile who))
        player =
      program.pureFrontierGame.eu profile player :=
  program.pureToBehavioralFrontierMorphism.eu_preserved profile player

/-- Pure frontier morphisms preserve expected utility under their profile
map. -/
theorem pureFrontierMorphism_preserves_eu
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : PureFrontierMorphism source target)
    (profile : source.PureFrontierProfile) (player : P) :
    target.pureFrontierEU (F.mapProfile profile) player =
      source.pureFrontierEU profile player :=
  F.mapProfile_eu_eq profile player

/-- Nash profiles pull back through pure frontier morphisms. -/
theorem pureFrontierMorphism_pulls_back_nash
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : PureFrontierMorphism source target)
    {profile : source.PureFrontierProfile}
    (hNash : target.PureFrontierNash (F.mapProfile profile)) :
    source.PureFrontierNash profile :=
  F.source_nash_of_target_mapped_nash hNash

/-- Behavioral frontier morphisms preserve expected utility under their
profile map. -/
theorem behavioralFrontierMorphism_preserves_eu
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : BehavioralFrontierMorphism source target)
    (profile : source.BehavioralFrontierProfile) (player : P) :
    target.behavioralFrontierEU (F.mapProfile profile) player =
      source.behavioralFrontierEU profile player :=
  F.mapProfile_eu_eq profile player

/-- Nash profiles pull back through behavioral frontier morphisms. -/
theorem behavioralFrontierMorphism_pulls_back_nash
    {source : WFProgram P L₁} [FiniteDomains source]
    {target : WFProgram P L₂} [FiniteDomains target]
    (F : BehavioralFrontierMorphism source target)
    {profile : source.BehavioralFrontierProfile}
    (hNash : target.BehavioralFrontierNash (F.mapProfile profile)) :
    source.BehavioralFrontierNash profile :=
  F.source_nash_of_target_mapped_nash hNash

/-- Pure frontier isomorphisms preserve and reflect Nash equilibrium. -/
theorem pureFrontierIsomorphism_preserves_nash
    {left : WFProgram P L₁} [FiniteDomains left]
    {right : WFProgram P L₂} [FiniteDomains right]
    (F : PureFrontierIsomorphism left right)
    (profile : left.PureFrontierProfile) :
    left.PureFrontierNash profile ↔
      right.PureFrontierNash (F.mapProfile profile) :=
  F.nash_iff profile

/-- Behavioral frontier isomorphisms preserve and reflect Nash equilibrium. -/
theorem behavioralFrontierIsomorphism_preserves_nash
    {left : WFProgram P L₁} [FiniteDomains left]
    {right : WFProgram P L₂} [FiniteDomains right]
    (F : BehavioralFrontierIsomorphism left right)
    (profile : left.BehavioralFrontierProfile) :
    left.BehavioralFrontierNash profile ↔
      right.BehavioralFrontierNash (F.mapProfile profile) :=
  F.nash_iff profile

end WFProgram

end Vegas
