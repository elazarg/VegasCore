/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureBehavioral

/-! # Restoring private intentions at actual source successors

These finite conditional laws restore only an owner's action history. They
leave all typed cells, obligations, publication positions, and other players'
histories unchanged. The successor equations retain those histories; terminal
outcome equality alone would not supply the conditional information needed for
sequential incentives.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {who : Player} {Γ : SourceCtx Player L}

/-- Replace the remembered intention list without changing any game data. -/
def Config.withOwnHistory (config : Config Player L Γ) (who : Player)
    (past : List (OwnAction Player L)) : Config Player L Γ :=
  { config with history := Function.update config.history who past }

/-- An observation-local conditional law of original private histories. -/
def Config.restoreMemory (config : Config Player L Γ) (who : Player)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) :
    FinDist (Config Player L Γ) :=
  (remember (config.view who)).map (config.withOwnHistory who)

@[simp] theorem Config.withOwnHistory_view (config : Config Player L Γ)
    (who : Player) (past : List (OwnAction Player L)) :
    (config.withOwnHistory who past).view who = (sourceObserve who config.state, past) := by
  simp only [withOwnHistory, view, Function.update_self]

theorem Config.withOwnHistory_foreign_view (config : Config Player L Γ)
    (other : Player) (different : other ≠ who) (past : List (OwnAction Player L)) :
    (config.withOwnHistory who past).view other = config.view other := by
  simp only [withOwnHistory, view, Function.update_of_ne different]

@[simp] theorem Config.withOwnHistory_twice (config : Config Player L Γ)
    (who : Player) (first second : List (OwnAction Player L)) :
    (config.withOwnHistory who first).withOwnHistory who second =
      config.withOwnHistory who second := by
  simp only [withOwnHistory, Function.update_idem]

theorem sampleSuccessor_withOwnHistory {payload : L.Ty} (name : VarId)
    (config : Config Player L Γ) (value : L.Val payload) (past : List (OwnAction Player L)) :
    sampleSuccessor name (config.withOwnHistory who past) value =
      (sampleSuccessor name config value).withOwnHistory who past := rfl

theorem commitSuccessor_withOwnHistory {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ who name payload) (config : Config Player L Γ)
    (binding : PublicationResult (L.Val payload)) (past : List (OwnAction Player L)) :
    commitSuccessor name guard (config.withOwnHistory who past) binding =
      (commitSuccessor name guard config binding).withOwnHistory who
        (past ++ [.commit who name payload binding]) := by
  simp only [commitSuccessor, Config.withOwnHistory, Function.update_self,
    Function.update_idem]

theorem revealSuccessor_withOwnHistory {payload : L.Ty} {name : VarId}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (config : Config Player L Γ) (disclose : Bool) (past : List (OwnAction Player L)) :
    revealSuccessor published selected (config.withOwnHistory who past) disclose =
      (revealSuccessor published selected config disclose).withOwnHistory who
        (past ++ [.reveal who name disclose]) := by
  simp only [revealSuccessor, Config.withOwnHistory, Function.update_self,
    Function.update_idem]

/-- The published result is unchanged while the posterior remembers the
owner's actual original disclosure choice. -/
theorem revealSuccessor_effective_withOwnHistory {payload : L.Ty} {name : VarId}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (config : Config Player L Γ) (disclose : Bool) (past : List (OwnAction Player L)) :
    (revealSuccessor published selected config
        (effectiveDisclosure published selected config disclose)).withOwnHistory who past =
      (revealSuccessor published selected config disclose).withOwnHistory who past := by
  have states := revealSuccessor_effective_state published selected config disclose
  simp only [Config.withOwnHistory, revealSuccessor, Function.update_idem]
  congr 1

/-- Exact joint configuration disintegration for a binding. In particular,
conditioning does not discard the initial private state or another player's
own history. -/
theorem commitSuccessor_memory_disintegration {payload : L.Ty} (name : VarId)
    (guard : SourceGuard L Γ who name payload) (config : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist (PublicationResult (L.Val payload))) :
    ((config.restoreMemory who remember).bind fun original =>
      (choose (original.view who)).map (commitSuccessor name guard original)) =
      ((bindingMemoryLaw name payload remember choose (config.view who)).map Prod.fst).bind
        fun binding =>
          (((bindingMemoryLaw name payload remember choose (config.view who)).condOnFibre
            Prod.fst binding).map Prod.snd).map
              ((commitSuccessor name guard config binding).withOwnHistory who) := by
  simpa only [Config.restoreMemory, Config.view, FinDist.map_eq_bind, FinDist.bind_bind,
    FinDist.pure_bind, Config.withOwnHistory, Function.update_self, commitSuccessor,
    Function.update_idem] using
    bindingMemoryLaw_disintegrate name payload remember choose (config.view who)
    (fun binding past => FinDist.pure
      ((commitSuccessor name guard config binding).withOwnHistory who past))

/-- Exact joint configuration disintegration for a guarded reveal. Distinct
ineffective intentions are averaged only after retaining the conditional
original action history. -/
theorem revealSuccessor_memory_disintegration {payload : L.Ty} {name : VarId}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (config : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist Bool) :
    ((config.restoreMemory who remember).bind fun original =>
      (choose (original.view who)).map (revealSuccessor published selected original)) =
      ((disclosureMemoryLaw published selected config.registry config.revelations remember
        choose (config.view who)).map Prod.fst).bind fun disclose =>
          (((disclosureMemoryLaw published selected config.registry config.revelations remember
            choose (config.view who)).condOnFibre Prod.fst disclose).map Prod.snd).map
              ((revealSuccessor published selected config disclose).withOwnHistory who) := by
  have law := disclosureMemoryLaw_disintegrate published selected config.registry
    config.revelations remember choose (config.view who)
    (fun disclose past => FinDist.pure
      ((revealSuccessor published selected config disclose).withOwnHistory who past))
  simp only [Config.view, effectiveDisclosureView_observe,
    revealSuccessor_effective_withOwnHistory] at law
  simpa only [Config.restoreMemory, FinDist.bind_map, Config.withOwnHistory_view,
    Config.view, FinDist.map_eq_bind, FinDist.pure_bind, FinDist.bind_bind,
    Config.withOwnHistory, Function.update_self, revealSuccessor,
    Function.update_idem] using law

end Vegas.SourceProgram
