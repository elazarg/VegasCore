/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Pools keyed by what a move may depend on

Some agents are keyed: they choose among finitely many options, and the
choice may depend on a key of the agent only, so that a move reveals nothing
the key does not. Keyed agents with a common key share one pool whose parts
are the options; every other agent sits in a single pool with one part
(`GameTheory.Protocol.InformationModel.keyedPool`,
`GameTheory.Protocol.InformationModel.KeyedPart`). A keyed agent's component
of an option is its keyed law of that option, and every other agent's single
component is its prescribed law
(`GameTheory.Protocol.InformationModel.keyedComponent`).

Given a choice of option at each key, the best part of a keyed pool is the
option chosen at the pool's key
(`GameTheory.Protocol.InformationModel.keyedBest`); choosing an option of
greatest score gives `GameTheory.Math.Probability.scoreArgmax`. The component
of the best part of a keyed agent is its keyed law of that option
(`GameTheory.Protocol.InformationModel.keyedComponent_best_of_keyed`), and
fully supported prescribed and keyed laws make every component fully supported
(`GameTheory.Protocol.InformationModel.keyedComponent_fullSupport`).
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- An option of greatest score, chosen by a fixed rule from the score. -/
def scoreArgmax {Option : Type*} [Fintype Option] [Nonempty Option] (score : Option → ℝ) :
    Option :=
  (Finset.univ.exists_max_image score Finset.univ_nonempty).choose

theorem le_scoreArgmax {Option : Type*} [Fintype Option] [Nonempty Option]
    (score : Option → ℝ) (option : Option) : score option ≤ score (scoreArgmax score) :=
  (Finset.univ.exists_max_image score Finset.univ_nonempty).choose_spec.2 option
    (Finset.mem_univ option)

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} {T : ExecutionProtocol Player} {N : InformationModel T}
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)]

section Structure

variable {Key : Type*} (keyed : N.InformationAgent N.playedInformation → Prop)
  (key : N.InformationAgent N.playedInformation → Key) (Opt : Type)

/-- The keyed pools: one per key of a keyed agent, and `none` for every other
agent. -/
abbrev KeyedPool := Option (Set.range fun agent : {agent // keyed agent} => key agent.1)

open Classical in
/-- The pool of an agent: its key if it is keyed, `none` otherwise. -/
def keyedPool (agent : N.InformationAgent N.playedInformation) : KeyedPool keyed key :=
  if isKeyed : keyed agent then some ⟨key agent, ⟨agent, isKeyed⟩, rfl⟩ else none

/-- The parts of a keyed pool are the options; the other pool has one part. -/
def KeyedPart : KeyedPool keyed key → Type
  | none => Unit
  | some _ => Opt

instance [Finite Opt] (p : KeyedPool keyed key) : Finite (KeyedPart keyed key Opt p) := by
  cases p <;> unfold KeyedPart <;> infer_instance

instance [Nonempty Opt] (p : KeyedPool keyed key) : Nonempty (KeyedPart keyed key Opt p) := by
  cases p <;> unfold KeyedPart <;> infer_instance

variable {keyed key Opt}

/-- A component at a pool: the prescribed law in the unkeyed pool, the keyed
law of the option in a keyed pool. -/
def keyedComponentAt
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    (p : KeyedPool keyed key) → KeyedPart keyed key Opt p → PMF (N.Choice agent.1 agent.2.1)
  | none, _ => prescribed agent
  | some _, option => keyedLaw agent option

/-- **The keyed components.** A keyed agent's component of an option is its
keyed law of the option; every other agent's single component is its
prescribed law. -/
def keyedComponent
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    KeyedPart keyed key Opt (keyedPool keyed key agent) → PMF (N.Choice agent.1 agent.2.1) :=
  keyedComponentAt prescribed keyedLaw agent (keyedPool keyed key agent)

/-- The best part of each pool: the best option of a keyed pool's key. -/
def keyedBest (bestOf : Key → Opt) : (p : KeyedPool keyed key) → KeyedPart keyed key Opt p
  | none => ()
  | some k => bestOf k.1

theorem keyedPool_of_keyed {agent : N.InformationAgent N.playedInformation}
    (isKeyed : keyed agent) :
    keyedPool keyed key agent = some ⟨key agent, ⟨agent, isKeyed⟩, rfl⟩ := by
  classical
  unfold keyedPool
  simp only [isKeyed, ↓reduceDIte]

theorem keyedPool_of_not_keyed {agent : N.InformationAgent N.playedInformation}
    (unkeyed : ¬ keyed agent) : keyedPool keyed key agent = none := by
  classical
  unfold keyedPool
  simp only [unkeyed, ↓reduceDIte]

theorem isSome_keyedPool_iff (agent : N.InformationAgent N.playedInformation) :
    (keyedPool keyed key agent).isSome ↔ keyed agent := by
  by_cases isKeyed : keyed agent
  · simp [keyedPool_of_keyed isKeyed, isKeyed]
  · simp [keyedPool_of_not_keyed isKeyed, isKeyed]

/-- Every component of a keyed agent is its keyed law of some option. -/
theorem keyedComponent_of_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (isKeyed : keyed agent) :
    ∀ part, ∃ option, keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent part =
      keyedLaw agent option := by
  unfold keyedComponent
  rw [keyedPool_of_keyed isKeyed]
  exact fun option => ⟨option, rfl⟩

/-- The component of the best part of a keyed agent is its keyed law of the
best option of its key. -/
theorem keyedComponent_best_of_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1)) (bestOf : Key → Opt)
    {agent : N.InformationAgent N.playedInformation} (isKeyed : keyed agent) :
    keyedComponent prescribed keyedLaw agent (keyedBest bestOf (keyedPool keyed key agent)) =
      keyedLaw agent (bestOf (key agent)) := by
  change (fun p => keyedComponentAt prescribed keyedLaw agent p (keyedBest bestOf p))
    (keyedPool keyed key agent) = _
  rw [keyedPool_of_keyed isKeyed]
  rfl

/-- Every component of an unkeyed agent is its prescribed law. -/
theorem keyedComponent_of_not_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (unkeyed : ¬ keyed agent) :
    ∀ part, keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent part =
      prescribed agent := by
  unfold keyedComponent
  rw [keyedPool_of_not_keyed unkeyed]
  exact fun _ => rfl

/-- Fully supported prescribed and keyed laws make every keyed component
fully supported. -/
theorem keyedComponent_fullSupport
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (prescribedFull : ∀ agent, FullSupport (prescribed agent))
    (keyedFull : ∀ agent option, FullSupport (keyedLaw agent option))
    (agent : N.InformationAgent N.playedInformation) :
    ∀ part, FullSupport (keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent
      part) := by
  unfold keyedComponent
  cases keyedPool keyed key agent with
  | none => exact fun _ => prescribedFull agent
  | some _ => exact fun option => keyedFull agent option

end Structure

end GameTheory.Protocol.InformationModel
