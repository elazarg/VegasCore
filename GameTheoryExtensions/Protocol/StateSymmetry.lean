/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Protocol.History

/-! # Guarded state symmetries of a protocol

A *guarded state symmetry* (`GameTheory.Protocol.ExecutionProtocol.StateSymmetry`)
maps states to states and joint actions to joint actions, so that every
realized transition into a guarded state is sent to a realized transition of
the same protocol. The guard is closed under predecessors along realized
transitions, so a history ending at a guarded state maps step by step to a
history ending at the image of its state
(`GameTheory.Protocol.ExecutionProtocol.StateSymmetry.mapTrace`).

When the symmetry is an involution on guarded states and on the joint actions
of their transitions, mapping a history twice returns it
(`GameTheory.Protocol.ExecutionProtocol.StateSymmetry.mapHistory_mapHistory`),
so the symmetry is a bijection between any two classes of guarded histories it
exchanges (`GameTheory.Protocol.ExecutionProtocol.StateSymmetry.exchange`).
-/

namespace GameTheory.Protocol

variable {ι : Type*}

namespace ExecutionProtocol

variable (E : ExecutionProtocol ι)

/-- **A guarded state symmetry.** A map of states and of joint actions sending
every realized transition into a guarded state to a realized transition. The
guard holds before every realized transition into a guarded state. -/
structure StateSymmetry where
  /-- The map of states. -/
  map : E.State → E.State
  /-- The map of joint actions at a source state. -/
  act : E.State → (∀ i, Option (E.Action i)) → ∀ i, Option (E.Action i)
  /-- The states the symmetry applies to. -/
  Guard : E.State → Prop
  map_init : map E.init = E.init
  guard_source : ∀ {source target : E.State} {joint : ∀ i, Option (E.Action i)}
    (_prior : E.Trace source) (isLegal : E.Legal source joint),
      target ∈ (E.step source ⟨joint, isLegal⟩).support → Guard target → Guard source
  legal : ∀ {source target : E.State} {joint : ∀ i, Option (E.Action i)}
    (_prior : E.Trace source) (isLegal : E.Legal source joint),
      target ∈ (E.step source ⟨joint, isLegal⟩).support → Guard target →
        E.Legal (map source) (act source joint)
  realized : ∀ {source target : E.State} {joint : ∀ i, Option (E.Action i)}
    (prior : E.Trace source) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) (guarded : Guard target),
      map target ∈
        (E.step (map source) ⟨act source joint, legal prior isLegal realized guarded⟩).support

namespace StateSymmetry

variable {E} (S : E.StateSymmetry)

/-- **The image of a history** ending at a guarded state. -/
def mapTrace : ∀ {state : E.State}, E.Trace state → S.Guard state → E.Trace (S.map state)
  | _, .start, _ => S.map_init.symm ▸ .start
  | _, .extend (source := source) prior joint isLegal realized, guarded =>
      .extend (mapTrace prior (S.guard_source prior isLegal realized guarded))
        (S.act source joint) (S.legal prior isLegal realized guarded)
        (S.realized prior isLegal realized guarded)

@[simp] theorem mapTrace_extend {source target : E.State} (prior : E.Trace source)
    (joint : ∀ i, Option (E.Action i)) (isLegal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, isLegal⟩).support) (guarded : S.Guard target) :
    S.mapTrace (.extend prior joint isLegal realized) guarded =
      .extend (S.mapTrace prior (S.guard_source prior isLegal realized guarded))
        (S.act source joint) (S.legal prior isLegal realized guarded)
        (S.realized prior isLegal realized guarded) := rfl

/-- The image of a history ending at a guarded state. -/
def mapHistory (history : E.History) (guarded : S.Guard history.state) : E.History :=
  ⟨S.map history.state, S.mapTrace history.trace guarded⟩

@[simp] theorem mapHistory_state (history : E.History) (guarded : S.Guard history.state) :
    (S.mapHistory history guarded).state = S.map history.state := rfl

/-- **An involutive symmetry.** On guarded states the map of states is an
involution that keeps the guard, and at every realized transition into a guarded
state the map of joint actions at the image of the source undoes the map at the
source. -/
structure Involutive : Prop where
  map_map : ∀ state, S.Guard state → S.map (S.map state) = state
  guard_map : ∀ state, S.Guard state → S.Guard (S.map state)
  act_act : ∀ {source target : E.State} {joint : ∀ i, Option (E.Action i)}
    (_prior : E.Trace source) (isLegal : E.Legal source joint),
      target ∈ (E.step source ⟨joint, isLegal⟩).support →
        S.Guard target → S.act (S.map source) (S.act source joint) = joint

/-- Extending equal histories by equal joints to equal states gives equal
histories. -/
theorem history_extend_congr {source source' target target' : E.State}
    {prior : E.Trace source} {prior' : E.Trace source'}
    {joint joint' : ∀ i, Option (E.Action i)} {isLegal : E.Legal source joint}
    {isLegal' : E.Legal source' joint'}
    {realized : target ∈ (E.step source ⟨joint, isLegal⟩).support}
    {realized' : target' ∈ (E.step source' ⟨joint', isLegal'⟩).support}
    (same : (⟨source, prior⟩ : E.History) = ⟨source', prior'⟩) (sameJoint : joint = joint')
    (sameTarget : target = target') :
    (⟨target, .extend prior joint isLegal realized⟩ : E.History) =
      ⟨target', .extend prior' joint' isLegal' realized'⟩ := by
  cases same
  subst sameJoint
  subst sameTarget
  rfl

/-- Transporting a history along an equality of states keeps the history. -/
theorem history_cast {source target : E.State} (same : source = target) (trace : E.Trace source) :
    (⟨target, same ▸ trace⟩ : E.History) = ⟨source, trace⟩ := by
  subst same
  rfl

/-- The image of a transported history is the image of the history. -/
theorem mapTrace_cast {source target : E.State} (same : source = target) (trace : E.Trace source)
    (guarded : S.Guard target) :
    (⟨S.map target, S.mapTrace (same ▸ trace) guarded⟩ : E.History) =
      ⟨S.map source, S.mapTrace trace (same ▸ guarded)⟩ := by
  subst same
  rfl

variable {S}

/-- **An involutive symmetry returns every guarded history.** -/
theorem mapTrace_mapTrace (involutive : S.Involutive) : ∀ {state : E.State}
    (trace : E.Trace state) (guarded : S.Guard state),
    (⟨S.map (S.map state), S.mapTrace (S.mapTrace trace guarded)
        (involutive.guard_map state guarded)⟩ : E.History) = ⟨state, trace⟩
  | _, .start, guarded => by
      change (⟨S.map (S.map E.init), S.mapTrace (S.map_init.symm ▸ Trace.start)
        (involutive.guard_map E.init guarded)⟩ : E.History) = _
      rw [mapTrace_cast]
      change (⟨S.map E.init, S.map_init.symm ▸ Trace.start⟩ : E.History) = _
      exact history_cast _ _
  | _, .extend (source := source) (target := target) prior joint isLegal realized, guarded => by
      rw [mapTrace_extend, mapTrace_extend]
      exact history_extend_congr
        (mapTrace_mapTrace involutive prior (S.guard_source prior isLegal realized guarded))
        (involutive.act_act prior isLegal realized guarded)
        (involutive.map_map target guarded)

theorem mapHistory_mapHistory (involutive : S.Involutive) (history : E.History)
    (guarded : S.Guard history.state) :
    S.mapHistory (S.mapHistory history guarded) (involutive.guard_map _ guarded) = history :=
  mapTrace_mapTrace involutive history.trace guarded

/-- **An involutive symmetry exchanges two classes of guarded histories** when it
sends each class into the other. -/
def exchange (involutive : S.Involutive) (first second : E.History → Prop)
    (firstGuarded : ∀ history, first history → S.Guard history.state)
    (secondGuarded : ∀ history, second history → S.Guard history.state)
    (toSecond : ∀ history (member : first history),
      second (S.mapHistory history (firstGuarded history member)))
    (toFirst : ∀ history (member : second history),
      first (S.mapHistory history (secondGuarded history member))) :
    {history // first history} ≃ {history // second history} where
  toFun history := ⟨S.mapHistory history.1 (firstGuarded _ history.2),
    toSecond history.1 history.2⟩
  invFun history := ⟨S.mapHistory history.1 (secondGuarded _ history.2),
    toFirst history.1 history.2⟩
  left_inv history := Subtype.ext (mapHistory_mapHistory involutive history.1 _)
  right_inv history := Subtype.ext (mapHistory_mapHistory involutive history.1 _)

@[simp] theorem exchange_apply (involutive : S.Involutive) (first second : E.History → Prop)
    (firstGuarded : ∀ history, first history → S.Guard history.state)
    (secondGuarded : ∀ history, second history → S.Guard history.state)
    (toSecond : ∀ history (member : first history),
      second (S.mapHistory history (firstGuarded history member)))
    (toFirst : ∀ history (member : second history),
      first (S.mapHistory history (secondGuarded history member)))
    (history : {history // first history}) :
    (exchange involutive first second firstGuarded secondGuarded toSecond toFirst history).1 =
      S.mapHistory history.1 (firstGuarded _ history.2) := rfl

end StateSymmetry

end ExecutionProtocol

end GameTheory.Protocol
