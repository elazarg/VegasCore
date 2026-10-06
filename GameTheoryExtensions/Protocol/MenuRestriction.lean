/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.ActionRestriction

/-! # Restricting the menus of a protocol

`GameTheory.Protocol.ExecutionProtocol.restrictAvailable` keeps the states,
actions, activity, termination and transition law of a protocol and offers
fewer actions; it supplies its own progress certificate. Every history of the
restricted protocol is a history of the original one with the same state, so
an information model of the original protocol restricts to it with the same
signals and information values
(`GameTheory.Protocol.InformationModel.restrictMenu`), once a local menu
adequate for the smaller availability is supplied.
`GameTheory.Protocol.InformationModel.menuRestriction` is the resulting
structural action restriction: identity on information values, inclusion on
choices and the trace embedding on histories.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

variable {ι : Type*}

/-- Legality is monotone in the available sets. -/
theorem IsLegalJoint.mono {Action : ι → Type*} {active : ι → Prop}
    {smaller larger : (i : ι) → Set (Action i)} (included : ∀ i, smaller i ⊆ larger i)
    {joint : ∀ i, Option (Action i)} (legal : IsLegalJoint active smaller joint) :
    IsLegalJoint active larger joint := by
  intro i
  have permittedHere := legal i
  revert permittedHere
  cases joint i with
  | none => exact id
  | some action => exact fun permitted => ⟨permitted.1, included i permitted.2⟩

namespace ExecutionProtocol

variable (E : ExecutionProtocol ι)

/-- The same protocol with fewer available actions. Activity, termination and
the transition law are unchanged; the smaller availability carries its own
progress certificate. -/
def restrictAvailable (available : (state : E.State) → (i : ι) → Set (E.Action i))
    (included : ∀ state i, available state i ⊆ E.available state i)
    (progress : ∀ state, ¬ E.terminal state →
      ∃ joint, IsLegalJoint (E.active state) (available state) joint) :
    ExecutionProtocol ι where
  State := E.State
  Action := E.Action
  init := E.init
  active := E.active
  available := available
  terminal := E.terminal
  step state joint := E.step state ⟨joint.1, joint.2.1, joint.2.2.mono (included state)⟩
  progress := progress

namespace restrictAvailable

variable {E} {available : (state : E.State) → (i : ι) → Set (E.Action i)}
  {included : ∀ state i, available state i ⊆ E.available state i}
  {progress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (available state) joint}

theorem legal {state : E.State} {joint : ∀ i, Option (E.Action i)}
    (permitted : (E.restrictAvailable available included progress).Legal state joint) :
    E.Legal state joint :=
  ⟨permitted.1, permitted.2.mono (included state)⟩

/-- A realized transition of the restricted protocol is one of the original. -/
@[elab_without_expected_type]
def stepEvent (event : (E.restrictAvailable available included progress).StepEvent) :
    E.StepEvent :=
  ⟨event.source, event.joint, legal event.isLegal, event.target, event.realized⟩

/-- Every trace of the restricted protocol is a trace of the original one. -/
@[elab_without_expected_type]
def trace : ∀ {state}, (E.restrictAvailable available included progress).Trace state →
    E.Trace state
  | _, .start => .start
  | _, .extend prior joint permitted realized =>
      .extend (trace prior) joint (legal permitted) realized

/-- Every history of the restricted protocol is a history of the original one. -/
@[elab_without_expected_type]
def history (original : (E.restrictAvailable available included progress).History) :
    E.History :=
  ⟨original.state, trace original.trace⟩

@[simp] theorem history_state
    (original : (E.restrictAvailable available included progress).History) :
    (history original).state = original.state := rfl

@[simp] theorem trace_length {state}
    (original : (E.restrictAvailable available included progress).Trace state) :
    (trace original).length = original.length := by
  induction original with
  | start => rfl
  | extend prior joint permitted realized ih => exact congrArg Nat.succ ih

theorem trace_injective {state} :
    Function.Injective (trace (available := available) (included := included)
      (progress := progress) (state := state)) := by
  intro first second same
  induction first with
  | start => cases second <;> cases same; rfl
  | extend prior joint permitted realized ih =>
      cases second with
      | start => cases same
      | extend other otherJoint otherLegal otherRealized =>
          simp only [trace, Trace.extend.injEq] at same
          rcases same with ⟨rfl, priorEq, jointEq⟩
          have equal := ih (eq_of_heq priorEq)
          cases equal
          cases jointEq
          rfl

theorem history_injective :
    Function.Injective (history (available := available) (included := included)
      (progress := progress)) := by
  rintro ⟨first, firstTrace⟩ ⟨second, secondTrace⟩ same
  have stateEq := congrArg History.state same
  change first = second at stateEq
  subst second
  have traceEq := History.mk.inj same
  have equal := trace_injective (eq_of_heq traceEq.2)
  cases equal
  rfl

/-- A horizon bound of the original protocol bounds the restricted one. -/
theorem boundedHorizon {bound : ℕ} (bounded : E.BoundedHorizon bound) :
    (E.restrictAvailable available included progress).BoundedHorizon bound :=
  fun state original long => bounded state (trace original) (by rwa [trace_length])

end restrictAvailable

end ExecutionProtocol

namespace InformationModel

open ExecutionProtocol

variable {E : ExecutionProtocol ι} (M : InformationModel E)
  {available : (state : E.State) → (i : ι) → Set (E.Action i)}
  {included : ∀ state i, available state i ⊆ E.available state i}
  {progress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (available state) joint}

/-- One local step depends on the local choices only through the joint action
they spell. -/
theorem localStep_eq_of_joint (history : E.History)
    (choices : ∀ who, M.Choice who (M.infoOf who history.trace))
    (running : ¬ E.terminal history.state) (joint : ∀ i, Option (E.Action i))
    (legal : E.Legal history.state joint) (same : ∀ who, (choices who).1 = joint who) :
    M.localStep history choices =
      (E.step history.state ⟨joint, legal⟩).bindOnSupport
        (fun _ realized => PMF.pure (history.extend legal realized)) := by
  have spelled : (fun who => (choices who).1) = joint := funext same
  subst spelled
  simp only [localStep, dite_eq_right running]

private theorem choice_cast_val {who : ι} {first second : M.InfoState who}
    (same : first = second) (cast : M.Choice who first = M.Choice who second)
    (choice : M.Choice who first) : (Eq.mp cast choice).1 = choice.1 := by
  subst same
  rfl

/-- The original signals read through the trace embedding. -/
def restrictSignals : InfoSignals (E.restrictAvailable available included progress) where
  PublicSignal := M.PublicSignal
  PrivateSignal := M.PrivateSignal
  initialPublic := M.initialPublic
  initialPrivate := M.initialPrivate
  publicSignal event := M.publicSignal (restrictAvailable.stepEvent event)
  privateSignal who event := M.privateSignal who (restrictAvailable.stepEvent event)
  InfoState := M.InfoState
  initInfo := M.initInfo
  pushInfo := M.pushInfo

/-- A restricted history leaves every player exactly the information of its
embedded original history. -/
theorem restrictSignals_infoOf (who : ι) :
    ∀ {state} (trace : (E.restrictAvailable available included progress).Trace state),
      (M.restrictSignals (included := included) (progress := progress)).infoOf who trace =
        M.infoOf who (restrictAvailable.trace trace)
  | _, .start => rfl
  | _, .extend prior joint permitted realized => by
      rw [InfoSignals.infoOf_extend, restrictSignals_infoOf who prior]
      rfl

/-- The restricted model: the original signals and information values, with a
local menu adequate for the smaller availability. -/
def restrictMenu (menu : ∀ who, M.InfoState who → Set (Option (E.Action who)))
    (adequate : ∀ who {state}
      (trace : (E.restrictAvailable available included progress).Trace state)
      (choice : Option (E.Action who)),
      choice ∈ menu who (M.infoOf who (restrictAvailable.trace trace)) ↔
        LegalOption (E.restrictAvailable available included progress) state who choice) :
    InformationModel (E.restrictAvailable available included progress) where
  toInfoSignals := M.restrictSignals
  menu := menu
  menu_adequate who state trace choice := by
    rw [restrictSignals_infoOf]
    exact adequate who trace choice

variable (menu : ∀ who, M.InfoState who → Set (Option (E.Action who)))
  (adequate : ∀ who {state}
    (trace : (E.restrictAvailable available included progress).Trace state)
    (choice : Option (E.Action who)),
    choice ∈ menu who (M.infoOf who (restrictAvailable.trace trace)) ↔
      LegalOption (E.restrictAvailable available included progress) state who choice)

@[simp] theorem restrictMenu_infoOf (who : ι) {state}
    (trace : (E.restrictAvailable available included progress).Trace state) :
    (M.restrictMenu menu adequate).infoOf who trace =
      M.infoOf who (restrictAvailable.trace trace) :=
  M.restrictSignals_infoOf who trace

/-- Own play is recorded identically along a restricted history and its
embedding. -/
theorem restrictMenu_ownPlay (who : ι) :
    ∀ {state} (trace : (E.restrictAvailable available included progress).Trace state),
      (M.restrictMenu menu adequate).ownPlay who trace =
        M.ownPlay who (restrictAvailable.trace trace)
  | _, .start => rfl
  | _, .extend prior joint permitted realized => by
      change (M.restrictMenu menu adequate).ownPlay who (.extend prior joint permitted realized) =
        M.ownPlay who (.extend (restrictAvailable.trace prior) joint
          (restrictAvailable.legal permitted) realized)
      rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, restrictMenu_ownPlay who prior,
        restrictMenu_infoOf]
      cases joint who <;> rfl

/-- Restricting menus preserves perfect recall. -/
theorem restrictMenu_perfectRecall (recall : M.PerfectRecall) :
    (M.restrictMenu menu adequate).PerfectRecall := by
  intro who first second firstTrace secondTrace same
  rw [restrictMenu_infoOf, restrictMenu_infoOf] at same
  rw [restrictMenu_ownPlay, restrictMenu_ownPlay]
  exact recall who _ _ same

/-- Restricting menus preserves the decision antichain obtained from perfect
recall. -/
theorem restrictMenu_decisionInformationAntichain (recall : M.PerfectRecall) :
    (M.restrictMenu menu adequate).DecisionInformationAntichain :=
  (M.restrictMenu menu adequate).decisionInformationAntichain_of_perfectRecall
    (M.restrictMenu_perfectRecall menu adequate recall)

/-- **Menu restriction.** A model with fewer available actions and an adequate
smaller menu embeds into the original one: identity on information values,
inclusion on choices, and the trace embedding on histories. -/
def menuRestriction (menuIncluded : ∀ who info, menu who info ⊆ M.menu who info) :
    (M.restrictMenu menu adequate).ActionRestriction M where
  history := ⟨restrictAvailable.history, restrictAvailable.history_injective⟩
  information _ := Function.Embedding.refl _
  choice who info := ⟨fun choice => ⟨choice.1, menuIncluded who info choice.2⟩,
    fun first second same => Subtype.ext (congrArg Subtype.val same :)⟩
  initial := rfl
  length original := restrictAvailable.trace_length original.trace
  terminal _ := Iff.rfl
  active _ _ := Iff.rfl
  observed who original := (M.restrictSignals_infoOf who original.trace).symm
  step original choices := by
    by_cases stopped : E.terminal original.state
    · have smaller : (M.restrictMenu menu adequate).localStep original choices =
          PMF.pure original := by
        simp only [localStep]
        exact dite_eq_left_of_eq_true (eq_true stopped)
      have larger : ∀ targetChoices, M.localStep (restrictAvailable.history original)
          targetChoices = PMF.pure (restrictAvailable.history original) := by
        intro targetChoices
        simp only [localStep]
        exact dite_eq_left_of_eq_true (eq_true stopped)
      rw [smaller, PMF.pure_map]
      exact (larger _).symm
    · let joint := fun who => (choices who).1
      have permitted : (E.restrictAvailable available included progress).Legal
          original.state joint :=
        legal_of_legalOption stopped fun who =>
          ((M.restrictMenu menu adequate).menu_adequate who original.trace
            (choices who).1).mp (choices who).2
      rw [(M.restrictMenu menu adequate).localStep_eq_of_joint original choices stopped joint
        permitted (fun _ => rfl)]
      rw [M.localStep_eq_of_joint _ _ stopped joint (restrictAvailable.legal permitted) ?same]
      · rw [map_bindOnSupport]
        apply bindOnSupport_congr
        intro target realized
        rw [PMF.pure_map]
        rfl
      · intro who
        exact M.choice_cast_val (M.restrictSignals_infoOf who original.trace) _ _

@[simp] theorem menuRestriction_history
    (menuIncluded : ∀ who info, menu who info ⊆ M.menu who info)
    (original : (E.restrictAvailable available included progress).History) :
    (M.menuRestriction menu adequate menuIncluded).history original =
      restrictAvailable.history original := rfl

@[simp] theorem menuRestriction_choice_val
    (menuIncluded : ∀ who info, menu who info ⊆ M.menu who info)
    (who : ι) (info : M.InfoState who)
    (choice : (M.restrictMenu menu adequate).Choice who info) :
    ((M.menuRestriction menu adequate menuIncluded).choice who info choice).1 = choice.1 := rfl

/-- An additional local choice at a retained information value is exactly an
option of the original menu missing from the restricted one. -/
theorem menuRestriction_extra_choice
    (menuIncluded : ∀ who info, menu who info ⊆ M.menu who info)
    (who : ι) (info : M.InfoState who)
    (action : M.Choice who ((M.menuRestriction menu adequate menuIncluded).information who info))
    (extra : action ∉ Set.range ((M.menuRestriction menu adequate menuIncluded).choice who info)) :
    action.1 ∉ menu who info := by
  intro permitted
  exact extra ⟨⟨action.1, permitted⟩, rfl⟩

end InformationModel

end GameTheory.Protocol
