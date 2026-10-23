/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Protocol.MenuRestriction

/-! # Menus restricted at flagged information values

`GameTheory.Protocol.InformationModel.flagMenu` keeps the signals of an
information model on a protocol with restricted availability, and pairs every
information value with a flag computed from it. Its menu is a given restricted
menu where the flag is set and the original menu elsewhere. Perfect recall is
preserved (`GameTheory.Protocol.InformationModel.flagMenu_perfectRecall`).

A second restriction of the same protocol, whose availability stays inside the
flagged one along its own traces and whose traces never set the flag, embeds
into the flagged model (`GameTheory.Protocol.InformationModel.flagRestriction`).
An information value `info` goes to `(info, false)`, where the flagged menu is
the original one. So every menu of the smaller model embeds, including at
information values that the flagged model reaches only with the flag set.
-/

noncomputable section

namespace GameTheory.Protocol

variable {ι : Type*}

namespace ExecutionProtocol.restrictAvailable

variable {E : ExecutionProtocol ι}
  {small large : (state : E.State) → (i : ι) → Set (E.Action i)}
  {smallIncluded : ∀ state i, small state i ⊆ E.available state i}
  {largeIncluded : ∀ state i, large state i ⊆ E.available state i}
  {smallProgress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (small state) joint}
  {largeProgress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (large state) joint}
  (contained : ∀ {state} (_ : (E.restrictAvailable small smallIncluded smallProgress).Trace state)
    i, small state i ⊆ large state i)

/-- A trace of one restriction whose availability stays inside a second
restriction of the same protocol is a trace of the second. -/
def liftTrace : ∀ {state}, (E.restrictAvailable small smallIncluded smallProgress).Trace state →
    (E.restrictAvailable large largeIncluded largeProgress).Trace state
  | _, .start => .start
  | _, .extend prior joint permitted realized =>
      .extend (liftTrace prior) joint ⟨permitted.1, permitted.2.mono (contained prior)⟩ realized

/-- Lifting a trace does not change its embedding into the original protocol. -/
theorem trace_liftTrace : ∀ {state}
    (original : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
    trace (liftTrace (largeIncluded := largeIncluded) (largeProgress := largeProgress) contained
      original) = trace original
  | _, .start => rfl
  | _, .extend prior joint permitted realized => by
      simp only [liftTrace, trace, trace_liftTrace prior]

theorem liftTrace_length {state}
    (original : (E.restrictAvailable small smallIncluded smallProgress).Trace state) :
    (liftTrace (largeIncluded := largeIncluded) (largeProgress := largeProgress) contained
      original).length = original.length := by
  induction original with
  | start => rfl
  | extend prior joint permitted realized ih => exact congrArg Nat.succ ih

/-- A history of one restriction, as a history of a second restriction that
contains its availability along its traces. -/
def liftHistory (original : (E.restrictAvailable small smallIncluded smallProgress).History) :
    (E.restrictAvailable large largeIncluded largeProgress).History :=
  ⟨original.state, liftTrace contained original.trace⟩

@[simp] theorem liftHistory_state
    (original : (E.restrictAvailable small smallIncluded smallProgress).History) :
    (liftHistory (largeIncluded := largeIncluded) (largeProgress := largeProgress) contained
      original).state = original.state := rfl

theorem history_liftHistory
    (original : (E.restrictAvailable small smallIncluded smallProgress).History) :
    history (liftHistory (largeIncluded := largeIncluded) (largeProgress := largeProgress)
      contained original) = history original := by
  change (⟨original.state, trace (liftTrace contained original.trace)⟩ : E.History) =
    ⟨original.state, trace original.trace⟩
  rw [trace_liftTrace]

theorem liftHistory_injective :
    Function.Injective (liftHistory (largeIncluded := largeIncluded)
      (largeProgress := largeProgress) contained) := by
  intro first second same
  apply history_injective
  rw [← history_liftHistory contained first, ← history_liftHistory contained second, same]

end ExecutionProtocol.restrictAvailable

namespace InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {E : ExecutionProtocol ι} (N : InformationModel E)
  {available : (state : E.State) → (i : ι) → Set (E.Action i)}
  {included : ∀ state i, available state i ⊆ E.available state i}
  {progress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (available state) joint}

/-- The original signals read through the trace embedding, with each
information value paired with a flag computed from it. -/
def flagSignals (flag : ∀ who, N.InfoState who → Bool) :
    InfoSignals (E.restrictAvailable available included progress) where
  PublicSignal := N.PublicSignal
  PrivateSignal := N.PrivateSignal
  initialPublic := N.initialPublic
  initialPrivate := N.initialPrivate
  publicSignal event := N.publicSignal (restrictAvailable.stepEvent event)
  privateSignal who event := N.privateSignal who (restrictAvailable.stepEvent event)
  InfoState who := N.InfoState who × Bool
  initInfo who privateSignal publicSignal :=
    (N.initInfo who privateSignal publicSignal,
      flag who (N.initInfo who privateSignal publicSignal))
  pushInfo who info action privateSignal publicSignal :=
    (N.pushInfo who info.1 action privateSignal publicSignal,
      flag who (N.pushInfo who info.1 action privateSignal publicSignal))

/-- A restricted history leaves every player the information of its embedded
original history, flagged. -/
theorem flagSignals_infoOf (flag : ∀ who, N.InfoState who → Bool) (who : ι) :
    ∀ {state} (trace : (E.restrictAvailable available included progress).Trace state),
      (N.flagSignals flag).infoOf who trace =
        (N.infoOf who (restrictAvailable.trace trace),
          flag who (N.infoOf who (restrictAvailable.trace trace)))
  | _, .start => rfl
  | _, .extend prior joint permitted realized => by
      rw [InfoSignals.infoOf_extend, flagSignals_infoOf flag who prior]
      rfl

/-- The restricted menu where the flag is set, the original menu elsewhere. -/
def flaggedMenu (flag : ∀ who, N.InfoState who → Bool)
    (restricted : ∀ who, N.InfoState who → Set (Option (E.Action who))) (who : ι)
    (info : N.InfoState who) : Set (Option (E.Action who)) :=
  cond (flag who info) (restricted who info) (N.menu who info)

/-- The flagged model: the original signals with flagged information values,
the restricted menu at a set flag and the original menu otherwise. -/
def flagMenu (flag : ∀ who, N.InfoState who → Bool)
    (restricted : ∀ who, N.InfoState who → Set (Option (E.Action who)))
    (adequate : ∀ who {state}
      (trace : (E.restrictAvailable available included progress).Trace state)
      (choice : Option (E.Action who)),
      choice ∈ N.flaggedMenu flag restricted who (N.infoOf who (restrictAvailable.trace trace)) ↔
        LegalOption (E.restrictAvailable available included progress) state who choice) :
    InformationModel (E.restrictAvailable available included progress) where
  toInfoSignals := N.flagSignals flag
  menu who info := cond info.2 (restricted who info.1) (N.menu who info.1)
  menu_adequate who state trace choice := by
    rw [flagSignals_infoOf]
    exact adequate who trace choice

variable (flag : ∀ who, N.InfoState who → Bool)
  (restricted : ∀ who, N.InfoState who → Set (Option (E.Action who)))
  (adequate : ∀ who {state}
    (trace : (E.restrictAvailable available included progress).Trace state)
    (choice : Option (E.Action who)),
    choice ∈ N.flaggedMenu flag restricted who (N.infoOf who (restrictAvailable.trace trace)) ↔
      LegalOption (E.restrictAvailable available included progress) state who choice)

@[simp] theorem flagMenu_infoOf (who : ι) {state}
    (trace : (E.restrictAvailable available included progress).Trace state) :
    (N.flagMenu flag restricted adequate).infoOf who trace =
      (N.infoOf who (restrictAvailable.trace trace),
        flag who (N.infoOf who (restrictAvailable.trace trace))) :=
  N.flagSignals_infoOf flag who trace

/-- Own play along a restricted history is the own play along its embedding,
with flagged information values. -/
theorem flagMenu_ownPlay (who : ι) :
    ∀ {state} (trace : (E.restrictAvailable available included progress).Trace state),
      (N.flagMenu flag restricted adequate).ownPlay who trace =
        (N.ownPlay who (restrictAvailable.trace trace)).map
          (fun entry => ((entry.1, flag who entry.1), entry.2))
  | _, .start => rfl
  | _, .extend prior joint permitted realized => by
      change (N.flagMenu flag restricted adequate).ownPlay who
          (.extend prior joint permitted realized) =
        (N.ownPlay who (.extend (restrictAvailable.trace prior) joint
          (restrictAvailable.legal permitted) realized)).map _
      rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, flagMenu_ownPlay who prior,
        flagMenu_infoOf]
      cases joint who <;> rfl

/-- Flagging information values and restricting menus preserves perfect
recall. -/
theorem flagMenu_perfectRecall (recall : N.PerfectRecall) :
    (N.flagMenu flag restricted adequate).PerfectRecall := by
  intro who first second firstTrace secondTrace same
  rw [flagMenu_infoOf, flagMenu_infoOf] at same
  rw [flagMenu_ownPlay, flagMenu_ownPlay, recall who _ _ (congrArg Prod.fst same)]

private theorem choice_cast_val {T : ExecutionProtocol ι} (M : InformationModel T) {who : ι}
    {first second : M.InfoState who} (same : first = second)
    (cast : M.Choice who first = M.Choice who second) (choice : M.Choice who first) :
    (Eq.mp cast choice).1 = choice.1 := by
  subst same
  rfl

variable {small : (state : E.State) → (i : ι) → Set (E.Action i)}
  {smallIncluded : ∀ state i, small state i ⊆ E.available state i}
  {smallProgress : ∀ state, ¬ E.terminal state →
    ∃ joint, IsLegalJoint (E.active state) (small state) joint}
  (menu : ∀ who, N.InfoState who → Set (Option (E.Action who)))
  (smallAdequate : ∀ who {state}
    (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state)
    (choice : Option (E.Action who)),
    choice ∈ menu who (N.infoOf who (restrictAvailable.trace trace)) ↔
      LegalOption (E.restrictAvailable small smallIncluded smallProgress) state who choice)
  (contained : ∀ {state} (_ : (E.restrictAvailable small smallIncluded smallProgress).Trace state)
    i, small state i ⊆ available state i)

/-- A lifted trace of the smaller restriction carries the original information
value with an unset flag. -/
theorem flagMenu_infoOf_liftTrace (unflagged : ∀ who {state}
      (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
      flag who (N.infoOf who (restrictAvailable.trace trace)) = false) (who : ι) {state}
    (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state) :
    (N.flagMenu flag restricted adequate).infoOf who
        (restrictAvailable.liftTrace contained trace) =
      ((N.restrictMenu menu smallAdequate).infoOf who trace, false) := by
  rw [flagMenu_infoOf, restrictAvailable.trace_liftTrace, unflagged, restrictMenu_infoOf]

/-- **Flagged restriction.** A restriction of the protocol whose availability
stays inside the flagged one along its traces, whose traces never set the flag,
and whose menus lie inside the original ones embeds into the flagged model:
`(info, false)` on information values, inclusion on choices and the lifted trace
on histories. -/
def flagRestriction (unflagged : ∀ who {state}
      (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
      flag who (N.infoOf who (restrictAvailable.trace trace)) = false)
    (menuIncluded : ∀ who info, menu who info ⊆ N.menu who info) :
    (N.restrictMenu menu smallAdequate).ActionRestriction
      (N.flagMenu flag restricted adequate) where
  history := ⟨restrictAvailable.liftHistory contained,
    restrictAvailable.liftHistory_injective contained⟩
  information _ := ⟨fun info => (info, false), fun _ _ same => congrArg Prod.fst same⟩
  choice who info := ⟨fun choice => ⟨choice.1, menuIncluded who info choice.2⟩,
    fun first second same => Subtype.ext (congrArg Subtype.val same :)⟩
  initial := rfl
  length original := restrictAvailable.liftTrace_length contained original.trace
  terminal _ := Iff.rfl
  active _ _ := Iff.rfl
  observed who original :=
    N.flagMenu_infoOf_liftTrace flag restricted adequate menu smallAdequate contained unflagged
      who original.trace
  step original choices := by
    by_cases stopped : E.terminal original.state
    · have smaller : (N.restrictMenu menu smallAdequate).localStep original choices =
          PMF.pure original := by
        simp only [localStep]
        exact dite_eq_left_of_eq_true (eq_true stopped)
      have larger : ∀ targetChoices, (N.flagMenu flag restricted adequate).localStep
          (restrictAvailable.liftHistory contained original) targetChoices =
            PMF.pure (restrictAvailable.liftHistory contained original) := by
        intro targetChoices
        simp only [localStep]
        exact dite_eq_left_of_eq_true (eq_true stopped)
      rw [smaller, PMF.pure_map]
      exact (larger _).symm
    · let joint := fun who => (choices who).1
      have permitted : (E.restrictAvailable small smallIncluded smallProgress).Legal
          original.state joint :=
        legal_of_legalOption stopped fun who =>
          ((N.restrictMenu menu smallAdequate).menu_adequate who original.trace
            (choices who).1).mp (choices who).2
      have lifted : (E.restrictAvailable available included progress).Legal
          original.state joint :=
        ⟨permitted.1, permitted.2.mono (contained original.trace)⟩
      rw [(N.restrictMenu menu smallAdequate).localStep_eq_of_joint original choices stopped joint
        permitted (fun _ => rfl)]
      change _ = (N.flagMenu flag restricted adequate).localStep
        (restrictAvailable.liftHistory contained original) _
      rw [(N.flagMenu flag restricted adequate).localStep_eq_of_joint
        (restrictAvailable.liftHistory contained original) _ stopped joint lifted ?same]
      · rw [map_bindOnSupport]
        apply bindOnSupport_congr
        intro target realized
        rw [PMF.pure_map]
        rfl
      · intro who
        exact choice_cast_val _ (N.flagMenu_infoOf_liftTrace flag restricted adequate menu
          smallAdequate contained unflagged who original.trace).symm _ _

@[simp] theorem flagRestriction_history (unflagged : ∀ who {state}
      (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
      flag who (N.infoOf who (restrictAvailable.trace trace)) = false)
    (menuIncluded : ∀ who info, menu who info ⊆ N.menu who info)
    (original : (E.restrictAvailable small smallIncluded smallProgress).History) :
    (N.flagRestriction flag restricted adequate menu smallAdequate contained unflagged
      menuIncluded).history original = restrictAvailable.liftHistory contained original := rfl

@[simp] theorem flagRestriction_information (unflagged : ∀ who {state}
      (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
      flag who (N.infoOf who (restrictAvailable.trace trace)) = false)
    (menuIncluded : ∀ who info, menu who info ⊆ N.menu who info)
    (who : ι) (info : N.InfoState who) :
    (N.flagRestriction flag restricted adequate menu smallAdequate contained unflagged
      menuIncluded).information who info = (info, false) := rfl

@[simp] theorem flagRestriction_choice_val (unflagged : ∀ who {state}
      (trace : (E.restrictAvailable small smallIncluded smallProgress).Trace state),
      flag who (N.infoOf who (restrictAvailable.trace trace)) = false)
    (menuIncluded : ∀ who info, menu who info ⊆ N.menu who info)
    (who : ι) (info : N.InfoState who)
    (choice : (N.restrictMenu menu smallAdequate).Choice who info) :
    ((N.flagRestriction flag restricted adequate menu smallAdequate contained unflagged
      menuIncluded).choice who info choice).1 = choice.1 := rfl

end InformationModel

end GameTheory.Protocol
