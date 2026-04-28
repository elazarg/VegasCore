import Vegas.FOSG.Observation

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}
namespace Observed

/-- Last element of a list, as an `Option`. Kept local to avoid depending on
which `List.getLast?` lemmas are imported. -/
def last? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => last? xs

@[simp] theorem last?_append_singleton {α : Type} (xs : List α) (x : α) :
    last? (xs ++ [x]) = some x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simpa [last?] using ih

/-- Observation events extracted from the final program-action FOSG information
state. -/
noncomputable def programObservationEvents
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    List (PrivateObs g who × PublicObs g hctx) :=
  s.filterMap
    (GameTheory.FOSG.PlayerEvent.observationPart
      (G := observedProgramFOSG g hctx) (i := who))

noncomputable def programLatestObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    Option (PrivateObs g who × PublicObs g hctx) :=
  last? (programObservationEvents g hctx who s)

@[simp] theorem programObservationEvents_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programObservationEvents g hctx who [] = [] := rfl

@[simp] theorem programLatestObservation?_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programLatestObservation? g hctx who [] = none := rfl

theorem programLatestObservation?_append_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (priv : PrivateObs g who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

theorem programLatestObservation?_append_act_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (a : ProgramAction g.prog who)
    (priv : PrivateObs g who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.act a,
        GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

/-- Extending a program-action FOSG history records the destination cursor
world's Vegas view/public state as the latest information-state observation. -/
theorem programLatestObservation?_history_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programLatestObservation? g hctx who ((h.snoc a dst support).playerView who) =
      some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst) := by
  rw [GameTheory.FOSG.History.playerView_snoc]
  let e : (observedProgramFOSG g hctx).Step :=
    { src := h.lastState, act := a, dst := dst, support := support }
  change programLatestObservation? g hctx who (h.playerView who ++ e.playerView who) =
    some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst)
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)

/-- Appending one concrete observed-program step records the destination cursor
world's observation as the latest player observation. -/
theorem programLatestObservation?_history_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programLatestObservation? g hctx who ((h.appendStep e hsrc).playerView who) =
      some (privateObsOfCursorWorld who (h.appendStep e hsrc).lastState,
        publicObsOfCursorWorld (h.appendStep e hsrc).lastState) := by
  rw [GameTheory.FOSG.History.playerView]
  change programLatestObservation? g hctx who
      (GameTheory.FOSG.History.playerViewFrom (G := observedProgramFOSG g hctx)
        who (h.steps ++ [e])) =
    some (privateObsOfCursorWorld who (h.appendStep e hsrc).lastState,
      publicObsOfCursorWorld (h.appendStep e hsrc).lastState)
  rw [GameTheory.FOSG.History.playerViewFrom_append_singleton]
  simp only [GameTheory.FOSG.History.lastState_appendStep]
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [GameTheory.FOSG.History.playerView, observedProgramFOSG] using
        programLatestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfCursorWorld who e.dst) (publicObsOfCursorWorld e.dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [GameTheory.FOSG.History.playerView, observedProgramFOSG] using
        programLatestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfCursorWorld who e.dst) (publicObsOfCursorWorld e.dst)

/-- The initial observed-program history has no latest program observation. -/
@[simp] theorem programLatestObservation?_history_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programLatestObservation? g hctx who
        ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      none := by
  simp [programLatestObservation?, programObservationEvents, last?]

/-- Any nonempty observed-program history records the final cursor world's
private/public observation as the latest program observation for every player. -/
theorem programLatestObservation?_history_of_ne_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (hne : h.steps ≠ []) :
    programLatestObservation? g hctx who (h.playerView who) =
      some (privateObsOfCursorWorld who h.lastState,
        publicObsOfCursorWorld h.lastState) := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          exact False.elim (hne rfl)
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq]
          exact programLatestObservation?_history_appendStep
            g hctx who hprefix e hsrc

theorem observedProgramFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (observedProgramFOSG g hctx).LegalObservable := by
  intro who h h' hInfo
  by_cases hnil : h.steps = []
  · have h_eq_nil :
        h = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
      GameTheory.FOSG.History.ext hnil
    subst h_eq_nil
    by_cases hnil' : h'.steps = []
    · have h'_eq_nil :
          h' = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
        GameTheory.FOSG.History.ext hnil'
      subst h'_eq_nil
      rfl
    · have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_nil,
        programLatestObservation?_history_of_ne_nil g hctx who h' hnil'] at hlatest
      cases hlatest
  · by_cases hnil' : h'.steps = []
    · have h'_eq_nil :
          h' = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
        GameTheory.FOSG.History.ext hnil'
      subst h'_eq_nil
      have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_of_ne_nil g hctx who h hnil,
        programLatestObservation?_history_nil] at hlatest
      cases hlatest
    · have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_of_ne_nil g hctx who h hnil,
        programLatestObservation?_history_of_ne_nil g hctx who h' hnil'] at hlatest
      injection hlatest with hobs
      have hpriv :
          privateObsOfCursorWorld who h.lastState =
            privateObsOfCursorWorld who h'.lastState :=
        congrArg Prod.fst hobs
      simpa [GameTheory.FOSG.availableMoves] using
        observedProgram_availableMovesAtState_eq_of_privateObs_eq
          g hctx who h.lastState h'.lastState hpriv

end Observed

end FOSGBridge
end Vegas
