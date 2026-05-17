import Vegas.GameBridge.FOSG.FromCore

/-!
# State sufficiency for event-graph FOSG views

The canonical event-graph machine stores an extensional protocol configuration.
For this machine, the current public transcript and a player's current private
observation are sufficient to determine that player's currently available
bounded FOSG moves. Full FOSG history is not needed for move availability.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Player action availability in the event graph is determined by the public
transcript plus the values of the generated guard-visible reads. This is the
machine-level invariant underlying the coarser observation-sufficiency theorem:
private observation equality is one way to prove equality of these guard-visible
values. -/
theorem eventGraph_available_eq_of_publicView_eq_of_guardVisibleValue_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right)
    (hvisible :
      ∀ node, AgreeOnGuardVisibleReads g left right node) :
    EventGraph.available (programEventGraph g) left who =
      EventGraph.available (programEventGraph g) right who := by
  classical
  ext action
  constructor
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hpatch, hlegal⟩
    have hfrontierRight : action.node ∈ right.frontier := by
      simpa [eventGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierRight, hactor, hpatch,
      eventGraph_actionLegal_of_guardVisibleValue_eq g hfrontierRight
        (hvisible action.node) hlegal⟩
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hpatch, hlegal⟩
    have hfrontierLeft : action.node ∈ left.frontier := by
      simpa [eventGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierLeft, hactor, hpatch,
      eventGraph_actionLegal_of_guardVisibleValue_eq g hfrontierLeft
        (AgreeOnGuardVisibleReads.symm (hvisible action.node)) hlegal⟩

/-- Current machine observations determine the bounded FOSG optional moves at
the endpoint of two event-graph histories, provided neither endpoint is past
the bounded presentation cutoff. -/
theorem eventGraph_availableMoves_eq_of_currentObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hpriv :
      eventGraphObserve g who h.lastState.state =
        eventGraphObserve g who h'.lastState.state)
    (hpub :
      eventGraphPublicView g h.lastState.state =
        eventGraphPublicView g h'.lastState.state) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  simpa [GameTheory.FOSG.availableMoves] using
    eventGraph_boundedAvailableMovesAtState_eq_of_observation_eq
      g horizon who hcut hcut' hpriv hpub

/-- On nonempty bounded event-graph histories before the presentation cutoff,
equality of the latest FOSG private/public observation already determines the
current optional move set. -/
theorem eventGraph_availableMoves_eq_of_latestObservation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {h h' : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)}
    (hcut : ¬ horizon ≤ h.lastState.depth)
    (hcut' : ¬ horizon ≤ h'.lastState.depth)
    (hne : h.steps ≠ [])
    (hne' : h'.steps ≠ [])
    (hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
          (i := who) (h'.playerView who)) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMoves h' who := by
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  have hlatest₁ :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h.playerView who) =
        some
          (eventGraphObserve g who h.lastState.state,
            eventGraphPublicView g h.lastState.state) := by
    simpa [G, eventGraphMachine, EventGraph.toMachine,
      eventGraphMachineInterface] using
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
          horizon who h hne
  have hlatest₂ :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h'.playerView who) =
        some
          (eventGraphObserve g who h'.lastState.state,
            eventGraphPublicView g h'.lastState.state) := by
    simpa [G, eventGraphMachine, EventGraph.toMachine,
      eventGraphMachineInterface] using
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
          horizon who h' hne'
  have hlatestG :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h.playerView who) =
        GameTheory.FOSG.InfoState.latestObservation?
          (G := G) (i := who) (h'.playerView who) := by
    simpa [G] using hlatest
  rw [hlatest₁, hlatest₂] at hlatestG
  injection hlatestG with hobs
  have hpriv :
      eventGraphObserve g who h.lastState.state =
        eventGraphObserve g who h'.lastState.state :=
    congrArg Prod.fst hobs
  have hpub :
      eventGraphPublicView g h.lastState.state =
        eventGraphPublicView g h'.lastState.state :=
    congrArg Prod.snd hobs
  exact
    eventGraph_availableMoves_eq_of_currentObservation_eq
      g horizon who hcut hcut' hpriv hpub

end Vegas
