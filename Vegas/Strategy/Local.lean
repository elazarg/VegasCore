import Vegas.Protocol.Strategic

/-!
# Local strategy predicates

Information-state predicates for saying what a checked Vegas strategy chooses
or supports locally. These predicates are intentionally independent of payoff
and equilibrium notions: nullable abort avoidance, no-signalling restrictions,
and program-specific invariants can all instantiate the same shape.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The bounded FOSG used by the finite strategy semantics of a checked Vegas
program. -/
noncomputable abbrev strategyFOSG (g : WFProgram P L) :=
  (syntaxGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog)

/-- Reachable information states at the finite strategy horizon. -/
abbrev StrategyInfoState
    (g : WFProgram P L) (who : P) : Type :=
  (strategyFOSG g).ReachableInfoState who

/-- Optional local moves at the finite strategy horizon. -/
abbrev StrategyMove
    (g : WFProgram P L) (who : P) : Type :=
  Option ((syntaxGraphFOSGView g).Act who)

/-- Local availability of an optional move at a reachable information state. -/
def MoveAvailableAtInfo
    (g : WFProgram P L) (who : P)
    (info : StrategyInfoState g who)
    (move : StrategyMove g who) : Prop :=
  move ∈ (strategyFOSG g).availableMovesAtInfoState who info.1

/-- A pure strategy chooses only moves satisfying `Allowed` at every reachable
information state. -/
def PureStrategyChoosesOnly
    (g : WFProgram P L) (who : P)
    (Allowed : StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : pureStrategyAt g who) : Prop :=
  ∀ info, Allowed info (σ.1 info)

/-- A behavioral strategy supports only moves satisfying `Allowed` at every
reachable information state. -/
def BehavioralStrategySupportsOnly
    (g : WFProgram P L) (who : P)
    (Allowed : StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : behavioralStrategyPMFAt g who) : Prop :=
  ∀ info move, move ∈ (σ.1 info).support → Allowed info move

/-- A pure profile satisfies local per-player move predicates. -/
def PureProfileChoosesOnly
    (g : WFProgram P L)
    (Allowed :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : pureProfileAt g) : Prop :=
  ∀ who, PureStrategyChoosesOnly g who (Allowed who) (σ who)

/-- A behavioral profile supports only local per-player allowed moves. -/
def BehavioralProfileSupportsOnly
    (g : WFProgram P L)
    (Allowed :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : behavioralProfilePMFAt g) : Prop :=
  ∀ who, BehavioralStrategySupportsOnly g who (Allowed who) (σ who)

/-- A pure strategy avoids every local move satisfying `Bad`. -/
def PureStrategyAvoids
    (g : WFProgram P L) (who : P)
    (Bad : StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : pureStrategyAt g who) : Prop :=
  PureStrategyChoosesOnly g who (fun info move => ¬ Bad info move) σ

/-- A behavioral strategy supports no local move satisfying `Bad`. -/
def BehavioralStrategyAvoids
    (g : WFProgram P L) (who : P)
    (Bad : StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : behavioralStrategyPMFAt g who) : Prop :=
  BehavioralStrategySupportsOnly g who (fun info move => ¬ Bad info move) σ

/-- A pure profile avoids every per-player local bad-move predicate. -/
def PureProfileAvoids
    (g : WFProgram P L)
    (Bad : ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : pureProfileAt g) : Prop :=
  PureProfileChoosesOnly g (fun who info move => ¬ Bad who info move) σ

/-- A behavioral profile supports no per-player local bad move. -/
def BehavioralProfileAvoids
    (g : WFProgram P L)
    (Bad : ∀ who, StrategyInfoState g who → StrategyMove g who → Prop)
    (σ : behavioralProfilePMFAt g) : Prop :=
  BehavioralProfileSupportsOnly g
    (fun who info move => ¬ Bad who info move) σ

theorem PureStrategyChoosesOnly.mono
    {g : WFProgram P L} {who : P}
    {Allowed Allowed' :
      StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ info move, Allowed info move → Allowed' info move)
    {σ : pureStrategyAt g who}
    (hσ : PureStrategyChoosesOnly g who Allowed σ) :
    PureStrategyChoosesOnly g who Allowed' σ :=
  fun info => h info (σ.1 info) (hσ info)

theorem BehavioralStrategySupportsOnly.mono
    {g : WFProgram P L} {who : P}
    {Allowed Allowed' :
      StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ info move, Allowed info move → Allowed' info move)
    {σ : behavioralStrategyPMFAt g who}
    (hσ : BehavioralStrategySupportsOnly g who Allowed σ) :
    BehavioralStrategySupportsOnly g who Allowed' σ :=
  fun info move hmem => h info move (hσ info move hmem)

theorem PureProfileChoosesOnly.mono
    {g : WFProgram P L}
    {Allowed Allowed' :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ who info move, Allowed who info move → Allowed' who info move)
    {σ : pureProfileAt g}
    (hσ : PureProfileChoosesOnly g Allowed σ) :
    PureProfileChoosesOnly g Allowed' σ :=
  fun who =>
    (PureStrategyChoosesOnly.mono (fun info move => h who info move)
      (hσ who))

theorem BehavioralProfileSupportsOnly.mono
    {g : WFProgram P L}
    {Allowed Allowed' :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ who info move, Allowed who info move → Allowed' who info move)
    {σ : behavioralProfilePMFAt g}
    (hσ : BehavioralProfileSupportsOnly g Allowed σ) :
    BehavioralProfileSupportsOnly g Allowed' σ :=
  fun who =>
    (BehavioralStrategySupportsOnly.mono (fun info move => h who info move)
      (hσ who))

theorem PureStrategyAvoids.mono
    {g : WFProgram P L} {who : P}
    {Bad Bad' : StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ info move, Bad' info move → Bad info move)
    {σ : pureStrategyAt g who}
    (hσ : PureStrategyAvoids g who Bad σ) :
    PureStrategyAvoids g who Bad' σ :=
  PureStrategyChoosesOnly.mono
    (fun info move hnot hbad' => hnot (h info move hbad')) hσ

theorem BehavioralStrategyAvoids.mono
    {g : WFProgram P L} {who : P}
    {Bad Bad' : StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ info move, Bad' info move → Bad info move)
    {σ : behavioralStrategyPMFAt g who}
    (hσ : BehavioralStrategyAvoids g who Bad σ) :
    BehavioralStrategyAvoids g who Bad' σ :=
  BehavioralStrategySupportsOnly.mono
    (fun info move hnot hbad' => hnot (h info move hbad')) hσ

theorem PureProfileAvoids.mono
    {g : WFProgram P L}
    {Bad Bad' :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ who info move, Bad' who info move → Bad who info move)
    {σ : pureProfileAt g}
    (hσ : PureProfileAvoids g Bad σ) :
    PureProfileAvoids g Bad' σ :=
  PureProfileChoosesOnly.mono
    (fun who info move hnot hbad' => hnot (h who info move hbad')) hσ

theorem BehavioralProfileAvoids.mono
    {g : WFProgram P L}
    {Bad Bad' :
      ∀ who, StrategyInfoState g who → StrategyMove g who → Prop}
    (h : ∀ who info move, Bad' who info move → Bad who info move)
    {σ : behavioralProfilePMFAt g}
    (hσ : BehavioralProfileAvoids g Bad σ) :
    BehavioralProfileAvoids g Bad' σ :=
  BehavioralProfileSupportsOnly.mono
    (fun who info move hnot hbad' => hnot (h who info move hbad')) hσ

/-- The reachable-legal pure strategy carrier chooses only moves available at
the corresponding information state. -/
theorem pureStrategy_chooses_available
    (g : WFProgram P L) (who : P)
    (σ : pureStrategyAt g who) :
    PureStrategyChoosesOnly g who (MoveAvailableAtInfo g who) σ := by
  intro info
  rcases info with ⟨s, h, hs⟩
  have hinfo :
      (strategyFOSG g).reachableInfoStateOfHistory who h =
        (⟨s, ⟨h, hs⟩⟩ : StrategyInfoState g who) := by
    apply Subtype.ext
    exact hs
  have hlegal :
      σ.1 (⟨s, ⟨h, hs⟩⟩ : StrategyInfoState g who) ∈
        (strategyFOSG g).availableMoves h who := by
    simpa [hinfo] using σ.2 h
  have hmem :=
    (strategyFOSG g).mem_availableMovesAtInfoState_of_history h hlegal
  simpa [MoveAvailableAtInfo, hs] using hmem

/-- The reachable-legal behavioral strategy carrier supports only moves
available at the corresponding information state. -/
theorem behavioralStrategy_supports_available
    (g : WFProgram P L) (who : P)
    (σ : behavioralStrategyPMFAt g who) :
    BehavioralStrategySupportsOnly g who (MoveAvailableAtInfo g who) σ := by
  intro info move hsupport
  rcases info with ⟨s, h, hs⟩
  have hinfo :
      (strategyFOSG g).reachableInfoStateOfHistory who h =
        (⟨s, ⟨h, hs⟩⟩ : StrategyInfoState g who) := by
    apply Subtype.ext
    exact hs
  have hsupport' :
      move ∈
        (σ.1 ((strategyFOSG g).reachableInfoStateOfHistory who h)).support := by
    simpa [hinfo] using hsupport
  have hlegal : move ∈ (strategyFOSG g).availableMoves h who :=
    σ.2 h hsupport'
  have hmem :=
    (strategyFOSG g).mem_availableMovesAtInfoState_of_history h hlegal
  simpa [MoveAvailableAtInfo, hs] using hmem

/-- Every reachable-legal pure profile chooses only locally available moves. -/
theorem pureProfile_chooses_available
    (g : WFProgram P L) (σ : pureProfileAt g) :
    PureProfileChoosesOnly g (fun who => MoveAvailableAtInfo g who) σ :=
  fun who => pureStrategy_chooses_available g who (σ who)

/-- Every reachable-legal behavioral profile supports only locally available
moves. -/
theorem behavioralProfile_supports_available
    (g : WFProgram P L) (σ : behavioralProfilePMFAt g) :
    BehavioralProfileSupportsOnly g
      (fun who => MoveAvailableAtInfo g who) σ :=
  fun who => behavioralStrategy_supports_available g who (σ who)

end Vegas
