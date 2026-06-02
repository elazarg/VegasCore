import Vegas.Frontier.SolutionConcepts
import Vegas.Language.Nullable
import GameTheory.Concepts.Dominance.DominanceNash

/-!
# Nullable lowering facts

Nullable surface commitments are represented by the ordinary core guard
interface.  The facts in `Vegas.Language.Nullable` are re-exported here as part of
the checked-source theorem surface.  The game-theoretic repair facts are
parametric: a particular nullable game supplies the proof that its abort moves
are strictly dominated, and then the generic Nash-avoidance theorem applies.
-/

namespace Vegas

namespace VegasLang

/-- The nullable action synthesized by lowering is always guard-legal:
choosing `none` satisfies the compiled guard independently of the source guard.
-/
theorem nullableGuard_accepts_none
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
      (Expr.nullableCommitGuard R) Option.none env = true :=
  nullableGuard_none_legal R env

/-- On ordinary source values, a lowered nullable guard agrees with the
original guard.
-/
theorem nullableGuard_some_agrees
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (value : Val b) (env : Env Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := simpleExpr)
        (Expr.nullableCommitGuard R) (some value) env =
      evalGuard (Player := P) (L := simpleExpr) R value env :=
  nullableGuard_some_eq R value env

/-- Every lowered nullable guard admits at least one legal action. -/
theorem nullableGuard_has_legal_action
    {P : Type} [DecidableEq P]
    {Γ : VCtx P simpleExpr} {secret : VarId} {b : BaseTy}
    [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool) :
    ∀ env : Env Val (eraseVCtx Γ),
      ∃ action : Val (.option b),
        evalGuard (Player := P) (L := simpleExpr)
          (Expr.nullableCommitGuard R) action env = true :=
  nullableGuard_satisfiable R

end VegasLang

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- A pure-strategy repair certificate for a checked program: every strategy
marked bad is strictly dominated by its repaired strategy.  Nullable games use
this to express that aborting is punished enough to make abort strategies
irrelevant to Nash analysis. -/
structure PureFrontierStrictDominationRepair
    (program : WFProgram P L) [FiniteDomains program] (player : P) where
  Bad : program.PureFrontierStrategy player → Prop
  repair :
    program.PureFrontierStrategy player →
      program.PureFrontierStrategy player
  dominates_bad :
    ∀ strategy, Bad strategy →
      program.PureFrontierStrictlyDominates player
        (repair strategy) strategy

/-- Behavioral-strategy counterpart of
`PureFrontierStrictDominationRepair`. -/
structure BehavioralFrontierStrictDominationRepair
    (program : WFProgram P L) [FiniteDomains program] (player : P) where
  Bad : program.BehavioralFrontierStrategy player → Prop
  repair :
    program.BehavioralFrontierStrategy player →
      program.BehavioralFrontierStrategy player
  dominates_bad :
    ∀ strategy, Bad strategy →
      program.BehavioralFrontierStrictlyDominates player
        (repair strategy) strategy

namespace PureFrontierStrictDominationRepair

variable {program : WFProgram P L} [FiniteDomains program] {player : P}

/-- If a pure nullable repair marks a strategy bad, the repair strictly
dominates it. -/
theorem nullable_abort_strictly_dominated
    (repair : PureFrontierStrictDominationRepair program player)
    {strategy : program.PureFrontierStrategy player}
    (hbad : repair.Bad strategy) :
    program.PureFrontierStrictlyDominates player
      (repair.repair strategy) strategy :=
  repair.dominates_bad strategy hbad

/-- Pure Nash profiles cannot play strategies that a nullable repair marks as
bad. -/
theorem nash_avoids_bad
    (repair : PureFrontierStrictDominationRepair program player)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    ¬ repair.Bad (profile player) := by
  intro hbad
  exact
    (repair.dominates_bad (profile player) hbad).not_nash hNash

end PureFrontierStrictDominationRepair

namespace BehavioralFrontierStrictDominationRepair

variable {program : WFProgram P L} [FiniteDomains program] {player : P}

/-- If a behavioral nullable repair marks a strategy bad, the repair strictly
dominates it. -/
theorem nullable_abort_strictly_dominated
    (repair : BehavioralFrontierStrictDominationRepair program player)
    {strategy : program.BehavioralFrontierStrategy player}
    (hbad : repair.Bad strategy) :
    program.BehavioralFrontierStrictlyDominates player
      (repair.repair strategy) strategy :=
  repair.dominates_bad strategy hbad

/-- Behavioral Nash profiles cannot play strategies that a nullable repair
marks as bad. -/
theorem nash_avoids_bad
    (repair : BehavioralFrontierStrictDominationRepair program player)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    ¬ repair.Bad (profile player) := by
  intro hbad
  exact
    (repair.dominates_bad (profile player) hbad).not_nash hNash

end BehavioralFrontierStrictDominationRepair

/-- If every player's bad nullable-abort strategies are exactly the strategies
that fail an honesty predicate, every pure Nash profile is honest. -/
theorem pureFrontier_nullable_equilibria_are_honest
    (program : WFProgram P L) [FiniteDomains program]
    (Honest :
      ∀ player, program.PureFrontierStrategy player → Prop)
    (repair :
      ∀ player, PureFrontierStrictDominationRepair program player)
    (hbad :
      ∀ player strategy,
        (repair player).Bad strategy ↔ ¬ Honest player strategy)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    ∀ player, Honest player (profile player) := by
  intro player
  by_contra hnot
  exact
    (repair player).nash_avoids_bad hNash
      ((hbad player (profile player)).2 hnot)

/-- Behavioral-strategy counterpart of
`pureFrontier_nullable_equilibria_are_honest`. -/
theorem behavioralFrontier_nullable_equilibria_are_honest
    (program : WFProgram P L) [FiniteDomains program]
    (Honest :
      ∀ player, program.BehavioralFrontierStrategy player → Prop)
    (repair :
      ∀ player, BehavioralFrontierStrictDominationRepair program player)
    (hbad :
      ∀ player strategy,
        (repair player).Bad strategy ↔ ¬ Honest player strategy)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    ∀ player, Honest player (profile player) := by
  intro player
  by_contra hnot
  exact
    (repair player).nash_avoids_bad hNash
      ((hbad player (profile player)).2 hnot)

/-- Pure-frontier honest embeddings preserve expected utility when the
embedding carries an explicit EU-preservation proof. -/
structure PureFrontierHonestEmbedding
    (source target : WFProgram P L)
    [FiniteDomains source] [FiniteDomains target] where
  mapStrategy :
    ∀ player,
      source.PureFrontierStrategy player →
        target.PureFrontierStrategy player
  eu_eq :
    ∀ profile player,
      target.pureFrontierGame.eu
          (fun who => mapStrategy who (profile who)) player =
        source.pureFrontierGame.eu profile player

/-- Behavioral-frontier honest embeddings preserve expected utility when the
embedding carries an explicit EU-preservation proof. -/
structure BehavioralFrontierHonestEmbedding
    (source target : WFProgram P L)
    [FiniteDomains source] [FiniteDomains target] where
  mapStrategy :
    ∀ player,
      source.BehavioralFrontierStrategy player →
        target.BehavioralFrontierStrategy player
  eu_eq :
    ∀ profile player,
      target.behavioralFrontierGame.eu
          (fun who => mapStrategy who (profile who)) player =
        source.behavioralFrontierGame.eu profile player

namespace PureFrontierHonestEmbedding

variable {source target : WFProgram P L}
variable [FiniteDomains source] [FiniteDomains target]

/-- Honest pure-frontier compilation preserves expected utility. -/
theorem preserves_eu
    (embedding : PureFrontierHonestEmbedding source target)
    (profile : source.PureFrontierProfile) (player : P) :
    target.pureFrontierGame.eu
        (fun who => embedding.mapStrategy who (profile who)) player =
      source.pureFrontierGame.eu profile player :=
  embedding.eu_eq profile player

/-- Honest pure-frontier compilation is never worse when expected utility is
preserved exactly. -/
theorem no_honest_disadvantage
    (embedding : PureFrontierHonestEmbedding source target)
    (profile : source.PureFrontierProfile) (player : P) :
    target.pureFrontierGame.eu
        (fun who => embedding.mapStrategy who (profile who)) player ≥
      source.pureFrontierGame.eu profile player := by
  rw [embedding.preserves_eu profile player]

end PureFrontierHonestEmbedding

namespace BehavioralFrontierHonestEmbedding

variable {source target : WFProgram P L}
variable [FiniteDomains source] [FiniteDomains target]

/-- Honest behavioral-frontier compilation preserves expected utility. -/
theorem preserves_eu
    (embedding : BehavioralFrontierHonestEmbedding source target)
    (profile : source.BehavioralFrontierProfile) (player : P) :
    target.behavioralFrontierGame.eu
        (fun who => embedding.mapStrategy who (profile who)) player =
      source.behavioralFrontierGame.eu profile player :=
  embedding.eu_eq profile player

/-- Honest behavioral-frontier compilation is never worse when expected
utility is preserved exactly. -/
theorem no_honest_disadvantage
    (embedding : BehavioralFrontierHonestEmbedding source target)
    (profile : source.BehavioralFrontierProfile) (player : P) :
    target.behavioralFrontierGame.eu
        (fun who => embedding.mapStrategy who (profile who)) player ≥
      source.behavioralFrontierGame.eu profile player := by
  rw [embedding.preserves_eu profile player]

end BehavioralFrontierHonestEmbedding

end WFProgram

end Vegas
