/-
  PokemonLean / Core / Types.lean

  Canonical core type definitions for PokemonLean.
  This file is self-contained and only relies on Lean's standard prelude.
-/

namespace PokemonLean.Core.Types

private def lawfulBEqOfDecidableEq (α : Type) [DecidableEq α] : LawfulBEq α where
  eq_of_beq := by
    intro a b h
    exact of_decide_eq_true h
  rfl := by
    intro a
    exact decide_eq_true rfl

/-- Pokemon typing used across cards and effects. -/
inductive PType where
  | fire
  | water
  | grass
  | electric
  | psychic
  | fighting
  | dark
  | steel
  | dragon
  | fairy
  | normal
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical TCG energy types (including Dragon, Fairy, and Colorless). -/
inductive EnergyType where
  | fire
  | water
  | grass
  | electric
  | psychic
  | fighting
  | dark
  | steel
  | dragon
  | fairy
  | normal
  | colorless
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Backward-compatible bridge from PType to EnergyType. -/
def EnergyType.typed : PType → EnergyType
  | .fire => .fire
  | .water => .water
  | .grass => .grass
  | .electric => .electric
  | .psychic => .psychic
  | .fighting => .fighting
  | .dark => .dark
  | .steel => .steel
  | .dragon => .dragon
  | .fairy => .fairy
  | .normal => .normal

/-- Evolution/special card stages used across formats. -/
inductive Stage where
  | basic
  | stage1
  | stage2
  | break_
  | mega
  | vmax
  | vstar
  | ex
  | gx
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Rule box groups relevant to prize mapping and interactions. -/
inductive RuleBox where
  | none
  | ex
  | gx
  | v
  | vmax
  | vstar
  | tagTeam
  | tera
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Card supertype for Pokemon, Trainer, and Energy cards. -/
inductive CardKind where
  | pokemon
  | trainer
  | energy
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Regulation marks used by rotation rules. -/
inductive RegulationMark where
  | D
  | E
  | F
  | G
  | H
  | I
  | preBW
  | bwToXY
  | smToSSH
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical special conditions for in-play Pokemon. -/
inductive SpecialCondition where
  | healthy
  | asleep
  | burned
  | confused
  | paralyzed
  | poisoned
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical attack payload. -/
structure Attack where
  name   : String
  cost   : List EnergyType
  damage : Nat
  effect : String
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical Pokemon payload: union of fields used across variants. -/
structure Pokemon where
  name           : String
  hp             : Nat
  maxHp          : Nat
  damage         : Nat
  currentHp      : Nat
  ptype          : Option PType
  energyType     : EnergyType
  stage          : Stage
  attacks        : List Attack
  weakness       : Option EnergyType
  resistance     : Option EnergyType
  retreatCost    : Nat
  ruleBox        : RuleBox
  evolvesFrom    : Option String
  abilityText    : Option String
  effectText     : String
  attachedEnergy : List EnergyType
  status         : Option SpecialCondition
  tool           : Option String
  isActive       : Bool
  isBasic        : Bool
  hasRuleBox     : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical card payload: union of Pokemon, Trainer, and Energy fields. -/
structure Card where
  name           : String
  kind           : CardKind
  pokemon        : Option Pokemon
  energyType     : Option EnergyType
  hp             : Nat
  stage          : Option Stage
  attacks        : List Attack
  weakness       : Option EnergyType
  resistance     : Option EnergyType
  retreatCost    : Nat
  ruleBox        : RuleBox
  evolvesFrom    : Option String
  abilityText    : Option String
  effectText     : String
  setCode        : Option String
  setNumber      : Option Nat
  regulationMark : Option RegulationMark
  isBasicEnergy  : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Player identifier. -/
inductive PlayerId where
  | player1
  | player2
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Standard turn phases. -/
inductive TurnPhase where
  | draw
  | main
  | attack
  | betweenTurns
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical per-player state with all primary zones and turn flags. -/
structure PlayerState where
  active          : Option Pokemon
  bench           : List Pokemon
  hand            : List Card
  deck            : List Card
  discard         : List Card
  prizes          : List Card
  lostZone        : List Card
  prizesRemaining : Nat
  deckSize        : Nat
  supporterPlayed : Bool
  energyAttached  : Bool
  gxUsed          : Bool
  vstarUsed       : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Canonical full game state with both players, turn state, and phase. -/
structure GameState where
  player1       : PlayerState
  player2       : PlayerState
  currentPlayer : PlayerId
  turnNumber    : Nat
  phase         : TurnPhase
  stadium       : Option Card
  winner        : Option PlayerId
  deriving DecidableEq, BEq, Repr, Inhabited

attribute [-instance] instBEqPType
attribute [-instance] instBEqEnergyType
attribute [-instance] instBEqStage
attribute [-instance] instBEqRuleBox
attribute [-instance] instBEqCardKind
attribute [-instance] instBEqRegulationMark
attribute [-instance] instBEqSpecialCondition
attribute [-instance] instBEqAttack
attribute [-instance] instBEqPokemon
attribute [-instance] instBEqCard
attribute [-instance] instBEqPlayerId
attribute [-instance] instBEqTurnPhase
attribute [-instance] instBEqPlayerState
attribute [-instance] instBEqGameState

instance : BEq PType := instBEqOfDecidableEq
instance : BEq EnergyType := instBEqOfDecidableEq
instance : BEq Stage := instBEqOfDecidableEq
instance : BEq RuleBox := instBEqOfDecidableEq
instance : BEq CardKind := instBEqOfDecidableEq
instance : BEq RegulationMark := instBEqOfDecidableEq
instance : BEq SpecialCondition := instBEqOfDecidableEq
instance : BEq Attack := instBEqOfDecidableEq
instance : BEq Pokemon := instBEqOfDecidableEq
instance : BEq Card := instBEqOfDecidableEq
instance : BEq PlayerId := instBEqOfDecidableEq
instance : BEq TurnPhase := instBEqOfDecidableEq
instance : BEq PlayerState := instBEqOfDecidableEq
instance : BEq GameState := instBEqOfDecidableEq

instance : LawfulBEq PType := lawfulBEqOfDecidableEq PType
instance : LawfulBEq EnergyType := lawfulBEqOfDecidableEq EnergyType
instance : LawfulBEq Stage := lawfulBEqOfDecidableEq Stage
instance : LawfulBEq RuleBox := lawfulBEqOfDecidableEq RuleBox
instance : LawfulBEq CardKind := lawfulBEqOfDecidableEq CardKind
instance : LawfulBEq RegulationMark := lawfulBEqOfDecidableEq RegulationMark
instance : LawfulBEq SpecialCondition := lawfulBEqOfDecidableEq SpecialCondition
instance : LawfulBEq Attack := lawfulBEqOfDecidableEq Attack
instance : LawfulBEq Pokemon := lawfulBEqOfDecidableEq Pokemon
instance : LawfulBEq Card := lawfulBEqOfDecidableEq Card
instance : LawfulBEq PlayerId := lawfulBEqOfDecidableEq PlayerId
instance : LawfulBEq TurnPhase := lawfulBEqOfDecidableEq TurnPhase
instance : LawfulBEq PlayerState := lawfulBEqOfDecidableEq PlayerState
instance : LawfulBEq GameState := lawfulBEqOfDecidableEq GameState

end PokemonLean.Core.Types

namespace PokemonLean.Core

/-- Backward-compatible alias for legacy imports. -/
abbrev PType := Types.PType

/-- Backward-compatible alias for legacy imports. -/
abbrev EnergyType := Types.EnergyType

/-- Lift a Pokemon type into its matching typed energy. -/
def PType.toEnergy (t : PType) : EnergyType := .typed t

end PokemonLean.Core
