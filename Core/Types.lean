/-
  Core/Types.lean — Shared types for PokemonLean
  Pokemon TCG foundational type definitions
-/

/-- Pokemon energy types in the TCG -/
inductive EnergyType where
  | grass | fire | water | lightning | psychic | fighting
  | darkness | metal | fairy | dragon | colorless | normal
  deriving Repr, BEq, DecidableEq

/-- Pokemon card types -/
inductive CardType where
  | basic | stage1 | stage2 | vstar | vmax | ex | gx | tagTeam | radiant
  deriving Repr, BEq, DecidableEq

/-- A Pokemon on the field -/
structure Pokemon where
  name : String
  hp : Nat
  currentHp : Nat
  energyType : EnergyType
  cardType : CardType
  retreatCost : Nat
  isEvolved : Bool := false
  deriving Repr, BEq

/-- Stadium card variants relevant to bench -/
inductive StadiumCard where
  | skyField          -- expands bench to 8
  | collapsedStadium  -- shrinks bench to 4
  | parallelCity      -- limits bench to 3 for one player
  | none              -- no stadium in play
  deriving Repr, BEq, DecidableEq

/-- Ability types for bench protection -/
inductive BenchAbility where
  | waveVeil       -- Manaphy: prevents bench damage from opponent
  | benchBarrier   -- Mr. Mime: prevents bench damage ≤ certain threshold
  | none
  deriving Repr, BEq, DecidableEq

/-- Supporter/trainer effects for bench targeting -/
inductive BenchTargeting where
  | bossOrders     -- switch opponent's benched to active
  | greninjaStar   -- snipe any benched for fixed damage
  | spreadDamage   -- damage all benched Pokemon
  | counterCatcher -- conditional gust effect
  | none
  deriving Repr, BEq, DecidableEq

/-- Board state for a single player -/
structure BoardState where
  active : Option Pokemon
  bench : List Pokemon
  stadium : StadiumCard
  benchAbility : BenchAbility
  deriving Repr

/-- Get bench size limit for a stadium -/
def stadiumBenchLimit (s : StadiumCard) : Nat :=
  match s with
  | StadiumCard.skyField => 8
  | StadiumCard.collapsedStadium => 4
  | StadiumCard.parallelCity => 3
  | StadiumCard.none => 5

/-- Default bench limit -/
def defaultBenchLimit : Nat := 5

/-- Check if bench is full given a stadium -/
def benchIsFull (bench : List Pokemon) (s : StadiumCard) : Bool :=
  decide (bench.length ≥ stadiumBenchLimit s)

/-- Check if bench has room -/
def benchHasRoom (bench : List Pokemon) (s : StadiumCard) : Bool :=
  decide (bench.length < stadiumBenchLimit s)

/-- Damage a Pokemon, reducing HP -/
def applyDamage (p : Pokemon) (dmg : Nat) : Pokemon :=
  { p with currentHp := p.currentHp - min dmg p.currentHp }

/-- Check if a Pokemon is knocked out -/
def isKnockedOut (p : Pokemon) : Bool :=
  p.currentHp == 0

/-- Remove a Pokemon at index from bench -/
def removeBenchAt (bench : List Pokemon) (idx : Nat) : List Pokemon :=
  bench.eraseIdx idx

/-- Count bench Pokemon of a specific energy type -/
def countBenchByType (bench : List Pokemon) (t : EnergyType) : Nat :=
  (bench.filter (fun p => p.energyType == t)).length

/-- Damage threshold for Mr. Mime's Bench Barrier -/
def mimeBarrierThreshold : Nat := 20

/-- Check if bench damage is blocked by an ability -/
def benchDamageBlocked (ability : BenchAbility) (damage : Nat) : Bool :=
  match ability with
  | BenchAbility.waveVeil => true
  | BenchAbility.benchBarrier => decide (damage ≤ mimeBarrierThreshold)
  | BenchAbility.none => false

/-- Calculate actual bench damage after protection -/
def effectiveBenchDamage (ability : BenchAbility) (damage : Nat) : Nat :=
  if benchDamageBlocked ability damage then 0 else damage

/-- Compute seats gained or lost when switching stadiums -/
def benchSeatDelta (old new_ : StadiumCard) : Int :=
  (stadiumBenchLimit new_ : Int) - (stadiumBenchLimit old : Int)

/-- Bench overflow when stadium changes -/
def benchOverflowCount (bench : List Pokemon) (_oldStadium newStadium : StadiumCard) : Nat :=
  let newLimit := stadiumBenchLimit newStadium
  if bench.length > newLimit then bench.length - newLimit else 0

/-- Discard Pokemon from bench to fit new limit -/
def trimBench (bench : List Pokemon) (limit : Nat) : List Pokemon :=
  bench.take limit

/-- Try to add a Pokemon to bench, respecting stadium limit -/
def addToBench (bench : List Pokemon) (p : Pokemon) (s : StadiumCard) : List Pokemon :=
  if bench.length < stadiumBenchLimit s then bench ++ [p] else bench

/-- A wall Pokemon has high HP and low retreat cost -/
def isWallPokemon (p : Pokemon) : Bool :=
  decide (p.hp ≥ 200) && decide (p.retreatCost ≤ 2)

/-- A setup attacker needs time on bench to power up -/
def isSetupAttacker (p : Pokemon) : Bool :=
  p.cardType == CardType.stage2 || p.cardType == CardType.vmax

/-- Count setup attackers on bench -/
def countSetupAttackers (bench : List Pokemon) : Nat :=
  (bench.filter isSetupAttacker).length

/-- Count empty bench slots -/
def emptyBenchSlots (bench : List Pokemon) (s : StadiumCard) : Nat :=
  stadiumBenchLimit s - bench.length

/-- Bench utilization percentage -/
def benchUtilization (bench : List Pokemon) (s : StadiumCard) : Nat :=
  (bench.length * 100) / stadiumBenchLimit s

/-- Total Pokemon on the field -/
def totalFieldPokemon (board : BoardState) : Nat :=
  (if board.active.isSome then 1 else 0) + board.bench.length

/-- Value of keeping a Pokemon on bench -/
def benchSitValue (p : Pokemon) : Nat :=
  (if p.isEvolved then 0 else 10) +
  (if isSetupAttacker p then 20 else 0) +
  p.retreatCost * 2

/-- Greninja Star's Moon Shuriken damage -/
def greninjaMoonShuriken : Nat := 90
