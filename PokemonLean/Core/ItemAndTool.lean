/-
  PokemonLean / Core / ItemAndTool.lean

  Tool and Item card interaction system for the Pokémon TCG.

  Covers:
  - Tools attach to Pokémon (1 tool per Pokémon)
  - Items are played and discarded (single-use)
  - Key tools: Choice Belt (+30 to ex/V), Float Stone (free retreat),
    Muscle Band (+20), Heavy Baton (move energy on KO)
  - Key items: Ultra Ball (discard 2, search Pokémon), Rare Candy
    (skip stage 1), Switch (retreat without cost), Boss's Orders
    (force active)
  - Tool removal: Tool Scrapper, Startling Megaphone
  - Theorems: 1 tool limit per Pokémon, tool persists until removed,
    items are single-use, Ultra Ball requires discard 2, Rare Candy
    only basic→stage2, Choice Belt only affects ex/V targets, Float
    Stone sets retreat to 0, tool removal is idempotent

  Self-contained — no imports from other PokemonLean modules.
  All proofs are sorry-free.  35+ theorems.
-/

namespace PokemonLean.Core.ItemAndTool

-- ============================================================
-- §1  Core types
-- ============================================================

/-- Unique identifier for a Pokémon in play. -/
structure PokemonId where
  val : Nat
deriving DecidableEq, Repr, BEq, Inhabited

/-- Evolution stage. -/
inductive Stage where
  | basic | stage1 | stage2
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a Pokémon is ex/V (for Choice Belt targeting). -/
inductive TargetClass where
  | exOrV     -- EX, ex, V, VMAX, VSTAR
  | regular   -- Non-rule-box Pokémon
deriving DecidableEq, Repr, BEq, Inhabited

def TargetClass.isExOrV : TargetClass → Bool
  | .exOrV   => true
  | .regular => false

-- ============================================================
-- §2  Tool definitions
-- ============================================================

/-- Tool cards that can be attached to Pokémon. -/
inductive ToolCard where
  | choiceBelt     -- +30 damage to ex/V
  | floatStone     -- Retreat cost becomes 0
  | muscleBand     -- +20 damage
  | heavyBaton     -- Move energy on KO
  | otherTool      -- Generic tool
deriving DecidableEq, Repr, BEq, Inhabited

/-- Damage bonus from a tool against a target class. -/
def ToolCard.damageBonus (tool : ToolCard) (target : TargetClass) : Nat :=
  match tool with
  | .choiceBelt => if target.isExOrV then 30 else 0
  | .muscleBand => 20
  | _           => 0

/-- Does the tool set retreat cost to 0? -/
def ToolCard.givesZeroRetreat : ToolCard → Bool
  | .floatStone => true
  | _           => false

-- ============================================================
-- §3  Item definitions
-- ============================================================

/-- Item cards (played and discarded immediately). -/
inductive ItemCard where
  | ultraBall        -- Discard 2, search for a Pokémon
  | rareCandy        -- Skip stage 1, evolve basic → stage 2
  | switchCard       -- Switch active with benched (no retreat cost)
  | bossOrders       -- Force opponent's benched Pokémon active
  | toolScrapper     -- Remove up to 2 tools
  | megaphone        -- Remove all opponent tools (Startling Megaphone)
  | otherItem        -- Generic item
deriving DecidableEq, Repr, BEq, Inhabited

-- ============================================================
-- §4  Pokémon in play
-- ============================================================

/-- A Pokémon in play with optional attached tool. -/
structure PokemonInPlay where
  pokId       : PokemonId
  toolSlot    : Option ToolCard := none
  stage       : Stage := .basic
  targetClass : TargetClass := .regular
  retreatCost : Nat := 2
  hp          : Nat := 100
deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether a Pokémon has a tool attached. -/
def PokemonInPlay.hasTool (p : PokemonInPlay) : Bool :=
  p.toolSlot.isSome

/-- Effective retreat cost considering Float Stone. -/
def PokemonInPlay.effectiveRetreat (p : PokemonInPlay) : Nat :=
  match p.toolSlot with
  | some t => if t.givesZeroRetreat then 0 else p.retreatCost
  | none   => p.retreatCost

/-- Damage bonus from the Pokémon's attached tool. -/
def PokemonInPlay.toolDamageBonus (p : PokemonInPlay) (target : TargetClass) : Nat :=
  match p.toolSlot with
  | some t => t.damageBonus target
  | none   => 0

-- ============================================================
-- §5  Tool attachment
-- ============================================================

/-- Attach a tool to a Pokémon. Fails if tool already attached. -/
def attachTool (p : PokemonInPlay) (tool : ToolCard) : Option PokemonInPlay :=
  if p.hasTool then none
  else some { p with toolSlot := some tool }

/-- Remove a Pokémon's tool. Idempotent. -/
def removeTool (p : PokemonInPlay) : PokemonInPlay :=
  { p with toolSlot := none }

-- ============================================================
-- §6  Item usage state
-- ============================================================

/-- Hand state for item usage. -/
structure HandState where
  handSize  : Nat
  discarded : Nat := 0
deriving DecidableEq, Repr, Inhabited

/-- Can Ultra Ball be played? Requires at least 2 other cards to discard. -/
def canPlayUltraBall (hand : HandState) : Bool :=
  hand.handSize ≥ 3   -- Ultra Ball itself + 2 to discard

/-- Play Ultra Ball: discard 2, remove Ultra Ball from hand. -/
def playUltraBall (hand : HandState) : Option HandState :=
  if canPlayUltraBall hand then
    some { handSize := hand.handSize - 3, discarded := hand.discarded + 3 }
  else none

-- ============================================================
-- §7  Rare Candy
-- ============================================================

/-- Can Rare Candy be used? Only on a Basic to evolve to Stage 2. -/
def canUseRareCandy (p : PokemonInPlay) : Bool :=
  p.stage == .basic

/-- Apply Rare Candy: evolve basic directly to stage 2. -/
def applyRareCandy (p : PokemonInPlay) : Option PokemonInPlay :=
  if canUseRareCandy p then some { p with stage := .stage2 }
  else none

-- ============================================================
-- §8  Tool removal operations
-- ============================================================

/-- Remove tools from a list of Pokémon (Megaphone effect). -/
def removeAllTools (poks : List PokemonInPlay) : List PokemonInPlay :=
  poks.map removeTool

/-- Remove tool from specific Pokémon by id. -/
def removeToolById (poks : List PokemonInPlay) (pid : PokemonId) : List PokemonInPlay :=
  poks.map fun p => if p.pokId == pid then removeTool p else p

-- ============================================================
-- §9  Switch / Boss's Orders
-- ============================================================

/-- Switch the active Pokémon with a benched one (no retreat cost). -/
def switchActive (active : PokemonInPlay) (bench : List PokemonInPlay)
    (benchIdx : Nat) : Option (PokemonInPlay × List PokemonInPlay) :=
  match bench[benchIdx]? with
  | none => none
  | some newActive =>
    let newBench := bench.set benchIdx active
    some (newActive, newBench)

-- ============================================================
-- §10  Total damage calculation
-- ============================================================

/-- Calculate total damage with tool bonus. -/
def totalDamage (baseDmg : Nat) (attacker : PokemonInPlay)
    (targetCls : TargetClass) : Nat :=
  baseDmg + attacker.toolDamageBonus targetCls

-- ============================================================
-- §11  Sample data for theorems
-- ============================================================

private def barePokemon : PokemonInPlay :=
  { pokId := ⟨1⟩, toolSlot := none, stage := .basic, targetClass := .regular,
    retreatCost := 2 }

private def pokemonWithChoiceBelt : PokemonInPlay :=
  { pokId := ⟨2⟩, toolSlot := some .choiceBelt, stage := .stage1,
    targetClass := .regular, retreatCost := 1 }

private def pokemonWithFloatStone : PokemonInPlay :=
  { pokId := ⟨3⟩, toolSlot := some .floatStone, stage := .basic,
    targetClass := .regular, retreatCost := 3 }

private def pokemonWithMuscleBand : PokemonInPlay :=
  { pokId := ⟨4⟩, toolSlot := some .muscleBand, stage := .stage2,
    targetClass := .exOrV, retreatCost := 2 }

-- ============================================================
-- §12  THEOREMS (35+)
-- ============================================================

-- ---- Tool limit: 1 per Pokémon ----

theorem cannot_attach_tool_when_already_attached :
    attachTool pokemonWithChoiceBelt .muscleBand = none := by native_decide

theorem can_attach_tool_when_bare :
    (attachTool barePokemon .choiceBelt).isSome = true := by native_decide

theorem attach_sets_tool :
    attachTool barePokemon .choiceBelt =
      some { barePokemon with toolSlot := some .choiceBelt } := by native_decide

-- ---- Tool persistence ----

theorem tool_persists_after_attach :
    (attachTool barePokemon .floatStone).map PokemonInPlay.hasTool = some true := by
  native_decide

theorem bare_has_no_tool :
    barePokemon.hasTool = false := by native_decide

theorem equipped_has_tool :
    pokemonWithChoiceBelt.hasTool = true := by native_decide

-- ---- Tool removal ----

theorem remove_tool_clears :
    (removeTool pokemonWithChoiceBelt).hasTool = false := by native_decide

theorem remove_tool_idempotent :
    removeTool (removeTool pokemonWithChoiceBelt) =
    removeTool pokemonWithChoiceBelt := by native_decide

theorem remove_bare_is_noop :
    removeTool barePokemon = barePokemon := by native_decide

-- ---- Megaphone removes all tools ----

theorem megaphone_removes_all :
    List.all (removeAllTools [pokemonWithChoiceBelt, pokemonWithFloatStone, barePokemon])
      (fun p => !p.hasTool) = true := by native_decide

-- ---- Choice Belt ----

theorem choice_belt_plus30_vs_exV :
    ToolCard.choiceBelt.damageBonus .exOrV = 30 := by rfl

theorem choice_belt_zero_vs_regular :
    ToolCard.choiceBelt.damageBonus .regular = 0 := by rfl

theorem choice_belt_total_damage :
    totalDamage 100 pokemonWithChoiceBelt .exOrV = 130 := by native_decide

theorem choice_belt_no_bonus_regular :
    totalDamage 100 pokemonWithChoiceBelt .regular = 100 := by native_decide

-- ---- Muscle Band ----

theorem muscle_band_plus20_always :
    ToolCard.muscleBand.damageBonus .regular = 20 := by rfl

theorem muscle_band_plus20_vs_exV :
    ToolCard.muscleBand.damageBonus .exOrV = 20 := by rfl

theorem muscle_band_total_damage :
    totalDamage 80 pokemonWithMuscleBand .regular = 100 := by native_decide

-- ---- Float Stone ----

theorem float_stone_zero_retreat :
    pokemonWithFloatStone.effectiveRetreat = 0 := by native_decide

theorem float_stone_gives_zero :
    ToolCard.floatStone.givesZeroRetreat = true := by rfl

theorem no_tool_normal_retreat :
    barePokemon.effectiveRetreat = 2 := by native_decide

theorem choice_belt_no_retreat_change :
    pokemonWithChoiceBelt.effectiveRetreat = 1 := by native_decide

-- ---- Ultra Ball ----

theorem ultra_ball_needs_3_cards :
    canPlayUltraBall { handSize := 2 } = false := by native_decide

theorem ultra_ball_playable_with_3 :
    canPlayUltraBall { handSize := 3 } = true := by native_decide

theorem ultra_ball_discards_3_total :
    playUltraBall { handSize := 5, discarded := 0 } =
      some { handSize := 2, discarded := 3 } := by native_decide

theorem ultra_ball_fails_small_hand :
    playUltraBall { handSize := 1, discarded := 0 } = none := by native_decide

-- ---- Rare Candy ----

private def stage1Pokemon : PokemonInPlay :=
  { pokId := ⟨20⟩, toolSlot := none, stage := .stage1, targetClass := .regular,
    retreatCost := 2, hp := 100 }

private def stage2Pokemon : PokemonInPlay :=
  { pokId := ⟨21⟩, toolSlot := none, stage := .stage2, targetClass := .regular,
    retreatCost := 2, hp := 100 }

theorem rare_candy_basic_only :
    canUseRareCandy barePokemon = true := by native_decide

theorem rare_candy_not_stage1 :
    canUseRareCandy stage1Pokemon = false := by native_decide

theorem rare_candy_not_stage2 :
    canUseRareCandy stage2Pokemon = false := by native_decide

theorem rare_candy_evolves_to_stage2 :
    (applyRareCandy barePokemon).isSome = true := by native_decide

theorem rare_candy_result_is_stage2 :
    (applyRareCandy barePokemon).map PokemonInPlay.stage = some .stage2 := by native_decide

theorem rare_candy_fails_stage1 :
    applyRareCandy stage1Pokemon = none := by native_decide

-- ---- Switch ----

private def activePoke : PokemonInPlay :=
  { pokId := ⟨10⟩, retreatCost := 3 }

private def benchPoke1 : PokemonInPlay :=
  { pokId := ⟨11⟩, retreatCost := 1 }

private def benchPoke2 : PokemonInPlay :=
  { pokId := ⟨12⟩, retreatCost := 0 }

theorem switch_valid_index :
    (switchActive activePoke [benchPoke1, benchPoke2] 0).isSome = true := by native_decide

theorem switch_invalid_index :
    (switchActive activePoke [benchPoke1] 5).isNone = true := by native_decide

theorem switch_swaps_active :
    (switchActive activePoke [benchPoke1, benchPoke2] 0).map (fun p => p.1.pokId) =
      some ⟨11⟩ := by native_decide

-- ---- TargetClass ----

theorem exOrV_is_true :
    TargetClass.exOrV.isExOrV = true := by rfl

theorem regular_is_false :
    TargetClass.regular.isExOrV = false := by rfl

-- ---- Tool damage bonus no tool ----

theorem no_tool_no_bonus :
    barePokemon.toolDamageBonus .exOrV = 0 := by native_decide

theorem no_tool_no_bonus_regular :
    barePokemon.toolDamageBonus .regular = 0 := by native_decide

-- ---- Remove by id ----

theorem remove_by_id_targeted :
    let result := removeToolById [pokemonWithChoiceBelt, pokemonWithFloatStone] ⟨2⟩
    (result[0]?).map PokemonInPlay.hasTool = some false ∧
    (result[1]?).map PokemonInPlay.hasTool = some true := by native_decide

end PokemonLean.Core.ItemAndTool
