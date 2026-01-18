import PokemonLean

open PokemonLean PokemonLean.Solver

def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════╗"
  IO.println "║   PokemonLean - Verified TCG Damage Calculator       ║"
  IO.println "╚══════════════════════════════════════════════════════╝"
  IO.println ""
  
  -- Demo: Charmander vs Pikachu
  IO.println "Battle Simulation: Charmander (🔥) vs Pikachu (⚡)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  
  let pikachu : PokemonInPlay := { card := samplePikachu, damage := 40, status := none }
  IO.println s!"Pikachu: {samplePikachu.hp} HP, {40} damage taken"
  IO.println s!"Charmander: {sampleCharmander.hp} HP, Ember attack (30 base)"
  
  match solve sampleCharmander pikachu with
  | none => IO.println "No valid attack found"
  | some result =>
    IO.println ""
    IO.println "Solver Result (Formally Verified):"
    IO.println s!"  Best Attack Index: {result.attackIndex}"
    IO.println s!"  Expected Damage: {result.expectedDamage}"
    IO.println s!"  Is Knockout: {result.isLethal}"
  
  IO.println ""
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  IO.println "Battle Simulation: Squirtle (💧) vs Charmander (🔥)"
  IO.println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  
  let charmander : PokemonInPlay := { card := sampleCharmander, damage := 0, status := none }
  IO.println s!"Charmander: {sampleCharmander.hp} HP, weak to Water"
  IO.println s!"Squirtle: {sampleSquirtle.hp} HP, Water Gun (20 base)"
  
  match solve sampleSquirtle charmander with
  | none => IO.println "No valid attack found"
  | some result =>
    IO.println ""
    IO.println "Solver Result (Formally Verified):"
    IO.println s!"  Best Attack Index: {result.attackIndex}"
    IO.println s!"  Expected Damage: {result.expectedDamage} (2x weakness!)"
    IO.println s!"  Is Knockout: {result.isLethal}"
  
  IO.println ""
  IO.println "✓ All calculations verified by Lean 4 type system"
