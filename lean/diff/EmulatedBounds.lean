import Sonobe.Circuit.EmuArithConcrete

/-!
Differential check against `crates/primitives/src/algebra/field/emulated.rs`: the static limb bounds
of `u + ρ` and `b * ρ + a` (BN254 `Fr` constraint field, `Fq` emulated) as computed by the Lean
model. `lake env lean --run diff/EmulatedBounds.lean` prints the lines that the Rust test
`test_static_bounds_match_lean` compares with `diff/emulated_bounds.txt`.
-/

open Sonobe.Gadget

def fq : ℕ := 21888242871839275222246405745257275088696311157297823662689037894645226208583

def fmt (name : String) (sh : ModShape) : String :=
  name ++ " " ++ toString sh.N ++ " " ++
    String.intercalate " " ((List.range sh.N).map fun i =>
      s!"[{(sh.selfB i).lo},{(sh.selfB i).hi}]")

def main : IO Unit := do
  IO.println (fmt "add" (addShape fq))
  IO.println (fmt "mul" (mulShape fq))
