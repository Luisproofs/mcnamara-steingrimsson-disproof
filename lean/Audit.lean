import PatternInterval
import Lean.Elab.Command
import Lean.Util.CollectAxioms

#check PatternInterval.consecutive_rank_sizes
#check PatternInterval.disproof
#print axioms PatternInterval.consecutive_rank_sizes
#print axioms PatternInterval.disproof

open Lean in
run_cmd do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for result in [``PatternInterval.consecutive_rank_sizes, ``PatternInterval.disproof] do
    for ax in ← collectAxioms result do
      unless standard.contains ax do
        throwError "{result} depends on unexpected axiom {ax}"
