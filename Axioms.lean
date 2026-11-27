import LatticePaths
import Lean

/-!
# Axiom check

`lake env lean Axioms.lean` collects every theorem whose name lies in the `LatticePaths`
namespace (the general results in `LatticePaths.General` and the finite checks in
`LatticePaths.Finite`), including private and auxiliary ones. It fails if any of them depends on
an axiom other than `propext`, `Classical.choice` and `Quot.sound`; this also excludes `sorryAx`
and `Lean.ofReduceBool` (so no `native_decide`). It then prints the axioms of the main results.
-/

open Lean Elab Command

elab "#check_lattice_paths_axioms" : command => do
  let env ← getEnv
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n info =>
    match info with
    | .thmInfo _ => if (`LatticePaths).isPrefixOf (privateToUserName n) then acc.push n else acc
    | _ => acc
  if names.isEmpty then
    throwError "no theorem in the LatticePaths namespace"
  let mut bad : Array MessageData := #[]
  for n in names do
    let axs ← collectAxioms n
    let extra := axs.filter (fun a => !standard.contains a)
    unless extra.isEmpty do
      bad := bad.push m!"{n}: {extra}"
  unless bad.isEmpty do
    throwError m!"theorems with non-standard axioms:\n{MessageData.joinSep bad.toList "\n"}"
  logInfo m!"{names.size} theorems in the LatticePaths namespace checked: each depends at most on propext, Classical.choice and Quot.sound."

#check_lattice_paths_axioms

/-! ## General results -/
#print axioms LatticePaths.ce_cons
#print axioms LatticePaths.ce_self
#print axioms LatticePaths.ce_comm
#print axioms LatticePaths.split_lemma
#print axioms LatticePaths.admissible_G
#print axioms LatticePaths.norm_le_G
#print axioms LatticePaths.shankar_inequality
#print axioms LatticePaths.even_family_card_sq_le
#print axioms LatticePaths.even_family_square
