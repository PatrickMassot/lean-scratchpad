namespace tactic
namespace interactive
open interactive interactive.types

/--
  `choice hyp with g H` takes an hypothesis `hyp` of the form
  `∀ (y : Y), ∃ (x : X), P x y` for some `P : X → Y → Prop` and outputs into
  context a function `g : Y → X` and a proposition `H` stating
  `∀ (y : Y), P (g y) y`. It presumably also works with dependent versions
  (see the actual type of `classical.axiom_of_choice`)
-/
meta def choice (e : parse cases_arg_p) (ids : parse with_ident_list) :=
do cases (e.1,``(classical.axiom_of_choice %%(e.2))) ids

end interactive
end tactic
