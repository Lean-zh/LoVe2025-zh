/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe Exercise 11: Denotational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Monotonicity

1.1. Prove the following theorem from the lecture. -/

theorem Monotone_restrict {α β : Type} [PartialOrder α] (f : α → Set (β × β))
      (p : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ p) :=
  sorry

/- 1.2. Prove its cousin. -/

theorem Monotone_comp {α β : Type} [PartialOrder α] (f g : α → Set (β × β))
      (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry


/- ## Question 2: Regular Expressions

__Regular expressions__, or __regexes__, are a highly popular tool for software
development, to analyze textual inputs. Regexes are generated by the following
grammar:

    R  ::=  ∅
         |  ε
         |  a
         |  R ⬝ R
         |  R + R
         |  R*

Informally, the semantics of regular expressions is as follows:

* `∅` accepts nothing;
* `ε` accepts the empty string;
* `a` accepts the atom `a`;
* `R ⬝ R` accepts the concatenation of two regexes;
* `R + R` accepts either of two regexes;
* `R*` accepts arbitrary many repetitions of a regex.

Notice the rough correspondence with a WHILE language:

    `∅` ~ diverging statement (e.g., `while true do skip`)
    `ε` ~ `skip`
    `a` ~ `:=`
    `⬝` ~ `;`
    `+` ~ `if then else`
    `*` ~ `while` loop -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- In this exercise, we explore an alternative semantics of regular
expressions. Namely, we can imagine that the atoms represent binary relations,
instead of letters or symbols. Concatenation corresponds to composition of
relations, and alternation is union. Mathematically, regexes and binary
relations are both instances of Kleene algebras.

2.1. Complete the following translation of regular expressions to relations.

Hint: Exploit the correspondence with the WHILE language. -/

def rel_of_Regex {α : Type} : Regex (Set (α × α)) → Set (α × α)
  | Regex.nothing      => ∅
  | Regex.empty        => Id
  -- enter the missing cases here

/- 2.2. Prove the following recursive equation about your definition. -/

theorem rel_of_Regex_Star {α : Type} (r : Regex (Set (α × α))) :
    rel_of_Regex (Regex.star r) =
    rel_of_Regex (Regex.alt (Regex.concat r (Regex.star r)) Regex.empty) :=
  sorry

end LoVe
