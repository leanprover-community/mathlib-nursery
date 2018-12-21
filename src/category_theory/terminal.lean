
import category_theory.category
import category_theory.products
import category_theory.opposites
import category_theory.functor_class
import tactic.squeeze

universes u v

namespace category_theory
variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

class has_terminal :=
(term : C)
(intro : Π {x}, x ⟶ term)

class has_initial :=
(init : C)
(elim : Π {x}, init ⟶ x)

open has_terminal has_initial

instance [has_terminal.{u v} C] : has_initial.{u v} (Cᵒᵖ) :=
{ init := (term.{u v} C : C),
  elim := λ x, intro.{u v} C }

instance [has_initial.{u v} C] : has_terminal.{u v} (Cᵒᵖ) :=
{ term := (init.{u v} C : C),
  intro := λ x, elim C }

def with_terminal := option C

inductive with_terminal_hom : with_terminal C → with_terminal C → Type.{max u v}
| hom {x y : C} : (x ⟶ y) → with_terminal_hom (some x) (some y)
| term (x : option C) : with_terminal_hom x none

def with_terminal_hom.comp : Π (x y z : with_terminal C), with_terminal_hom C x y → with_terminal_hom C y z → with_terminal_hom C x z
| x y z a (with_terminal_hom.hom b) :=
match x, a with
| _, (with_terminal_hom.hom a) := with_terminal_hom.hom $ a ≫ b
end
| x y z _ (with_terminal_hom.term _) := with_terminal_hom.term _

instance with_terminal.category : category (with_terminal C) :=
{ hom := with_terminal_hom C,
  id := λ x, option.rec_on x (with_terminal_hom.term none) (λ x, with_terminal_hom.hom $ 𝟙 _),
  comp := with_terminal_hom.comp _,
  id_comp' := by { introv, cases f; simp only [with_terminal_hom.comp,category.id_comp], },
  comp_id' := by { introv, cases f; simp only [with_terminal_hom.comp,category.comp_id], },
  assoc' := by { introv, cases h; simp only [with_terminal_hom.comp,category.id_comp],
                 cases g; cases f; simp only [with_terminal_hom.comp,category.id_comp,category.assoc], } }

instance with_terminal.has_terminal : has_terminal.{u max u v} (with_terminal C) :=
{ term := none,
  intro := with_terminal_hom.term }

def with_initial := option C

inductive with_initial_hom : with_terminal C → with_terminal C → Type.{max u v}
| hom {x y : C} : (x ⟶ y) → with_initial_hom (some x) (some y)
| init (y : option C) : with_initial_hom none y

def with_initial_hom.comp : Π (x y z : with_initial C), with_initial_hom C x y → with_initial_hom C y z → with_initial_hom C x z
| x y z (with_initial_hom.hom a) b :=
match z, b with
| _, (with_initial_hom.hom b) := with_initial_hom.hom $ a ≫ b
end
| x y z (with_initial_hom.init _) _ := with_initial_hom.init _

instance with_initial.category : category.{u max u v} (with_initial C) :=
{ hom := with_initial_hom C,
  id := λ x, option.rec_on x (with_initial_hom.init none) (λ x, with_initial_hom.hom $ 𝟙 _),
  comp := with_initial_hom.comp _,
  id_comp' := by { introv, cases f; simp only [with_initial_hom.comp,category.id_comp], },
  comp_id' := by { introv, cases f; simp only [with_initial_hom.comp,category.comp_id], },
  assoc' := by { introv, cases f; simp only [with_initial_hom.comp,category.id_comp],
                 cases g; cases h; simp only [with_initial_hom.comp,category.id_comp,category.assoc], } }

instance with_initial.has_initial : has_initial.{u max u v} (with_initial C) :=
{ init := none,
  elim := with_initial_hom.init }

end category_theory
