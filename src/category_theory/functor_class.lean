import category_theory.category
import category_theory.functor

universes v v' u u' -- important order for conciseness

namespace category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
variables {D : Type u'} [𝒟 : category.{u' v'} D]
include 𝒞 𝒟

class is_functor (F : C → D) :=
(map : Π {x y : C}, (x ⟶ y) → (F x ⟶ F y))
(map_id : ∀ {x : C}, map (𝟙 x) = 𝟙 (F x))
(map_comp : ∀ {x y z : C} (a : x ⟶ y) (b : y ⟶ z), map (a ≫ b) = map a ≫ map b)

namespace functor

variables (F : C ⥤ D)

instance is_functor (F : C ⥤ D) : is_functor.{v v'} (F.obj) :=
{ map := λ x y a, F.map a,
  map_id := λ x, F.map_id x,
  map_comp := λ x y z a, F.map_comp a }

variables {F} {x y : C}

@[simp]
lemma map_functor (a : x ⟶ y) : is_functor.map.{v v'} F.obj a = F.map a := rfl

end functor
namespace is_functor
variables (F : C → D) [FF : is_functor.{v v'} F]
include FF
def bundled : C ⥤ D :=
{ obj := F,
  map := λ x y, is_functor.map F,
  map_id' := λ x, is_functor.map_id F,
  map_comp' := λ x y z, is_functor.map_comp F }

variables {F} {x y : C}

@[simp]
lemma bundled_obj : (bundled F).obj = F := rfl

@[simp]
lemma bundled_map (a : x ⟶ y) : (bundled F).map a = map.{v v'} F a := rfl

attribute [simp] map_id map_comp

end is_functor

end category_theory
