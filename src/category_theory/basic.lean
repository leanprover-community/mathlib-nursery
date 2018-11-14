
import category_theory.isomorphism
       category_theory.natural_isomorphism
       category_theory.functor_category
       category_theory.products

universes u v

namespace category_theory
namespace nat_iso

variables {C₀ C₁ C₂ C₃ : Type u}
          [category.{u v} C₀]
          [category.{u v} C₁]
          [category.{u v} C₂]
          [category.{u v} C₃]

variables {D₀ D₁ D₂ D₃ : Type u}
          [category.{u v} D₀]
          [category.{u v} D₁]
          [category.{u v} D₂]
          [category.{u v} D₃]

variables {F₀ F₁ : C₀ ⥤ D₀}
          {F₂ F₃ : C₂ ⥤ D₂}
          (h₀ : F₀ ≅ F₁) (h₁ : F₂ ≅ F₃)
def prod : functor.prod F₀ F₂ ≅ functor.prod F₁ F₃ :=
{ hom := { app := λ X, (nat_trans.app h₀.hom _,nat_trans.app h₁.hom _),
           naturality' := by { obviously, repeat { apply nat_trans.naturality' }, } },
  inv := { app := λ X, (nat_trans.app h₀.inv _,nat_trans.app h₁.inv _),
           naturality' := by { obviously, repeat { apply nat_trans.naturality' }, } },
  hom_inv_id' := by { obviously, all_goals { rw [← app_hom,← app_inv,iso.hom_inv_id], }, },
  inv_hom_id' := by { obviously, all_goals { rw [← app_hom,← app_inv,iso.inv_hom_id], }, }, }

end nat_iso

-- def swap {C₀} [category.{u v} C₀] (X Y : C₀) :

end category_theory
