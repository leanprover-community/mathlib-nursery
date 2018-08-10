
import category.liftable

@[reducible]
def {u} m := state_t (ulift.{u} ℤ) (reader (ulift.{u} ℕ))

def add : m ℤ :=
do ⟨x⟩ ← get,
   ⟨y⟩ ← read,
   return $ x+y

open liftable

def my_prog : m (Σ t : Type, t) :=
do ⟨ x ⟩ ← up' add,
   pure ⟨ℤ,x⟩

#check add
-- add : m.{0} ℤ
#check my_prog
-- my_prog : m.{1} (Σ (t : Type), t)
