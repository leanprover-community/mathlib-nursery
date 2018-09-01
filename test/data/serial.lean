
import data.serial

open serial serializer

structure point :=
(x y : unsigned)

instance : serial point :=
of_serializer (point.mk <$> ser_field point.x <*> ser_field point.y)
begin
  intro,
  apply there_and_back_again_seq,
  apply there_and_back_again_map,
  cases w, refl
end

@[derive serial]
inductive my_sum
| first : my_sum
| second : ℕ → my_sum
| third (n : ℕ) (xs : list ℕ) : n ≤ xs.length → my_sum

@[derive serial]
structure my_struct :=
(x : ℕ)
(xs : list ℕ)
(bounded : xs.length ≤ x)

@[derive [serial, decidable_eq]]
inductive tree (α : Type)
| leaf {} : tree
| node2 : α → tree → tree → tree
| node3 : α → tree → tree → tree → tree

open tree

meta def tree.repr {α} [has_repr α] : tree α → string
| leaf := "leaf"
| (node2 x t₀ t₁) := to_string $ format!"(node2 {repr x} {tree.repr t₀} {tree.repr t₁})"
| (node3 x t₀ t₁ t₂) := to_string $ format!"(node3 {repr x} {tree.repr t₀} {tree.repr t₁} {tree.repr t₂})"

meta instance {α} [has_repr α] : has_repr (tree α) := ⟨ tree.repr ⟩

def x := node2 2 (node3 77777777777777 leaf leaf (node2 1 leaf leaf)) leaf

#eval serialize x
-- [17, 1, 5, 2, 430029026, 72437, 0, 0, 1, 3, 0, 0, 0]
#eval deserialize (tree ℕ) [17, 1, 5, 2, 430029026, 72437, 0, 0, 1, 3, 0, 0, 0]
-- (some (node2 2 (node3 77777777777777 leaf leaf (node2 1 leaf leaf)) leaf))
#eval (deserialize _ (serialize x) = some x : bool)
-- tt

example (x : tree ℕ) : deserialize _ (serialize x) = some x :=
by { dsimp [serialize,deserialize],
     rw [eval_eval,serial.correctness],
     refl }
