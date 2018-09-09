
instance list.empty.decidable {α} : Π (xs : list α), decidable (xs = [])
| [] := is_true rfl
| (_ :: _) := is_false (by contradiction)

instance list.empty.decidable' {α} : Π (xs : list α), decidable ([] = xs)
| [] := is_true rfl
| (_ :: _) := is_false (by contradiction)
