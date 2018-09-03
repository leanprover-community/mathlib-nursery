
## The serial type class

For a variable `x: α` with the instance `[serial α]`, one can use
`serialize x : list unsigned` and then `deserialize α : list unsigned
→ option α`. `serial.correctness` guarantees the validity of the
translations.

When defining our own data types, in many cases, `serial` and its
proof of correctness can be derived automatically:

```lean
@[derive [serial, decidable_eq]]
inductive tree (α : Type)
| leaf {} : tree
| node2 : α → tree → tree → tree
| node3 : α → tree → tree → tree → tree
```

On a given tree, one can then observe the following:

```lean
def x := node2 2 (node3 77777777777777 leaf leaf (node2 1 leaf leaf)) leaf

#eval serialize x
-- [17, 1, 5, 2, 430029026, 72437, 0, 0, 1, 3, 0, 0, 0]
#eval deserialize (tree ℕ) [17, 1, 5, 2, 430029026, 72437, 0, 0, 1, 3, 0, 0, 0]
-- (some (node2 2 (node3 77777777777777 leaf leaf (node2 1 leaf leaf)) leaf))
```

One can notice in the above example that the number `77777777777777`
cannot be represented on the 32 bits of the unsigned. `serial`
automatically uses as many 32 bits words as necessary.

We can let Lean test that this is correct:

```lean
#eval (deserialize _ (serialize x) = some x : bool)
-- tt
```

or we can prove it:

```lean
example : deserialize _ (serialize x) = some x :=
by rw deserialize_serialize
```

The derivation of serialization code also works if the data types have
dependent types and even with decidable proposition:

```lean
@[derive serial]
structure my_struct :=
(x : ℕ)
(xs : list ℕ)
(bounded : xs.length ≤ x)
```

## Building your own serializer

It some cases, it may be necessary to specify a serializer by
hand. The applicative functor `serializer` exists for that purpose. It
encapsulates both the serializer and deserializer together. Let us
consider the following example, a `point` data type:

```lean
structure point :=
(x y z : ℕ)
```

A simple serializer / deserializer pair can be specified as `point.mk
<$> ser_field point.x <*> ser_field point.y <*> ser_field point.z`. It
creates a value of type `serializer point point`. The first type
parameter stands for the input of the serializer and the second stands
for the output of the deserializer. They are separate because
`ser_field point.x : serializer point ℕ` uses the `point.x` selector
on the `point` input to serialize `ℕ`. The deserializer return `ℕ`
which is given to `point.mk`. A complete `serial` instance with its
proof of correctness can be created as:

```lean
instance : serial point :=
by mk_serializer point.mk <$> ser_field point.x <*> ser_field point.y <*> ser_field point.z
```

If necessary, the proof of correctness can be written by the user
with:

```lean
instance : serial point :=
serial.of_serializer (point.mk <$> ser_field point.x <*> ser_field point.y <*> ser_field point.z)
begin
  ...
end
```
