
import data.serial.string
import system.io

universes u

namespace json

inductive value
| object : unit → list (string × value) → value
| number : ℤ → value
| array : unit → list value → value
| bool : bool → value
| string : string → value
| nil : value
-- with object : Type
-- | fields : list (string × value) → object

open value (hiding object bool string)

def object := list (string × value)

def is_atom : value → bool
| (number n) := tt
| (value.bool b) := tt
| (value.string s) := tt
| value.nil := tt
| _ := ff

def encode_line : value → string
| (number n) := to_string n
| (value.bool n) := to_string n
| (value.string n) := to_string n
| nil := "nil"
| (value.object _ _) := "<object>"
| (value.array _ _) := "<array>"

end json

namespace yaml

open string.medium json

@[reducible] def writer := reader_t ℕ put_m'

def newline : writer unit :=
⟨ λ n, emit $ "\n" ++ (list.repeat ' ' n).as_string ⟩

def bump {α} (tac : writer α) : writer α :=
⟨ λ n, tac.run (n+2) ⟩

mutual def encode_aux, encode_obj, encode_array
with encode_aux : value → writer unit
| (value.string v) := monad_lift $ emit $ "\"" ++ v ++ "\""
| (value.bool v) := monad_lift $ emit $ to_string v
| (value.number v) := monad_lift $ emit $ to_string v
| value.nil := monad_lift $ emit "nil"
| (value.object _ o) := encode_obj o
| (value.array _ ar) := encode_array ar
with encode_obj : list (string × value) → writer unit
| [] := monad_lift $ emit "[]"
| ((f,v) :: vs) :=
  do monad_lift $ emit (f ++ ": "),
     bump $ do {
       when (¬ is_atom v) newline,
       encode_aux v },
     when (¬ vs.empty) $ do
       newline,
       encode_obj vs
with encode_array : list value → writer unit
| [] := monad_lift $ emit "[]"
| (v :: vs) :=
  do monad_lift $ emit "- ",
     bump $ encode_aux v,
     when (¬ vs.empty) $ do
       newline,
       encode_array vs

def encode (v : value) : put_m :=
(encode_aux v).run 0

#eval do io.put_str_ln "",
         io.put_str_ln $ to_string $ encode (value.object ()
           [ ("a",value.number 3),
             ("boo",value.array () [ value.number 3,
                                     value.array () [ value.number 3, value.number 7, value.string "ho" ] ,
                                     value.string "abc" ]) ])

end yaml
