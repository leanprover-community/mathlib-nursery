
import data.serial.string
import tactic.linarith
import category.monad_trans
import data.list.nursery
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

@[reducible] def object := list (string × value)

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

namespace syntax

@[derive decidable_eq]
inductive token
| open_curly  | close_curly
| open_square | close_square
| colon | comma | nil | bool (b : bool)
| number (n : ℤ) | string (s : string)

abbreviation put_m' := medium.put_m'.{u} token
abbreviation put_m  := medium.put_m'.{u} token punit
abbreviation get_m  := medium.get_m.{u} token
export medium (hiding put_m put_m' get_m)

namespace put_m'
export medium.put_m'
end put_m'

namespace get_m
export medium.get_m
end get_m

export token (hiding number string bool)

mutual def encode_val, encode_obj, encode_array
with encode_val : value → put_m
| (value.string s) := write_word $ token.string s
| (value.number n) := write_word $ token.number n
| (value.bool b) := write_word $ token.bool b
| (value.nil) := write_word $ token.nil
| (value.object _ []) :=
  write_word open_curly >> write_word close_curly
| (value.object _ ((fn,v)::vs)) :=
  do write_word open_curly,
     write_word (token.string fn),
     write_word colon,
     encode_obj v vs,
     write_word close_curly
| (value.array _ obj) :=
  write_word open_square >> encode_array obj >> write_word close_square
with encode_obj : value → list (string × value) → put_m
| v [] := encode_val v
| v ((fn,v') :: vs) :=
do encode_val v,
   write_word comma,
   write_word (token.string fn),
   write_word colon,
   encode_obj v' vs
with encode_array : list value → put_m
| [] := pure ()
| (v :: vs) :=
do encode_val v,
   when (¬ vs = []) $ do
     write_word comma,
     encode_array vs

inductive partial_val
| array (ar : list value)
| object (obj : list (string × value)) (field : string)

def parser_state := list partial_val

open ulift

def push : list partial_val → value → get_m ( value ⊕ parser_state )
| [] v := pure (sum.inl v)
| (partial_val.array ar :: vs) v :=
  do t ← read_word,
     if down t = comma then pure (sum.inr (partial_val.array (v :: ar) :: vs))
     else if down t = close_square then push vs (value.array () (list.reverse $ v :: ar))
     else failure
| (partial_val.object ar fn :: vs) v :=
  do t ← read_word,
     if down t = comma then do
       ⟨token.string fn'⟩ ← read_word | failure,
       ⟨colon⟩ ← read_word | failure,
       pure (sum.inr (partial_val.object ((fn,v) :: ar) fn' :: vs))
     else if down t = close_curly then push vs (value.object () (list.reverse $ (fn,v) :: ar))
     else failure

def parser_step : parser_state → token → get_m ( value ⊕ parser_state )
| vs nil := push vs value.nil
| vs open_curly :=
  do t ← read_word,
     match down t with
     | (token.string fn) :=
       expect_word colon >>
       pure (sum.inr (partial_val.object [] fn :: vs))
     | close_curly := push vs (value.object () [])
     | _ := failure
     end
| vs open_square := pure (sum.inr (partial_val.array [] :: vs))
| vs (token.bool b) := push vs (value.bool b)
| vs (token.number n) := push vs (value.number n)
| vs (token.string str) := push vs (value.string str)
| vs close_square :=
  match vs with
  | (partial_val.array vs' :: vs) := push vs $ value.array () vs'.reverse
  | _ := failure
  end
| _ _ := failure


def decode_val : get_m value :=
get_m.loop parser_step pure []

def encoding_correctness_val (m : ℕ) :=
(∀ (v : value) (vs : list partial_val) (x : punit → put_m), sizeof v ≤ m →
   get_m.loop parser_step pure vs -<< (encode_val v >>= x) =
   (push vs v >>= get_m.loop.rest parser_step pure) -<< x punit.star)

def encoding_correctness_obj (m : ℕ) :=
(∀ (fn : string) (v : value) (obj obj' : object)
   (vs : list partial_val) (x : punit → put_m),
   sizeof obj' ≤ m → sizeof v < m →
get_m.loop parser_step pure (partial_val.object obj fn :: vs) -<<
  (encode_obj v obj' >>= λ _, write_word close_curly >>= x) =
  (push vs (value.object punit.star (obj.reverse ++ (fn,v) :: obj')) >>= get_m.loop.rest parser_step pure) -<< x punit.star)

def encoding_correctness_array (m : ℕ) :=
(∀ (v v' : list value)
   (vs : list partial_val) (x : punit → put_m), sizeof v' ≤ m →
get_m.loop parser_step pure (partial_val.array v :: vs) -<<
      (encode_array v' >>= λ (x_1 : punit), write_word close_square >>= x) =
    (push vs (value.array punit.star (v.reverse ++ v')) >>= get_m.loop.rest parser_step pure) -<< x punit.star)

section correctness

variables n : ℕ
variables ih_val : ∀ (x : ℕ), x < n → encoding_correctness_val x
variables ih_obj : ∀ (x : ℕ), x < n → encoding_correctness_obj x
variables ih_ar : ∀ (x : ℕ), x < n → encoding_correctness_array x

include ih_val ih_obj ih_ar

lemma encode_val_ind_step : encoding_correctness_val n :=
begin
  dsimp [encoding_correctness_val], introv h,
  { cases v with v fs _ v fs; casesm* unit;
          try { simp [encode_val,parser_step] },
    { rcases fs with _ | ⟨ ⟨ fn,v ⟩, vs ⟩,
      { simp [encode_val,parser_step] with functor_norm },
      { simp [encode_val,parser_step,expect_word] with functor_norm,
        apply ih_obj (1 + sizeof v + sizeof vs),
        apply lt_of_lt_of_le _ h,
        well_founded_tactics.default_dec_tac,
        apply le_of_lt, well_founded_tactics.default_dec_tac,
        well_founded_tactics.default_dec_tac }, },
    { simp [encode_val,parser_step] with functor_norm,
      rw ih_ar; try { refl },
      apply lt_of_lt_of_le _ h,
      simp [sizeof,has_sizeof.sizeof,value.sizeof,punit.sizeof,list.sizeof] } },
end

lemma encode_obj_ind_step : encoding_correctness_obj n :=
begin
  dsimp [encoding_correctness_obj], introv h h',
  { rcases obj' with _ | ⟨ ⟨ fn', v' ⟩, obj' ⟩,
    { simp [encode_obj], rw ih_val; try { assumption <|> refl },
      simp [push] with functor_norm, },
    { simp [encode_obj] with functor_norm, rw ih_val (sizeof v),
      simp [push] with functor_norm, rw ih_obj (1 + sizeof v' + sizeof obj'),
      congr' 4, simp,
      apply lt_of_lt_of_le _ h,
      all_goals { try { well_founded_tactics.default_dec_tac } },
      apply le_of_lt, well_founded_tactics.default_dec_tac,
      refl } },
end

lemma encode_array_ind_step : encoding_correctness_array n :=
begin
  dsimp [encoding_correctness_array], introv h,
  { cases v' with v' vs'; simp [encode_array,parser_step] with functor_norm,
    rw ih_val (sizeof v' ),
    by_cases h' : (vs' = []),
    { subst vs', simp [when,list.empty,push] with functor_norm },
    { simp [when,*,push] with functor_norm,
      rw ih_ar (sizeof vs'), simp, apply lt_of_lt_of_le _ h,
      well_founded_tactics.default_dec_tac, refl },
    apply lt_of_lt_of_le _ h,
    well_founded_tactics.default_dec_tac,
    refl },
end

end correctness

lemma encoding_correctness' (m : ℕ) :
    encoding_correctness_val m ∧
    encoding_correctness_obj m ∧
    encoding_correctness_array m :=
begin
  induction m using nat.strong_induction_on with n ih,
  simp [imp_and_distrib,forall_and_distrib,push] at ih,
  rcases ih with ⟨ ih_val, ih_obj, ih_ar ⟩,
  repeat { split },
  apply encode_val_ind_step; assumption,
  apply encode_obj_ind_step; assumption,
  apply encode_array_ind_step; assumption,
end

lemma encoding_correctness (v : value) :
  decode_val -<< encode_val v = some v :=
begin
  have := (encoding_correctness' (sizeof v)).1 v [] pure _,
  simp with functor_norm at this,
  simp [decode_val,this,push], refl, refl
end

def value.repr : token → string
| (token.number n) := to_string n
| (token.string s) := "\"" ++ s ++ "\""
| (token.bool b) := to_string b
| nil := "nil"
| open_curly := "'{'"
| close_curly := "'}'"
| open_square := "'['"
| close_square := "']'"
| colon := "':'"
| comma := "','"

instance : has_repr token := ⟨ value.repr ⟩

#eval (encode_val (value.object ()
           [ ("a",value.number 3),
             ("boo",value.array () [ value.number 3,
                                     value.array () [ value.number 3, value.number 7, value.string "ho" ] ,
                                     value.string "abc" ]) ])).eval


end syntax
end json

-- namespace yaml

-- open string.medium json

-- @[reducible] def writer := reader_t ℕ put_m'

-- def newline : writer unit :=
-- ⟨ λ n, emit $ "\n" ++ (list.repeat ' ' n).as_string ⟩

-- def bump {α} (tac : writer α) : writer α :=
-- ⟨ λ n, tac.run (n+2) ⟩

-- mutual def encode_aux, encode_obj, encode_array
-- with encode_aux : value → writer unit
-- | (value.string v) := monad_lift $ emit $ "\"" ++ v ++ "\""
-- | (value.bool v) := monad_lift $ emit $ to_string v
-- | (value.number v) := monad_lift $ emit $ to_string v
-- | value.nil := monad_lift $ emit "nil"
-- | (value.object _ o) := encode_obj o
-- | (value.array _ ar) := encode_array ar
-- with encode_obj : list (string × value) → writer unit
-- | [] := monad_lift $ emit "[]"
-- | ((f,v) :: vs) :=
--   do monad_lift $ emit (f ++ ": "),
--      bump $ do {
--        when (¬ is_atom v) newline,
--        encode_aux v },
--      when (¬ vs.empty) $ do
--        newline,
--        encode_obj vs
-- with encode_array : list value → writer unit
-- | [] := monad_lift $ emit "[]"
-- | (v :: vs) :=
--   do monad_lift $ emit "- ",
--      bump $ encode_aux v,
--      when (¬ vs.empty) $ do
--        newline,
--        encode_array vs

-- def encode (v : value) : put_m :=
-- (encode_aux v).run 0

-- def select_aux {α} (f : char → list (bool × reader α)) (c : char) : reader α :=
-- (prod.snd <$> list.find (λ x, prod.fst x = tt) (f c)).get_or_else failure

-- def select {α} (f : char → list (bool × reader α)) : reader α :=
-- peek >>= select_aux f

-- def try_char (p : char → Prop) [decidable_pred p] : reader (option char) :=
-- do c ← read_char,
--    if p c then pure c
--           else unread c >> pure none

-- def many_loop (p : char → Prop) [decidable_pred p] : list char → char → get_m ((list char × option char) ⊕ list char)
-- | s c :=
-- if p c then pure (sum.inr $ c :: s)
--        else pure (sum.inl (s.reverse,some c))

-- def many (p : char → Prop) [decidable_pred p] : reader (list char) :=
-- ⟨ λ n, ⟨ λ s : option char,
-- do s' ← match s with
--         | none := pure $ sum.inr []
--         | (some s) := many_loop p [] s
--         end,
--    match s' with
--    | (sum.inl x) := pure x
--    | (sum.inr x) := get_m.loop (many_loop p) pure x
--    end ⟩ ⟩

-- def parse_nat : reader ℕ :=
-- do c ← read_char,
--    guard c.is_digit,
--    cs ← many char.is_digit,
--    pure $ list.foldl (λ x (c : char), 10 * x + c.val - '0'.val) 0 (c :: cs)

-- def parse_int : reader ℤ :=
-- do x ← try_char (= '-'),
--    n ← parse_nat,
--    pure $ if x.is_some then - ↑n
--                        else n

-- def parse_value : reader value :=
-- value.number <$> parse_int <* expect_char '\n'

-- -- def read_write (i n : ℕ) :
-- --   parse_value.run i -<< encode (value.number n) = some (value.number n) :=
-- -- begin
-- --   rw [encode,encode_aux,emit],
-- --   induction n using nat.strong_induction_on,
-- --   simp [to_string,has_to_string.to_string],
-- --   unfold_coes, simp [int.repr],
-- --   -- induction h : (string.to_list (to_string ↑n)) generalizing n;
-- --     -- rw [mmap'],
-- --   -- { admit },
-- --   -- { simp [monad_lift_and_then writer,parse_value,parse_int] with functor_norm, }
-- -- end


-- #eval do io.put_str_ln "",
--          io.put_str_ln $ to_string $ encode (value.object ()
--            [ ("a",value.number 3),
--              ("boo",value.array () [ value.number 3,
--                                      value.array () [ value.number 3, value.number 7, value.string "ho" ] ,
--                                      value.string "abc" ]) ])

-- end yaml
