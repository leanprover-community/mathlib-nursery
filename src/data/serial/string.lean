
import data.serial.medium

universes u

namespace string.medium

abbreviation put_m' := medium.put_m'.{u} char
abbreviation put_m  := medium.put_m'.{u} char punit
abbreviation get_m  := medium.get_m.{u} char
export medium (hiding put_m put_m' get_m)

def emit (s : string) : put_m :=
s.to_list.mmap' write_word

def expect_char (c : char) : get_m.{u} punit :=
do ⟨ c' ⟩ ← read_word,
   if c = c' then pure punit.star
             else get_m.fail

def expect (s : string) : get_m.{u} punit :=
punit.star <$ s.to_list.mmap expect_char

protected def to_string_aux : put_m → string → string
| (put_m'.pure x) y := y
| (put_m'.write w f) y := to_string_aux (f punit.star) (y.push w)

instance : has_to_string put_m.{u} :=
⟨ λ x, string.medium.to_string_aux x "" ⟩

end string.medium
