
import tactic
import tactic.linarith
import tactic.norm_num
import data.sigma.fst
import control.basic

universes u

structure ref (α : Type u) : Type u :=
(addr : ℕ)

def value := Σ α : Type u, α

namespace intl

inductive st (α : Type u) : Type.{u+1}
| pure (x : α) : st
| new_ref {β : Type u} : β → (ref β → st) → st
| read {β : Type u} : ref β → (β → st) → st
| write {β : Type u} : β → ref β → (punit.{u+1} → st) → st

end intl

export intl (st)

namespace st

variables {α β : Type u}
open intl.st (hiding pure)

protected def bind : Π (x : st α) (f : α → st β), st β
| (intl.st.pure x) f := f x
| (new_ref x f) g := new_ref x $ λ r, bind (f r) g
| (read r f) g := read r $ λ v, bind (f v) g
| (write v r f) g := write v r $ λ v, bind (f v) g

def addr : sigma ref → ℕ
| ⟨_,x⟩ := x.addr

instance : monad.{u u+1} st :=
{ pure := @intl.st.pure,
  bind := @st.bind }

instance : is_lawful_monad.{u u+1} st :=
begin
  refine { .. }; intros; try { refl <|> dsimp [(>>=),(<$>)] };
  induction x; simp [(>>=),(<$>),st.bind] with functor_norm;
  ext; simp *,
end

inductive ref_layout : list (sigma ref) → Prop
| nil : ref_layout []
| cons (r : sigma ref) (xs : list (sigma ref)) :
  ¬ addr r ∈ xs.map addr →
  ref_layout xs →
  ref_layout (r :: xs)

inductive mem_safety : list (sigma ref.{u}) → Π {α}, st.{u} α → Prop
| pure (ls) {α} (x : α) : mem_safety ls (pure x)
| new_ref (ls) {α β} (x : α) (f : ref α → st β) :
  (∀ (r : ref α),
    let r' := sigma.mk α r in
    ¬ r' ∈ ls →
    mem_safety (r' :: ls) (f r)) →
  mem_safety ls (new_ref x f)
| read (ls) {β} (r : ref β) {α} (f : β → st α) :
  sigma.mk β r ∈ ls →
  (∀ x, mem_safety ls (f x)) →
  mem_safety ls (read r f)
| write (ls) {β} (r : ref β) (x : β) {α} (f : punit → st α) :
  sigma.mk _ r ∈ ls →
  mem_safety ls (f punit.star) →
  mem_safety ls (write x r f)

lemma mem_safety_bind {ls} {x : st β} {f : β → st α}
  (h₀ : mem_safety ls x)
  (h₁ : ∀ ls' i, ls ⊆ ls' → mem_safety ls' (f i)) :
  mem_safety ls (st.bind x f) :=
begin
  induction h₀ generalizing f; simp only [st.bind,pure],
  { apply h₁, refl },
  { constructor, intros, apply h₀_ih, assumption,
    intros, apply h₁, transitivity ; [skip, exact a_1],
    apply list.subset_cons_of_subset, refl },
  { constructor, assumption, intros, apply h₀_ih _ h₁, },
  { constructor, assumption, apply h₀_ih h₁, },
end

def alloc (α : Type u) (ls : list (sigma ref.{u})) : ref α :=
⟨ ls.length ⟩

structure mem (ls : list (sigma ref.{u})) :=
(vals : array ls.length value.{u})
(valid_ptrs : ∀ x : sigma ref, x ∈ ls → x.2.addr < ls.length)
(well_typed : ∀ (x : sigma ref) (h : x ∈ ls), (vals.read ⟨x.2.addr,valid_ptrs _ h⟩).1 = x.1 )

local notation `♯` := by assumption

lemma same_type_of_same_addr {ls : list (sigma ref)} (m : mem ls) (r₀ ∈ ls) (r₁ ∈ ls)
  (h : r₀.2.addr = r₁.2.addr) :
  r₀.1 = r₁.1 :=
calc  r₀.1
    = (m.vals.read ⟨r₀.2.addr,m.valid_ptrs _ ♯⟩).1 : by rw m.well_typed
... = (m.vals.read ⟨r₁.2.addr,m.valid_ptrs _ ♯⟩).1 : by { casesm* [sigma _,ref _], cases h, refl }
... = r₁.1 : by rw m.well_typed


def mem.read {ls : list (sigma ref.{u})} {α} (r : ref α) (h : sigma.mk α r ∈ ls) (m : mem ls) : α :=
cast (m.well_typed _ h) (m.vals.read ⟨r.addr,m.valid_ptrs _ h⟩).2

def mem.write {ls : list (sigma ref.{u})} {α} (x : α) (r : ref α) (h : sigma.mk _ r ∈ ls) (m : mem ls) : mem ls :=
{ vals := m.vals.write ⟨r.addr,m.valid_ptrs _ h⟩ ⟨α,x⟩,
  well_typed := by { intros,
                     by_cases h' : r.addr = (x_1.snd).addr,
                     { cases r, cases h', rw array.read_write,
                       exact same_type_of_same_addr m _ h _ h_1 h', },
                     { rw array.read_write_of_ne, apply m.well_typed,
                       intro, injection a, contradiction } },
  .. m  }

def mem.alloc {ls : list (sigma ref.{u})} {α} (x : α) (m : mem ls) : mem (⟨α,⟨ls.length⟩⟩ :: ls) :=
{ vals := m.vals.push_back ⟨_,x⟩,
  valid_ptrs := by { rintro _ ⟨_ | _⟩, norm_num, dsimp,
                     transitivity ls.length, apply m.valid_ptrs _ ♯, norm_num },
  well_typed := by { rintros _ ⟨ _ | _ ⟩,
                     { simp [array.read,array.push_back,d_array.read] },
                     have : (x_1.snd).addr ≠ list.length ls,
                     { apply ne_of_lt, apply m.valid_ptrs _ h },
                     { simp [array.read,array.push_back,d_array.read,*],
                       apply m.well_typed _ h, } }
   }

lemma alloc_free {ls : list (sigma ref)} (m : mem ls) : sigma.mk α (alloc α ls) ∉ ls :=
begin
  dsimp [alloc], intro h,
  have := m.valid_ptrs _ h,
  dsimp at this, apply lt_irrefl _ this
end

def mem₀ : mem [] :=
{ vals := array.nil,
  valid_ptrs := by rintro _ ⟨ ⟩,
  well_typed := by rintro _ ⟨ ⟩ }

def run' {α} : Π ls (x : st α), mem ls → mem_safety ls x → α
| ls (intl.st.pure a) m _ := a
| ls (@new_ref _ α x f) m h :=
  run' (sigma.mk _ _ :: ls) (f _) (m.alloc x)
    (by cases h; apply h_a _ (alloc_free m))
| ls (@read _ α r f) m h :=
  run' ls (f $ m.read r $ by { cases h, assumption }) ♯
    (by cases h; apply h_a_1)
| ls (@write _ α x r f) m h :=
  run' ls (f ()) (m.write x r $ by { cases h, assumption })
  $ by { cases h, assumption }

def run {α} (x : st α) (h : mem_safety [] x) : α :=
run' [] x mem₀ h

run_cmd mk_simp_attr `st

attribute [st] st.bind

@[st]
def new_ref (x : α) : st (ref α) :=
intl.st.new_ref x pure

@[st]
def write (r : ref α) (x : α) : st punit :=
intl.st.write x r pure

@[st]
def read (r : ref α) : st α :=
intl.st.read r pure

def ex (x x' : α) : st (α × α) :=
do r ← new_ref x,
   y ← read r,
   write r x',
   prod.mk y <$> read r

lemma ex_safe : ∀ x x' : α, mem_safety [] (ex x x') :=
begin
  intros, simp [ex,(>>=),(<$>),pure] with st,
  constructor, intros,
  constructor, simp, intros,
  constructor, simp, intros,
  constructor, simp, intros,
  constructor
end

#eval run (ex 1 3) (ex_safe 1 3)

def swap (r r' : ref α) : st punit :=
do t ← read r >>= new_ref,
   read r' >>= write r,
   read t >>= write r'

lemma swap_safe (ls : list $ sigma ref.{u}) :
  ∀ r r' : ref α, (sigma.mk _ r ∈ ls) → (sigma.mk _ r' ∈ ls) →
    mem_safety ls (swap r r') :=
begin
  intros, simp [swap,(>>=),(<$>),pure] with st,
  constructor, simpa, intros,
  constructor, intros,
  constructor, right, simpa, intros,
  constructor, right, simpa, intros,
  constructor, left, refl, intros,
  constructor, right, simpa, intros,
  constructor
end

def swap_if [decidable_linear_order α] (r r' : ref α) : st punit :=
do x ← read r,
   y ← read r',
   if y < x
     then swap r r'
     else pure punit.star

lemma swap_if_safe [decidable_linear_order α] (ls : list $ sigma ref.{u}) :
  ∀ r r' : ref α, (sigma.mk _ r ∈ ls) → (sigma.mk _ r' ∈ ls) →
    mem_safety ls (swap_if r r') :=
begin
  intros, simp [swap_if,(>>=),(<$>),pure] with st,
  constructor, assumption, intros,
  constructor, assumption, intros,
  split_ifs, apply swap_safe; assumption,
  constructor,
end

def sort_triple [decidable_linear_order α] (x y z : α) : st (α × α × α) :=
do rx ← new_ref x,
   ry ← new_ref y,
   rz ← new_ref z,
   swap_if rx ry,
   swap_if ry rz,
   swap_if rx ry,
   x' ← read rx, y' ← read ry, z' ← read rz,
   pure (x',y',z')

lemma sort_triple_safe [decidable_linear_order α] (ls : list $ sigma ref.{u}) :
  ∀ x y z : α,
    mem_safety ls (sort_triple x y z) :=
begin
  intros, simp [sort_triple,(>>=),(<$>),pure] with st,
  constructor, intros,
  constructor, intros,
  constructor, intros,
  refine mem_safety_bind _ _,
  apply swap_if_safe,
  { simp },
  { simp },
  intros,
  refine mem_safety_bind _ _,
  apply swap_if_safe,
  { apply a_3, simp },
  { apply a_3, simp },
  intros,
  refine mem_safety_bind _ _,
  apply swap_if_safe,
  { apply a_4, apply a_3, simp },
  { apply a_4, apply a_3, simp },
  intros,
  constructor, apply a_5, apply a_4, apply a_3, simp, intros,
  constructor, apply a_5, apply a_4, apply a_3, simp, intros,
  constructor, apply a_5, apply a_4, apply a_3, simp, intros,
  constructor,
end

#eval run (sort_triple 3 7 2) (sort_triple_safe _ _ _ _)

end st
