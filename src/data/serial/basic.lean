
import tactic
import tactic.monotonicity
import tactic.norm_num
import category.basic
import category.nursery
import data.serial.medium

universes u v w

def serial_inverse {α : Type u} (encode : α → put_m) (decode : get_m α) : Prop :=
∀ w, decode -<< encode w = pure w

class serial (α : Type u) :=
  (encode : α → put_m.{u})
  (decode : get_m α)
  (correctness : ∀ w, decode -<< encode w = pure w)

class serial1 (f : Type u → Type v) :=
  (encode : Π {α} [serial α], f α → put_m.{v})
  (decode : Π {α} [serial α], get_m (f α))
  (correctness : ∀ {α} [serial α] (w : f α), decode -<< encode w = pure w)

instance serial.serial1 {f α} [serial1 f] [serial α] : serial (f α) :=
{ encode := λ x, serial1.encode x,
  decode := serial1.decode f,
  correctness := serial1.correctness }

class serial2 (f : Type u → Type v → Type w) :=
  (encode : Π {α β} [serial α] [serial β], f α β → put_m.{w})
  (decode : Π {α β} [serial α] [serial β], get_m (f α β))
  (correctness : ∀ {α β} [serial α] [serial β] (w : f α β), decode -<< encode w = pure w)

instance serial.serial2 {f α β} [serial2 f] [serial α] [serial β] : serial (f α β) :=
{ encode := λ x, serial2.encode x,
  decode := serial2.decode f,
  correctness := serial2.correctness }

instance serial1.serial2 {f α} [serial2 f] [serial α] : serial1 (f α) :=
{ encode := λ β inst x, @serial2.encode _ _ α β _ inst x,
  decode := λ β inst, @serial2.decode f _ α β _ inst,
  correctness := λ β inst, @serial2.correctness _ _ α β _ inst }

export serial (encode decode)

namespace serial

open function

variables {α β σ γ : Type u} {ω : Type}

def serialize [serial α] (x : α) : list unsigned := (encode x).eval
def deserialize (α : Type u) [serial α] (bytes : list unsigned) : option α := (decode α).eval bytes

lemma deserialize_serialize  [serial α] (x : α) :
  deserialize _ (serialize x) = some x :=
by simp [deserialize,serialize,eval_eval,serial.correctness]; refl

lemma encode_decode_bind [serial α]
  (f : α → get_m β) (f' : punit → put_m) (w : α) :
  (decode α >>= f) -<< (encode w >>= f') = f w -<< f' punit.star :=
by { rw [read_write_mono]; rw serial.correctness; refl }

lemma encode_decode_bind' [serial α]
  (f : α → get_m β) (w : α) :
  (decode α >>= f) -<< (encode w) = f w -<< pure punit.star :=
by { rw [read_write_mono_left]; rw serial.correctness; refl }

lemma encode_decode_pure
  (w w' : α) (u : punit) :
  (pure w) -<< (pure u) = pure w' ↔ w = w' :=
by split; intro h; cases h; refl

open ulift

protected def ulift.encode [serial α] (w : ulift.{v} α) : put_m :=
liftable1.up equiv.punit_equiv_punit (encode (down w))

protected def ulift.decode [serial α] : get_m (ulift α) :=
get_m.up ulift.up (decode α)

instance [serial α] : serial (ulift.{v u} α) :=
{ encode := ulift.encode
, decode := ulift.decode
, correctness :=
  by { introv, simp [ulift.encode,ulift.decode],
       rw up_read_write' _ equiv.ulift.symm,
       rw [serial.correctness], cases w, refl,
       intro, refl } }

instance unsigned.serial : serial unsigned :=
{ encode := λ w, put_m'.write w put_m'.pure
, decode := get_m.read get_m.pure
, correctness := by introv; refl }

def write_word (w : unsigned) : put_m.{u} :=
encode (up.{u} w)

@[simp] lemma loop_read_write_word {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)
  (rest : punit → put_m) :
  get_m.loop f g x -<< (write_word w >>= rest) =
  (f x w >>= @sum.rec _ _ (λ _, get_m γ) g (get_m.loop f g)) -<< rest punit.star := rfl

@[simp] lemma loop_read_write_word' {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)  :
  get_m.loop f g x -<< (write_word w) =
  (f x w >>= @sum.rec _ _ (λ _, get_m γ) g (get_m.loop f g)) -<< pure punit.star := rfl

def read_word : get_m.{u} (ulift unsigned) :=
decode _

def select_tag' (tag : unsigned) : list (unsigned × get_m α) → get_m α
| [] := get_m.fail
| ((w,x) :: xs) := if w = tag then x else select_tag' xs

def select_tag (xs : list (unsigned × get_m α)) : get_m α :=
do w ← read_word,
   select_tag' (down w) xs

@[simp]
lemma read_write_tag_hit {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = x -<< y :=
by subst w'; simp [select_tag,(>>),read_word,write_word,encode_decode_bind,select_tag']

lemma read_write_tag_hit' {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w') = x -<< pure punit.star :=
by subst w'; simp [select_tag,(>>),read_word,write_word,encode_decode_bind',select_tag']

@[simp]
lemma read_write_tag_miss {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w ≠ w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = select_tag xs -<< (write_word w' >> y) :=
by simp [select_tag,(>>),read_word,write_word,encode_decode_bind,select_tag',*]

def recursive_parser {α} : ℕ → (get_m α → get_m α) → get_m α
| 0 _ := get_m.fail
| (nat.succ n) rec_fn := rec_fn $ recursive_parser n rec_fn

lemma recursive_parser_unfold {α} (n : ℕ) (f : get_m α → get_m α) (h : 1 ≤ n) :
  recursive_parser n f = f (recursive_parser (n-1) f) :=
by cases n; [ cases h, refl ]

attribute [simp] serial.correctness

end serial

structure serializer (α : Type u) (β : Type u) :=
(encoder : α → put_m.{u})
(decoder : get_m β)

namespace serializer

def valid_serializer {α} (x : serializer α α) :=
serial_inverse
      (serializer.encoder x)
      (serializer.decoder x)

lemma serializer.eq {α β} (x y : serializer α β)
  (h : x.encoder = y.encoder)
  (h' : x.decoder = y.decoder) :
  x = y :=
by cases x; cases y; congr; assumption

namespace serializer.seq

variables {α : Type u} {i j : Type u}
variables (x : serializer α (i → j))
variables (y : serializer α i)

def encoder := λ (k : α), x.encoder k >> y.encoder k
def decoder := x.decoder <*> y.decoder

end serializer.seq

instance {α : Type u} : applicative (serializer.{u} α) :=
{ pure := λ i x, { encoder := λ _, return punit.star, decoder := pure x }
, seq := λ i j x y,
  { encoder := serializer.seq.encoder x y
  , decoder := serializer.seq.decoder x y } }

section lawful_applicative

variables {α β : Type u} {σ : Type u}

@[simp]
lemma decoder_pure (x : β) :
  (pure x : serializer σ β).decoder = pure x := rfl

@[simp]
lemma decoder_map (f : α → β) (x : serializer σ α) :
  (f <$> x).decoder = f <$> x.decoder := rfl

@[simp]
lemma decoder_seq (f : serializer σ (α → β)) (x : serializer σ α) :
  (f <*> x).decoder = f.decoder <*> x.decoder := rfl

@[simp]
lemma encoder_pure (x : β) (w : σ) :
  (pure x : serializer σ β).encoder w = pure punit.star := rfl

@[simp]
lemma encoder_map (f : α → β) (w : σ) (x : serializer σ α) :
  (f <$> x : serializer σ β).encoder w = x.encoder w := rfl

@[simp]
lemma encoder_seq (f : serializer σ (α → β)) (x : serializer σ α) (w : σ) :
  (f <*> x : serializer σ β).encoder w = f.encoder w >> x.encoder w := rfl

end lawful_applicative

instance {α} : is_lawful_functor (serializer.{u} α) :=
by refine { .. }; intros; apply serializer.eq; try { ext }; simp [map_map]

instance {α} : is_lawful_applicative (serializer.{u} α) :=
by{  constructor; intros; apply serializer.eq; try { ext };
     simp [(>>),pure_seq_eq_map,seq_assoc,bind_assoc],  }

def ser_field {α β} [serial β] (f : α → β) : serializer α β :=
{ encoder := λ x, encode (f x)
, decoder := @decode _ _ }

variables {α β σ γ : Type u} {ω : Type}

def there_and_back_again
  (y : serializer γ α) (w : γ) : option α :=
y.decoder -<< y.encoder w

lemma there_and_back_again_seq [serial α]
  (x : serializer γ (α → β)) (f : α → β) (y : γ → α) (w : γ) (w' : β)
  (h' : there_and_back_again x w = pure f)
  (h  : w' = f (y w)) :
  there_and_back_again (x <*> ser_field y) w = pure w' :=
by { simp [there_and_back_again,(>>),seq_eq_bind_map] at *,
     rw [read_write_mono h',map_read_write],
     rw [ser_field,serial.correctness], subst w', refl }

@[simp]
lemma there_and_back_again_map [serial α]
  (f : α → β) (y : γ → α) (w : γ) :
  there_and_back_again (f <$> ser_field y) w = pure (f $ y w) :=
by rw [← pure_seq_eq_map,there_and_back_again_seq]; refl

@[simp]
lemma there_and_back_again_pure (x : β) (w : γ) :
  there_and_back_again (pure x) w =
  pure x := rfl

lemma valid_serializer_of_there_and_back_again
      {α : Type*} (y : serializer α α) :
  valid_serializer y ↔
  ∀ (w : α), there_and_back_again y w = pure w :=
by { simp [valid_serializer,serial_inverse],
     repeat { rw forall_congr, intro }, refl }

open ulift

def ser_field' {α β} [serial β] (f : α → β) : serializer.{max u v} α (ulift.{v} β) :=
ser_field (up ∘ f)

def of_serializer {α} (s : serializer α α) (h : ∀ w, there_and_back_again s w = pure w) : serial α :=
{ encode := s.encoder
, decode := s.decoder
, correctness := @h }

def of_serializer₁ {f : Type u → Type v}
  (s : Π α [serial α], serializer (f α) (f α))
  (h : ∀ α [serial α] w, there_and_back_again (s α) w = pure w) : serial1 f :=
{ encode := λ α inst, (@s α inst).encoder
, decode := λ α inst, (@s α inst).decoder
, correctness := @h }

def of_serializer₂ {f : Type u → Type v → Type w}
  (s : Π α β [serial α] [serial β], serializer (f α β) (f α β))
  (h : ∀ α β [serial α] [serial β] w, there_and_back_again (s α β) w = pure w) : serial2 f :=
{ encode := λ α β inst inst', (@s α β inst inst').encoder
, decode := λ α β inst inst', (@s α β inst inst').decoder
, correctness := @h }

end serializer
