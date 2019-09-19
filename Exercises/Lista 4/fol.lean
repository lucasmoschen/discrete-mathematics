/-

Alunos:
 - Lucas Emanuel
 - Lucas Moschen

Assume that we have a language with the following parameters: ∀,
intended to mean “for all things”; N, intended to mean “is a number”;
I , intended to mean “is interesting”; ; 'lt', intended to mean “is
less than”; and 'z', a constant symbol intended to denote
zero. Translate into this language the English sentences listed
below. If the English sentence is ambiguous, you will need more than
one translation.

(a) Zero is less than any number.
(b) If any number is interesting, then zero is interesting.
(c) No number is less than zero.
(d) Any uninteresting number with the property that all smaller
    numbers are interesting certainly is interesting.
(e) There is no number such that all numbers are less than it.
(f) There is no number such that no number is less than it.


Complete o exercício criando as demais variáveis hb...hf. Se a frase
for ambigua, use hX1, hX2...

-/

constant U : Type
constant N : U → Prop
constant z : U
constant lt : U → U → Prop
constant I : U → Prop

variable ha : ∀ x : U , N(x) → lt z x

variable hb1 : ∀ x : U, N(x) ∧ I(x) → I(z)
variable hb2 : ∃ x : U, N(x) ∧ I(x) → I(z) 

variable hc : ¬ (∃ x : U, N(x) →  lt x z) 

variable hd : ∀ x : U, ¬ I(x) ∧ (∀ y : U, lt y x → I(y)) → I(x) 

variable he : ¬ (∃ x : U, (∀ y : U, lt y x))

variable hf : ¬ (∃ x : U, ¬ (∃ y, lt y x))

