/- 

Alunos:
 - Lucas Resck
 - Lucas Moschen

Formalize em FOL:

Três irmãs - Ana, Maria e Cláudia - foram a uma festa com vestidos de
cores diferentes. Uma vestia azul, a outra branco e a Terceira
preto. Chegando à festa, o anfitrião perguntou quem era cada uma
delas. As respostas foram:

- A de azul respondeu: “Ana é a que está de branco”
- A de branco falou: “Eu sou Maria”
- A de preto disse:  “Cláudia é quem está de branco”

O anfitrião foi capaz de identificar corretamente quem era cada pessoa
considerando que:

- Ana sempre diz a verdade
- Maria às vezes diz a verdade
- Cláudia nunca diz a verdade

Pensando um pouco sobre o problema, pode-se concluir que a Ana estava
com o vestido preto, a Cláudia com o branco e a Maria com o
azul.  
-/

-- I define two import types in the problem
constant Colors : Type
constant People : Type

-- I define the function and some constants quoteds in the problem
constant DressColor : People → Colors → Prop

constant Ana : People
constant Maria : People
constant Claudia : People

constant Black : Colors
constant White : Colors
constant Blue : Colors

-- The condition that everyone quoted is dressed with only one dress color.
variable AnaDressed : ∃ x : Colors, DressColor Ana x ∧ 
                      (∀ y: Colors, ¬ (y = x) → ¬ (DressColor Ana y))
variable ClaudiaDressed : ∃ x : Colors, DressColor Claudia x ∧ 
                          (∀ y: Colors, ¬ (y = x) → ¬ (DressColor Claudia y))
variable MariaDressed : ∃ x : Colors, DressColor Maria x ∧ 
                        (∀ y: Colors, ¬ (y = x) → ¬ (DressColor Maria y))

-- The condition that every color quoted is used by only one person 
variable BlackUsed : ∃ x : People, DressColor x Black ∧ 
                    (∀ y : People, ¬ (y = x) → ¬ (DressColor y Black))
variable WhiteUsed : ∃ x : People, DressColor x White ∧ 
                    (∀ y : People, ¬ (y = x) → ¬ (DressColor y White))
variable BlueUsed: ∃ x : People, DressColor x Blue ∧ 
                   (∀ y : People, ¬ (y = x) → ¬ (DressColor y Blue))

-- This conditions are importants to use some relations with the dresses in this particular case
variable a: (DressColor Ana Black ∨ DressColor Ana White ∨ DressColor Ana Blue) ∧
            ¬ (DressColor Ana Black ∧ DressColor Ana White) ∧ 
            ¬ (DressColor Ana Black ∧ DressColor Ana Blue) ∧ 
            ¬ (DressColor Ana Blue ∧ DressColor Ana White)
variable c: (DressColor Claudia Black ∨ DressColor Claudia White ∨ DressColor Claudia Blue) ∧
            ¬ (DressColor Claudia Black ∧ DressColor Claudia White) ∧ 
            ¬ (DressColor Claudia Black ∧ DressColor Claudia Blue) ∧ 
            ¬ (DressColor Claudia Blue ∧ DressColor Claudia White)
variable m: (DressColor Maria Black ∨ DressColor Maria White ∨ DressColor Maria Blue) ∧
            ¬ (DressColor Maria Black ∧ DressColor Maria White) ∧ 
            ¬ (DressColor Maria Black ∧ DressColor Maria Blue) ∧ 
            ¬ (DressColor Maria Blue ∧ DressColor Maria White)

-- We know Ana always says the truth and Claudia doesn't. 
variable AnaBlue: DressColor Ana Blue → DressColor Ana White
variable AnaWhite: DressColor Ana White → DressColor Maria White
variable AnaBlack: DressColor Ana Black → DressColor Claudia Blue

variable ClaudiaBlue: DressColor Claudia Blue → ¬ (DressColor Ana White)
variable ClaudiaWhite: DressColor Claudia White → ¬ (DressColor Maria White)
variable ClaudiaBlack: DressColor Claudia Black → ¬ (DressColor Claudia Blue)

-- Note that Maria is not necessary, because we do not know if she says truth

-- Variable that needed to be proved
variable conclusion: (DressColor Ana Black) ∧ 
            (DressColor Claudia White) ∧ 
            (DressColor Maria Blue) 


