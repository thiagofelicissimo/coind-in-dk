require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__List as Agda__Builtin__List;
require tests.Agda__Builtin__Unit as Agda__Builtin__Unit;
require tests.boolaux as boolaux;
require tests.eqaux as eqaux;
constant symbol TYPE__Lang : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Lang : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Lang $A) ↪ TYPE__Lang $A;
constant symbol {|!Lang'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A))) (λ {|!δ|}, (Lang A)))))));
symbol {|!Lang__ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, Agda__Builtin__Bool.Bool))));
symbol {|!Lang__δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Lang A)))))));


rule {|!Lang__ν|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ ${|!ν|};
 
rule {|!Lang__δ|} $A ({|!Lang'constructor|} _ ${|!ν|} ${|!δ|}) ↪ ${|!δ|};
 
symbol {|!_∈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, Agda__Builtin__Bool.Bool))))));
rule {|!_∈_|} $A (Agda__Builtin__List.{|!List__[]|} _ _) $x ↪ {|!Lang__ν|} $A $x;
rule {|!_∈_|} $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x ↪ {|!_∈_|} $A $x0 ({|!Lang__δ|} $A $x $x1);
 
symbol trie : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, Agda__Builtin__Bool.Bool)) (λ f, (Lang A)))));
rule {|!Lang__ν|} _ (trie $A $f) ↪ $f (Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) $A);
rule {|!Lang__δ|} _ (trie $A $f) $x ↪ trie $A (λ ls, $f (Agda__Builtin__List.{|!List___∷_|} (s 0ₙ z) $A $x ls));
 
symbol {|!∅|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!∅|} $A) ↪ Agda__Builtin__Bool.Bool__false;
rule {|!Lang__δ|} _ ({|!∅|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!A*|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!A*|} $A) ↪ Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!A*|} $A) $x ↪ {|!A*|} $A;
 
symbol {|!ε|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Lang A)));
rule {|!Lang__ν|} _ ({|!ε|} $A) ↪ Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!ε|} $A) $x ↪ {|!∅|} $A;
 
symbol {|!¬|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))));
rule {|!Lang__ν|} _ ({|!¬|} $A $x) ↪ boolaux.not ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!¬|} $A $x0) $x ↪ {|!¬|} $A ({|!Lang__δ|} $A $x0 $x);
 
symbol {|!_∪_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_∪_|} $A $x0 $x) ↪ boolaux.{|!_∨_|} ({|!Lang__ν|} $A $x0) ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!_∪_|} $A $x1 $x0) $x ↪ {|!_∪_|} $A ({|!Lang__δ|} $A $x1 $x) ({|!Lang__δ|} $A $x0 $x);
 
symbol {|!_∩_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_∩_|} $A $x0 $x) ↪ boolaux.{|!_∧_|} ({|!Lang__ν|} $A $x0) ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!_∩_|} $A $x1 $x0) $x ↪ {|!_∩_|} $A ({|!Lang__δ|} $A $x1 $x) ({|!Lang__δ|} $A $x0 $x);
 
symbol {|!_·_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))))));
rule {|!Lang__ν|} _ ({|!_·_|} $A $x0 $x) ↪ boolaux.{|!_∧_|} ({|!Lang__ν|} $A $x0) ({|!Lang__ν|} $A $x);
rule {|!Lang__δ|} _ ({|!_·_|} $A $x1 $x0) $x ↪ boolaux.if_then_else_ (Lang $A) ({|!Lang__ν|} $A $x1) ({|!_∪_|} $A ({|!_·_|} $A ({|!Lang__δ|} $A $x1 $x) $x0) ({|!Lang__δ|} $A $x0 $x)) ({|!_·_|} $A ({|!Lang__δ|} $A $x1 $x) $x0);
 
symbol {|!_*|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ _0, (Lang A)))));
rule {|!Lang__ν|} _ ({|!_*|} $A $x) ↪ Agda__Builtin__Bool.Bool__true;
rule {|!Lang__δ|} _ ({|!_*|} $A $x0) $x ↪ {|!_·_|} $A ({|!Lang__δ|} $A $x0 $x) ({|!_*|} $A $x0);
 
constant symbol {|!TYPE___≈_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π l : El (set (s 0ₙ z)) (Lang A), Π {|!s|} : El (set (s 0ₙ z)) (Lang A), TYPE;
constant symbol {|!_≈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Lang A) (λ {|!s|}, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≈_|} $A $l ${|!s|}) ↪ {|!TYPE___≈_|} $A $l ${|!s|};
symbol {|!_≈___≈ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ r, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A l) ({|!Lang__ν|} A {|!s|}))))))))));
symbol {|!_≈___≈δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≈_|} A ({|!Lang__δ|} A l a) ({|!Lang__δ|} A {|!s|} a))))))))))));
constant symbol {|!_≈_'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} A l) ({|!Lang__ν|} A {|!s|})) (λ {|!≈ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, ({|!_≈_|} A ({|!Lang__δ|} A l a) ({|!Lang__δ|} A {|!s|} a)))) (λ {|!≈δ|}, ({|!_≈_|} A l {|!s|})))))))))));

rule {|!_≈___≈ν|} $A $l ${|!s|} ({|!_≈_'constructor|} _ _ _ ${|!≈ν|} ${|!≈δ|}) ↪ ${|!≈ν|};
 
rule {|!_≈___≈δ|} $A $l ${|!s|} ({|!_≈_'constructor|} _ _ _ ${|!≈ν|} ${|!≈δ|}) ↪ ${|!≈δ|};
 

symbol {|!≈refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A l l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈refl|} $A $l) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l);
rule {|!_≈___≈δ|} _ _ _ ({|!≈refl|} $A $l) $a ↪ {|!≈refl|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!≈sym|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ _0, ({|!_≈_|} A {|!s|} l)))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈sym|} $A $l ${|!s|} $x) ↪ eqaux.sym Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!_≈___≈ν|} $A $l ${|!s|} $x);
rule {|!_≈___≈δ|} _ _ _ ({|!≈sym|} $A $l ${|!s|} $x) $a ↪ {|!≈sym|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!_≈___≈δ|} $A $l ${|!s|} $x $a);
 
symbol {|!≈trans|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!s|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A {|!s|} k) (λ _0, ({|!_≈_|} A l k)))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!≈trans|} $A $l ${|!s|} $k $x0 $x) ↪ eqaux.trans Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!Lang__ν|} $A $k) ({|!_≈___≈ν|} $A $l ${|!s|} $x0) ({|!_≈___≈ν|} $A ${|!s|} $k $x);
rule {|!_≈___≈δ|} _ _ _ ({|!≈trans|} $A $l ${|!s|} $k $x0 $x) $a ↪ {|!≈trans|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!Lang__δ|} $A $k $a) ({|!_≈___≈δ|} $A $l ${|!s|} $x0 $a) ({|!_≈___≈δ|} $A ${|!s|} $k $x $a);
 
symbol {|!∪-assoc|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, ({|!_≈_|} A ({|!_∪_|} A ({|!_∪_|} A l {|!s|}) k) ({|!_∪_|} A l ({|!_∪_|} A {|!s|} k)))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-assoc|} $A $l ${|!s|} $k) ↪ boolaux.{|!∨-assoc|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!Lang__ν|} $A $k);
rule {|!_≈___≈δ|} _ _ _ ({|!∪-assoc|} $A $l ${|!s|} $k) $a ↪ {|!∪-assoc|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!Lang__δ|} $A $k $a);
 
symbol {|!∪-comm|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, ({|!_≈_|} A ({|!_∪_|} A l {|!s|}) ({|!_∪_|} A {|!s|} l))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-comm|} $A $l ${|!s|}) ↪ boolaux.{|!∨-comm|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|});
rule {|!_≈___≈δ|} _ _ _ ({|!∪-comm|} $A $l ${|!s|}) $a ↪ {|!∪-comm|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a);
 
symbol {|!∪-idem|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A l l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-idem|} $A $l) ↪ boolaux.{|!∨-idem|} ({|!Lang__ν|} $A $l);
rule {|!_≈___≈δ|} _ _ _ ({|!∪-idem|} $A $l) $a ↪ {|!∪-idem|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!∪-cong|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!l'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!l'|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A {|!s|} {|!s'|}) (λ _0, ({|!_≈_|} A ({|!_∪_|} A l {|!s|}) ({|!_∪_|} A {|!l'|} {|!s'|}))))))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-cong|} $A ${|!l'|} ${|!s'|} $l ${|!s|} $x0 $x) ↪ boolaux.{|!∨-cong|} ({|!Lang__ν|} $A ${|!l'|}) ({|!Lang__ν|} $A ${|!s'|}) ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!_≈___≈ν|} $A $l ${|!l'|} $x0) ({|!_≈___≈ν|} $A ${|!s|} ${|!s'|} $x);
rule {|!_≈___≈δ|} _ _ _ ({|!∪-cong|} $A ${|!l'|} ${|!s'|} $l ${|!s|} $x0 $x) $a ↪ {|!∪-cong|} $A ({|!Lang__δ|} $A ${|!l'|} $a) ({|!Lang__δ|} $A ${|!s'|} $a) ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!_≈___≈δ|} $A $l ${|!l'|} $x0 $a) ({|!_≈___≈δ|} $A ${|!s|} ${|!s'|} $x $a);
 
symbol {|!∩-assoc|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, ({|!_≈_|} A ({|!_∩_|} A ({|!_∩_|} A l {|!s|}) k) ({|!_∩_|} A l ({|!_∩_|} A {|!s|} k)))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-assoc|} $A $l ${|!s|} $k) ↪ boolaux.{|!∧-assoc|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!Lang__ν|} $A $k);
rule {|!_≈___≈δ|} _ _ _ ({|!∩-assoc|} $A $l ${|!s|} $k) $a ↪ {|!∩-assoc|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!Lang__δ|} $A $k $a);
 
symbol {|!∩-comm|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, ({|!_≈_|} A ({|!_∩_|} A l {|!s|}) ({|!_∩_|} A {|!s|} l))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-comm|} $A $l ${|!s|}) ↪ boolaux.{|!∧-comm|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|});
rule {|!_≈___≈δ|} _ _ _ ({|!∩-comm|} $A $l ${|!s|}) $a ↪ {|!∩-comm|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a);
 
symbol {|!∩-idem|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∩_|} A l l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-idem|} $A $l) ↪ boolaux.{|!∧-idem|} ({|!Lang__ν|} $A $l);
rule {|!_≈___≈δ|} _ _ _ ({|!∩-idem|} $A $l) $a ↪ {|!∩-idem|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!∩-cong|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!l'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A l {|!l'|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A {|!s|} {|!s'|}) (λ _0, ({|!_≈_|} A ({|!_∩_|} A l {|!s|}) ({|!_∩_|} A {|!l'|} {|!s'|}))))))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-cong|} $A ${|!l'|} ${|!s'|} $l ${|!s|} $x0 $x) ↪ boolaux.{|!∧-cong|} ({|!Lang__ν|} $A ${|!l'|}) ({|!Lang__ν|} $A ${|!s'|}) ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!_≈___≈ν|} $A $l ${|!l'|} $x0) ({|!_≈___≈ν|} $A ${|!s|} ${|!s'|} $x);
rule {|!_≈___≈δ|} _ _ _ ({|!∩-cong|} $A ${|!l'|} ${|!s'|} $l ${|!s|} $x0 $x) $a ↪ {|!∩-cong|} $A ({|!Lang__δ|} $A ${|!l'|} $a) ({|!Lang__δ|} $A ${|!s'|} $a) ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!_≈___≈δ|} $A $l ${|!l'|} $x0 $a) ({|!_≈___≈δ|} $A ${|!s|} ${|!s'|} $x $a);
 
symbol {|!∪-unit₁|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A ({|!∅|} A) l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-unit₁|} $A $l) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∪_|} $A ({|!∅|} $A) $l));
rule {|!_≈___≈δ|} _ _ _ ({|!∪-unit₁|} $A $l) $a ↪ {|!∪-unit₁|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!∪-unit₂|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A l ({|!∅|} A)) l)))));
rule {|!∪-unit₂|} $A $l ↪ {|!≈trans|} $A ({|!_∪_|} $A $l ({|!∅|} $A)) ({|!_∪_|} $A ({|!∅|} $A) $l) $l ({|!∪-comm|} $A $l ({|!∅|} $A)) ({|!∪-unit₁|} $A $l);
 
symbol {|!∩-unit₁|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∩_|} A ({|!A*|} A) l) l)))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-unit₁|} $A $l) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A ({|!_∩_|} $A ({|!A*|} $A) $l));
rule {|!_≈___≈δ|} _ _ _ ({|!∩-unit₁|} $A $l) $a ↪ {|!∩-unit₁|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!∩-unit₂|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∩_|} A l ({|!A*|} A)) l)))));
rule {|!∩-unit₂|} $A $l ↪ {|!≈trans|} $A ({|!_∩_|} $A $l ({|!A*|} $A)) ({|!_∩_|} $A ({|!A*|} $A) $l) $l ({|!∩-comm|} $A $l ({|!A*|} $A)) ({|!∩-unit₁|} $A $l);
 
symbol {|!∪-∩-dist|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, ({|!_≈_|} A ({|!_∪_|} A l ({|!_∩_|} A {|!s|} k)) ({|!_∩_|} A ({|!_∪_|} A l {|!s|}) ({|!_∪_|} A l k)))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-∩-dist|} $A $l ${|!s|} $k) ↪ boolaux.{|!∨-∧-dist|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!Lang__ν|} $A $k);
rule {|!_≈___≈δ|} _ _ _ ({|!∪-∩-dist|} $A $l ${|!s|} $k) $a ↪ {|!∪-∩-dist|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!Lang__δ|} $A $k $a);
 
symbol {|!∩-∪-dist|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ k, ({|!_≈_|} A ({|!_∩_|} A l ({|!_∪_|} A {|!s|} k)) ({|!_∪_|} A ({|!_∩_|} A l {|!s|}) ({|!_∩_|} A l k)))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-∪-dist|} $A $l ${|!s|} $k) ↪ boolaux.{|!∧-∨-dist|} ({|!Lang__ν|} $A $l) ({|!Lang__ν|} $A ${|!s|}) ({|!Lang__ν|} $A $k);
rule {|!_≈___≈δ|} _ _ _ ({|!∩-∪-dist|} $A $l ${|!s|} $k) $a ↪ {|!∩-∪-dist|} $A ({|!Lang__δ|} $A $l $a) ({|!Lang__δ|} $A ${|!s|} $a) ({|!Lang__δ|} $A $k $a);
 
symbol {|!∪-comp|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∪_|} A l ({|!¬|} A l)) ({|!A*|} A))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∪-comp|} $A $l) ↪ boolaux.{|!∨-comp|} ({|!Lang__ν|} $A $l);
rule {|!_≈___≈δ|} _ _ _ ({|!∪-comp|} $A $l) $a ↪ {|!∪-comp|} $A ({|!Lang__δ|} $A $l $a);
 
symbol {|!∩-comp|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Lang A) (λ l, ({|!_≈_|} A ({|!_∩_|} A l ({|!¬|} A l)) ({|!∅|} A))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∩-comp|} $A $l) ↪ boolaux.{|!∧-comp|} ({|!Lang__ν|} $A $l);
rule {|!_≈___≈δ|} _ _ _ ({|!∩-comp|} $A $l) $a ↪ {|!∩-comp|} $A ({|!Lang__δ|} $A $l $a);
 
constant symbol TYPE__DA : Π S : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol DA : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))))));
rule El _ (DA $S $A) ↪ TYPE__DA $S $A;
symbol {|!DA__ν|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, Agda__Builtin__Bool.Bool))))))));
symbol {|!DA__δ|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ r, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, S))))))))));
constant symbol {|!DA'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, Agda__Builtin__Bool.Bool)) (λ {|!ν|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ a, S)))) (λ {|!δ|}, (DA S A)))))))));

rule {|!DA__ν|} $S $A ({|!DA'constructor|} _ _ ${|!ν|} ${|!δ|}) ↪ ${|!ν|};
 
rule {|!DA__δ|} $S $A ({|!DA'constructor|} _ _ ${|!ν|} ${|!δ|}) ↪ ${|!δ|};
 

symbol lang : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, (Lang A)))))))));
rule {|!Lang__ν|} _ (lang $A $S $da ${|!s|}) ↪ {|!DA__ν|} $S $A $da ${|!s|};
rule {|!Lang__δ|} _ (lang $A $S $da ${|!s|}) $x ↪ lang $A $S $da ({|!DA__δ|} $S $A $da ${|!s|} $x);
 
constant symbol {|!TYPE___×_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π B : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol {|!_×_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ B, (⋄ (set (s 0ₙ z)))))));
rule El _ ({|!_×_|} $A $B) ↪ {|!TYPE___×_|} $A $B;
symbol {|!_×___fst|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_×_|} A B) (λ r, A))))));
symbol {|!_×___snd|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_×_|} A B) (λ r, B))))));
constant symbol {|!_,_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ fst, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) B (λ snd, ({|!_×_|} A B)))))))));

rule {|!_×___fst|} $A $B ({|!_,_|} _ _ $fst $snd) ↪ $fst;
 
rule {|!_×___snd|} $A $B ({|!_,_|} _ _ $fst $snd) ↪ $snd;
 

symbol {|!_⊕_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ {|!S'|}, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA {|!S'|} A) (λ {|!da'|}, (DA ({|!_×_|} S {|!S'|}) A)))))))))));
rule {|!DA__ν|} _ _ ({|!_⊕_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} _ _ $fst $snd) ↪ boolaux.{|!_∨_|} ({|!DA__ν|} $S $A $da $fst) ({|!DA__ν|} ${|!S'|} $A ${|!da'|} $snd);
rule {|!DA__δ|} _ _ ({|!_⊕_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} _ _ $fst $snd) $a ↪ {|!_,_|} $S ${|!S'|} ({|!DA__δ|} $S $A $da $fst $a) ({|!DA__δ|} ${|!S'|} $A ${|!da'|} $snd $a);
 
symbol {|!⊕-is-∪|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ {|!S'|}, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA {|!S'|} A) (λ {|!da'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) {|!S'|} (λ {|!s'|}, ({|!_≈_|} A (lang A ({|!_×_|} S {|!S'|}) ({|!_⊕_|} S {|!S'|} A da {|!da'|}) ({|!_,_|} S {|!S'|} {|!s|} {|!s'|})) ({|!_∪_|} A (lang A S da {|!s|}) (lang A {|!S'|} {|!da'|} {|!s'|})))))))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!⊕-is-∪|} $S ${|!S'|} $A $da ${|!da'|} ${|!s|} ${|!s'|}) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A ({|!_×_|} $S ${|!S'|}) ({|!_⊕_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} $S ${|!S'|} ${|!s|} ${|!s'|})));
rule {|!_≈___≈δ|} _ _ _ ({|!⊕-is-∪|} $S ${|!S'|} $A $da ${|!da'|} ${|!s|} ${|!s'|}) $a ↪ {|!⊕-is-∪|} $S ${|!S'|} $A $da ${|!da'|} ({|!DA__δ|} $S $A $da ${|!s|} $a) ({|!DA__δ|} ${|!S'|} $A ${|!da'|} ${|!s'|} $a);
 
symbol {|!_⊗_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ {|!S'|}, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA {|!S'|} A) (λ {|!da'|}, (DA ({|!_×_|} S {|!S'|}) A)))))))))));
rule {|!DA__ν|} _ _ ({|!_⊗_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} _ _ $fst $snd) ↪ boolaux.{|!_∧_|} ({|!DA__ν|} $S $A $da $fst) ({|!DA__ν|} ${|!S'|} $A ${|!da'|} $snd);
rule {|!DA__δ|} _ _ ({|!_⊗_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} _ _ $fst $snd) $a ↪ {|!_,_|} $S ${|!S'|} ({|!DA__δ|} $S $A $da $fst $a) ({|!DA__δ|} ${|!S'|} $A ${|!da'|} $snd $a);
 
symbol {|!⊗-is-∩|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ {|!S'|}, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA {|!S'|} A) (λ {|!da'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) {|!S'|} (λ {|!s'|}, ({|!_≈_|} A (lang A ({|!_×_|} S {|!S'|}) ({|!_⊗_|} S {|!S'|} A da {|!da'|}) ({|!_,_|} S {|!S'|} {|!s|} {|!s'|})) ({|!_∩_|} A (lang A S da {|!s|}) (lang A {|!S'|} {|!da'|} {|!s'|})))))))))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!⊗-is-∩|} $S ${|!S'|} $A $da ${|!da'|} ${|!s|} ${|!s'|}) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A ({|!_×_|} $S ${|!S'|}) ({|!_⊗_|} $S ${|!S'|} $A $da ${|!da'|}) ({|!_,_|} $S ${|!S'|} ${|!s|} ${|!s'|})));
rule {|!_≈___≈δ|} _ _ _ ({|!⊗-is-∩|} $S ${|!S'|} $A $da ${|!da'|} ${|!s|} ${|!s'|}) $a ↪ {|!⊗-is-∩|} $S ${|!S'|} $A $da ${|!da'|} ({|!DA__δ|} $S $A $da ${|!s|} $a) ({|!DA__δ|} ${|!S'|} $A ${|!da'|} ${|!s'|} $a);
 
symbol inv : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ _0, (DA S A)))))));
rule {|!DA__ν|} _ _ (inv $S $A $x) ${|!s|} ↪ boolaux.not ({|!DA__ν|} $S $A $x ${|!s|});
rule {|!DA__δ|} _ _ (inv $S $A $x) ${|!s|} $a ↪ {|!DA__δ|} $S $A $x ${|!s|} $a;
 
symbol {|!inv-is-¬|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ S, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (DA S A) (λ da, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) S (λ {|!s|}, ({|!_≈_|} A (lang A S (inv S A da) {|!s|}) ({|!¬|} A (lang A S da {|!s|})))))))))));
rule {|!_≈___≈ν|} _ _ _ ({|!inv-is-¬|} $S $A $da ${|!s|}) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A $S (inv $S $A $da) ${|!s|}));
rule {|!_≈___≈δ|} _ _ _ ({|!inv-is-¬|} $S $A $da ${|!s|}) $a ↪ {|!inv-is-¬|} $S $A $da ({|!DA__δ|} $S $A $da ${|!s|} $a);
 
symbol {|!∅A|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (DA Agda__Builtin__Unit.{|!⊤|} A)));
rule {|!DA__ν|} _ _ ({|!∅A|} $A) ${|!s|} ↪ Agda__Builtin__Bool.Bool__false;
rule {|!DA__δ|} _ _ ({|!∅A|} $A) ${|!s|} $a ↪ ${|!s|};
 
symbol {|!∅A-is-∅|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Unit.{|!⊤|} (λ {|!s|}, ({|!_≈_|} A (lang A Agda__Builtin__Unit.{|!⊤|} ({|!∅A|} A) {|!s|}) ({|!∅|} A))))));
rule {|!_≈___≈ν|} _ _ _ ({|!∅A-is-∅|} $A ${|!s|}) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A Agda__Builtin__Unit.{|!⊤|} ({|!∅A|} $A) ${|!s|}));
rule {|!_≈___≈δ|} _ _ _ ({|!∅A-is-∅|} $A ${|!s|}) $a ↪ {|!∅A-is-∅|} $A ${|!s|};
 
symbol {|!εA|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (DA Agda__Builtin__Bool.Bool A)));
rule {|!DA__ν|} _ _ ({|!εA|} $A) ${|!s|} ↪ ${|!s|};
rule {|!DA__δ|} _ _ ({|!εA|} $A) ${|!s|} $a ↪ Agda__Builtin__Bool.Bool__false;
 
symbol {|!εA-is-ε'|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, ({|!_≈_|} A (lang A Agda__Builtin__Bool.Bool ({|!εA|} A) Agda__Builtin__Bool.Bool__false) ({|!∅|} A))));
rule {|!_≈___≈ν|} _ _ _ ({|!εA-is-ε'|} $A) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A Agda__Builtin__Bool.Bool ({|!εA|} $A) Agda__Builtin__Bool.Bool__false));
rule {|!_≈___≈δ|} _ _ _ ({|!εA-is-ε'|} $A) $a ↪ {|!εA-is-ε'|} $A;
 
symbol {|!εA-is-ε|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, ({|!_≈_|} A (lang A Agda__Builtin__Bool.Bool ({|!εA|} A) Agda__Builtin__Bool.Bool__true) ({|!ε|} A))));
rule {|!_≈___≈ν|} _ _ _ ({|!εA-is-ε|} $A) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!Lang__ν|} $A (lang $A Agda__Builtin__Bool.Bool ({|!εA|} $A) Agda__Builtin__Bool.Bool__true));
rule {|!_≈___≈δ|} _ _ _ ({|!εA-is-ε|} $A) $a ↪ {|!εA-is-ε'|} $A;
 
