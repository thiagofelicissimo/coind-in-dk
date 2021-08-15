require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Coinduction as Agda__Builtin__Coinduction;
require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__List as Agda__Builtin__List;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
require tests.eqaux as eqaux;
require tests.nataux as nataux;
constant symbol TYPE__Maybe : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Maybe : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Maybe $A) ↪ TYPE__Maybe $A;
constant symbol Maybe__nothing : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Maybe A)));
constant symbol Maybe__just : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Maybe A)))));



constant symbol TYPE__Stream : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Stream : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Stream $A) ↪ TYPE__Stream $A;
constant symbol {|!Stream__[]|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (Stream A)));
constant symbol {|!Stream___∷_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ xs, (Stream A)))))));



symbol zeros : El (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat);
symbol {|!___♯-0|} : El (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat));
rule zeros ↪ {|!Stream___∷_|} Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero {|!___♯-0|};
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ {|!___♯-0|} ↪ zeros;
 
symbol natStream : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (Stream Agda__Builtin__Nat.Nat)));
symbol {|!___♯-1|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat))));
rule natStream $x ↪ {|!Stream___∷_|} Agda__Builtin__Nat.Nat $x ({|!___♯-1|} $x);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-1|} $n) ↪ natStream (Agda__Builtin__Nat.Nat__suc $n);
 
symbol nth : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Maybe A)))))));
rule nth $A Agda__Builtin__Nat.Nat__zero ({|!Stream__[]|} _) ↪ Maybe__nothing $A;
rule nth $A Agda__Builtin__Nat.Nat__zero ({|!Stream___∷_|} _ $x $xs) ↪ Maybe__just $A $x;
rule nth $A (Agda__Builtin__Nat.Nat__suc $x) ({|!Stream__[]|} _) ↪ Maybe__nothing $A;
rule nth $A (Agda__Builtin__Nat.Nat__suc $x0) ({|!Stream___∷_|} _ $x $xs) ↪ nth $A $x0 (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $xs);
 
symbol {|!list-to-stream|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (Stream A)))));
symbol {|!___♯-2|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ l, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A))))))));
rule {|!list-to-stream|} $A (Agda__Builtin__List.{|!List__[]|} _ _) ↪ {|!Stream__[]|} $A;
rule {|!list-to-stream|} $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x0 $x) ↪ {|!Stream___∷_|} $A $x0 ({|!___♯-2|} $A $x0 $x);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-2|} $A $x $l) ↪ {|!list-to-stream|} $A $l;
 
symbol {|!stream-to-list|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Agda__Builtin__List.List (s 0ₙ z) A)))))));
rule {|!stream-to-list|} $A Agda__Builtin__Nat.Nat__zero $x ↪ Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) $A;
rule {|!stream-to-list|} $A (Agda__Builtin__Nat.Nat__suc $x) ({|!Stream__[]|} _) ↪ Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) $A;
rule {|!stream-to-list|} $A (Agda__Builtin__Nat.Nat__suc $x0) ({|!Stream___∷_|} _ $x $xs) ↪ Agda__Builtin__List.{|!List___∷_|} (s 0ₙ z) $A $x ({|!stream-to-list|} $A $x0 (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $xs));
 
symbol append : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Stream A)))))));
symbol {|!___♯-3|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!s|}, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A))))))))));
rule append $A (Agda__Builtin__List.{|!List__[]|} _ _) $x ↪ $x;
rule append $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x ↪ {|!Stream___∷_|} $A $x1 ({|!___♯-3|} $A $x1 $x0 $x);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-3|} $A $x $l ${|!s|}) ↪ append $A $l ${|!s|};
 
constant symbol {|!TYPE___~_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π _0 : El (set (s 0ₙ z)) (Stream A), Π _0 : El (set (s 0ₙ z)) (Stream A), TYPE;
constant symbol {|!_~_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Stream A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Stream A) (λ _0, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_~_|} $A $x0 $x) ↪ {|!TYPE___~_|} $A $x0 $x;
constant symbol {|!_~___~-empty|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, ({|!_~_|} A ({|!Stream__[]|} A) ({|!Stream__[]|} A))));
constant symbol {|!_~___~-cons|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!x'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ {|!l'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x {|!x'|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l'|}))) (λ _0, ({|!_~_|} A ({|!Stream___∷_|} A x l) ({|!Stream___∷_|} A {|!x'|} {|!l'|}))))))))))))))));



symbol {|!~-refl|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ x, ({|!_~_|} A x x)))));
symbol {|!___♯-4|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ l, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l)))))))));
rule {|!~-refl|} $A ({|!Stream__[]|} _) ↪ {|!_~___~-empty|} $A;
rule {|!~-refl|} $A ({|!Stream___∷_|} _ $x $xs) ↪ {|!_~___~-cons|} $A $x $x $xs $xs (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) $A $x) ({|!___♯-4|} $A $x $xs);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-4|} $A $x $l) ↪ {|!~-refl|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $l);
 
symbol {|!~-sym|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_~_|} A x y) (λ _0, ({|!_~_|} A y x)))))))));
symbol {|!___♯-5|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!x'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ {|!l'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x {|!x'|}) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l'|}))) (λ q, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l'|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l)))))))))))))))));
rule {|!~-sym|} $A _ _ ({|!_~___~-empty|} _) ↪ {|!_~___~-empty|} $A;
rule {|!~-sym|} $A ({|!Stream___∷_|} _ $x1 $l) ({|!Stream___∷_|} _ ${|!x'|} ${|!l'|}) ({|!_~___~-cons|} _ _ _ _ _ $x0 $x) ↪ {|!_~___~-cons|} $A ${|!x'|} $x1 ${|!l'|} $l (eqaux.sym $A $x1 ${|!x'|} $x0) ({|!___♯-5|} $A $x1 $l ${|!x'|} ${|!l'|} $x0 $x);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-5|} $A $x $l ${|!x'|} ${|!l'|} $p $q) ↪ {|!~-sym|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l'|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) ({|!_~_|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l'|})) $q);
 
symbol {|!~-trans|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_~_|} A x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_~_|} A y {|!z|}) (λ _0, ({|!_~_|} A x {|!z|})))))))))))));
symbol {|!___♯-6|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!x'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ {|!l'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!x''|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream A)) (λ {|!l''|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x {|!x'|}) (λ p, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l'|}))) (λ q, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A {|!x'|} {|!x''|}) (λ {|!p'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l'|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l''|}))) (λ {|!q'|}, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream A) {|!l''|})))))))))))))))))))))))));
rule {|!~-trans|} $A _ _ _ ({|!_~___~-empty|} _) ({|!_~___~-empty|} _) ↪ {|!_~___~-empty|} $A;
rule {|!~-trans|} $A ({|!Stream___∷_|} _ $x3 $l) ({|!Stream___∷_|} _ ${|!x'|} ${|!l'|}) ({|!Stream___∷_|} _ $x4 $xs) ({|!_~___~-cons|} _ _ _ _ _ $x2 $x1) ({|!_~___~-cons|} _ _ _ _ _ $x0 $x) ↪ {|!_~___~-cons|} $A $x3 $x4 $l $xs (eqaux.trans $A $x3 ${|!x'|} $x4 $x2 $x0) ({|!___♯-6|} $A $x3 $l ${|!x'|} ${|!l'|} $x4 $xs $x2 $x1 $x0 $x);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-6|} $A $x $l ${|!x'|} ${|!l'|} ${|!x''|} ${|!l''|} $p $q ${|!p'|} ${|!q'|}) ↪ {|!~-trans|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l'|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l''|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) ({|!_~_|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) $l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l'|})) $q) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) ({|!_~_|} $A (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l'|}) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream $A) ${|!l''|})) ${|!q'|});
 
symbol {|!_⊕_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (Stream Agda__Builtin__Nat.Nat)))));
symbol {|!___♯-7|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ {|!x'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ {|!l'|}, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat))))))))));
rule {|!_⊕_|} ({|!Stream__[]|} _) $x ↪ {|!Stream__[]|} Agda__Builtin__Nat.Nat;
rule {|!_⊕_|} ({|!Stream___∷_|} _ $x $xs) ({|!Stream__[]|} _) ↪ {|!Stream__[]|} Agda__Builtin__Nat.Nat;
rule {|!_⊕_|} ({|!Stream___∷_|} _ $x0 $xs0) ({|!Stream___∷_|} _ $x $xs) ↪ {|!Stream___∷_|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} $x0 $x) ({|!___♯-7|} $x0 $xs0 $x $xs);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-7|} $x $l ${|!x'|} ${|!l'|}) ↪ {|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) ${|!l'|});
 
symbol {|!⊕-trans|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ l1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ l2, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ l3, ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} ({|!_⊕_|} l1 l2) l3) ({|!_⊕_|} l1 ({|!_⊕_|} l2 l3)))))))));
symbol {|!___♯-8|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x2, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l2, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x3, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l3, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} ({|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l1) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l2)) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l3)) ({|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l1) ({|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l2) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l3)))))))))))))))));
rule {|!⊕-trans|} ({|!Stream__[]|} _) $l2 $l3 ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-trans|} ({|!Stream___∷_|} _ $x $xs) ({|!Stream__[]|} _) $l3 ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-trans|} ({|!Stream___∷_|} _ $x0 $xs0) ({|!Stream___∷_|} _ $x $xs) ({|!Stream__[]|} _) ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-trans|} ({|!Stream___∷_|} _ $x1 $xs1) ({|!Stream___∷_|} _ $x0 $xs0) ({|!Stream___∷_|} _ $x $xs) ↪ {|!_~___~-cons|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.{|!_+_|} $x1 $x0) $x) (Agda__Builtin__Nat.{|!_+_|} $x1 (Agda__Builtin__Nat.{|!_+_|} $x0 $x)) ({|!___♯-7|} (Agda__Builtin__Nat.{|!_+_|} $x1 $x0) ({|!___♯-7|} $x1 $xs1 $x0 $xs0) $x $xs) ({|!___♯-7|} $x1 $xs1 (Agda__Builtin__Nat.{|!_+_|} $x0 $x) ({|!___♯-7|} $x0 $xs0 $x $xs)) (nataux.{|!+-assoc|} $x1 $x0 $x) ({|!___♯-8|} $x1 $xs1 $x0 $xs0 $x $xs);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-8|} $x1 $l1 $x2 $l2 $x3 $l3) ↪ {|!⊕-trans|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l1) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l2) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l3);
 
symbol {|!⊕-com|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ l, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ k, ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} l k) ({|!_⊕_|} k l))))));
symbol {|!___♯-9|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l1, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ x2, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l2, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l1) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l2)) ({|!_⊕_|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l2) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l1))))))))))));
rule {|!⊕-com|} ({|!Stream__[]|} _) ({|!Stream__[]|} _) ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-com|} ({|!Stream__[]|} _) ({|!Stream___∷_|} _ $x $xs) ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-com|} ({|!Stream___∷_|} _ $x $xs) ({|!Stream__[]|} _) ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!⊕-com|} ({|!Stream___∷_|} _ $x0 $xs0) ({|!Stream___∷_|} _ $x $xs) ↪ {|!_~___~-cons|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} $x0 $x) (Agda__Builtin__Nat.{|!_+_|} $x $x0) ({|!___♯-7|} $x0 $xs0 $x $xs) ({|!___♯-7|} $x $xs $x0 $xs0) (nataux.{|!+-com|} $x0 $x) ({|!___♯-9|} $x0 $xs0 $x $xs);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-9|} $x1 $l1 $x2 $l2) ↪ {|!⊕-com|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l1) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l2);
 
symbol {|!0-⊕|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ l, ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} zeros l) l)));
symbol {|!___♯-10|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat)) (λ l, (Agda__Builtin__Coinduction.{|!∞|} (s 0ₙ z) ({|!_~_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} zeros (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l)) (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) l)))))));
rule {|!0-⊕|} ({|!Stream__[]|} _) ↪ {|!_~___~-empty|} Agda__Builtin__Nat.Nat;
rule {|!0-⊕|} ({|!Stream___∷_|} _ $x $xs) ↪ {|!_~___~-cons|} Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} Agda__Builtin__Nat.Nat__zero $x) $x ({|!___♯-7|} Agda__Builtin__Nat.Nat__zero {|!___♯-0|} $x $xs) $xs (Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.{|!_+_|} Agda__Builtin__Nat.Nat__zero $x)) ({|!___♯-10|} $x $xs);
 
rule Agda__Builtin__Coinduction.{|!♭|} _ _ ({|!___♯-10|} $n $l) ↪ {|!0-⊕|} (Agda__Builtin__Coinduction.{|!♭|} (s 0ₙ z) (Stream Agda__Builtin__Nat.Nat) $l);
 
