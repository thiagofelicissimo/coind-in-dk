require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
require tests.Agda__Builtin__List as Agda__Builtin__List;
require tests.Agda__Builtin__Nat as Agda__Builtin__Nat;
require tests.eqaux as eqaux;
require tests.nataux as nataux;
constant symbol TYPE__Stream : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), TYPE;
constant symbol Stream : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⋄ (set (s 0ₙ z)))));
rule El _ (Stream $A) ↪ TYPE__Stream $A;
constant symbol {|!Stream'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ hd, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ tl, (Stream A)))))));
symbol Stream__hd : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ r, A))));
symbol Stream__tl : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ r, (Stream A)))));


rule Stream__hd $A ({|!Stream'constructor|} _ $hd $tl) ↪ $hd;
 
rule Stream__tl $A ({|!Stream'constructor|} _ $hd $tl) ↪ $tl;
 
symbol nth : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, A))))));
rule nth $A Agda__Builtin__Nat.Nat__zero $x ↪ Stream__hd $A $x;
rule nth $A (Agda__Builtin__Nat.Nat__suc $x0) $x ↪ nth $A $x0 (Stream__tl $A $x);
 
symbol zeros : El (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat);
rule Stream__hd _ zeros ↪ Agda__Builtin__Nat.Nat__zero;
rule Stream__tl _ zeros ↪ zeros;
 
symbol natStream : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (Stream Agda__Builtin__Nat.Nat)));
rule Stream__hd _ (natStream $n) ↪ $n;
rule Stream__tl _ (natStream $n) ↪ natStream (Agda__Builtin__Nat.Nat__suc $n);
 
symbol {|!list-to-stream|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ {|!end|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (Stream A)))))));
rule Stream__hd _ ({|!list-to-stream|} $A ${|!end|} (Agda__Builtin__List.{|!List__[]|} _ _)) ↪ ${|!end|};
rule Stream__hd _ ({|!list-to-stream|} $A ${|!end|} (Agda__Builtin__List.{|!List___∷_|} _ _ $x0 $x)) ↪ $x0;
rule Stream__tl _ ({|!list-to-stream|} $A ${|!end|} (Agda__Builtin__List.{|!List__[]|} _ _)) ↪ {|!list-to-stream|} $A ${|!end|} (Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) $A);
rule Stream__tl _ ({|!list-to-stream|} $A ${|!end|} (Agda__Builtin__List.{|!List___∷_|} _ _ $x0 $x)) ↪ {|!list-to-stream|} $A ${|!end|} $x;
 
symbol {|!stream-to-list|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Agda__Builtin__List.List (s 0ₙ z) A)))))));
rule {|!stream-to-list|} $A Agda__Builtin__Nat.Nat__zero $x ↪ Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) $A;
rule {|!stream-to-list|} $A (Agda__Builtin__Nat.Nat__suc $x0) $x ↪ Agda__Builtin__List.{|!List___∷_|} (s 0ₙ z) $A (Stream__hd $A $x) ({|!stream-to-list|} $A $x0 (Stream__tl $A $x));
 
symbol append : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) A) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Stream A)))))));
rule append $A (Agda__Builtin__List.{|!List__[]|} _ _) $x ↪ $x;
rule Stream__hd _ (append $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x) ↪ $x1;
rule Stream__tl _ (append $A (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x) ↪ append $A $x0 $x;
 
symbol {|!stream-fare-comp'|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream (Stream A)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) (Stream A)) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__List.List (s 0ₙ z) (Stream A)) (λ _0, (Stream A)))))))));
rule Stream__hd _ ({|!stream-fare-comp'|} $A $x0 (Agda__Builtin__List.{|!List__[]|} _ _) $x) ↪ Stream__hd $A (Stream__hd (Stream $A) $x0);
rule Stream__hd _ ({|!stream-fare-comp'|} $A $x2 (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x) ↪ Stream__hd $A $x1;
rule Stream__tl _ ({|!stream-fare-comp'|} $A $x0 (Agda__Builtin__List.{|!List__[]|} _ _) $x) ↪ {|!stream-fare-comp'|} $A (Stream__tl (Stream $A) $x0) $x (Agda__Builtin__List.{|!List___∷_|} (s 0ₙ z) (Stream $A) (Stream__tl $A (Stream__hd (Stream $A) $x0)) (Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) (Stream $A)));
rule Stream__tl _ ({|!stream-fare-comp'|} $A $x2 (Agda__Builtin__List.{|!List___∷_|} _ _ $x1 $x0) $x) ↪ {|!stream-fare-comp'|} $A $x2 $x0 (Agda__Builtin__List.{|!List___∷_|} (s 0ₙ z) (Stream $A) (Stream__tl $A $x1) $x);
 
symbol {|!stream-fare-comp|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream (Stream A)) (λ _0, (Stream A)))));
rule {|!stream-fare-comp|} $A $x ↪ {|!stream-fare-comp'|} $A $x (Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) (Stream $A)) (Agda__Builtin__List.{|!List__[]|} (s 0ₙ z) (Stream $A));
 
symbol natStreamStream : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ _0, (Stream (Stream Agda__Builtin__Nat.Nat))));
rule Stream__hd _ (natStreamStream $x) ↪ natStream $x;
rule Stream__tl _ (natStreamStream $x) ↪ natStreamStream (Agda__Builtin__Nat.Nat__suc $x);
 
constant symbol {|!TYPE___≈_|} : Π A : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))), Π xs : El (set (s 0ₙ z)) (Stream A), Π ys : El (set (s 0ₙ z)) (Stream A), TYPE;
constant symbol {|!_≈_|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Stream A) (λ xs, (⇝ (set (s 0ₙ z)) (set (s (sₙ 0ₙ) z)) (Stream A) (λ ys, (⋄ (set (s 0ₙ z)))))))));
rule El _ ({|!_≈_|} $A $xs $ys) ↪ {|!TYPE___≈_|} $A $xs $ys;
symbol {|!_≈___hd-≡|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ xs, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ ys, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A xs ys) (λ r, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A (Stream__hd A xs) (Stream__hd A ys))))))))));
symbol {|!_≈___tl-≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ xs, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ ys, (⇝proj (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A xs ys) (λ r, ({|!_≈_|} A (Stream__tl A xs) (Stream__tl A ys))))))))));
constant symbol {|!_≈_'constructor|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ xs, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ ys, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A (Stream__hd A xs) (Stream__hd A ys)) (λ {|!hd-≡|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A (Stream__tl A xs) (Stream__tl A ys)) (λ {|!tl-≈|}, ({|!_≈_|} A xs ys)))))))))));

rule {|!_≈___hd-≡|} $A $xs $ys ({|!_≈_'constructor|} _ _ _ ${|!hd-≡|} ${|!tl-≈|}) ↪ ${|!hd-≡|};
 
rule {|!_≈___tl-≈|} $A $xs $ys ({|!_≈_'constructor|} _ _ _ ${|!hd-≡|} ${|!tl-≈|}) ↪ ${|!tl-≈|};
 

symbol {|!refl-≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!s|}, ({|!_≈_|} A {|!s|} {|!s|})))));
rule {|!_≈___hd-≡|} _ _ _ ({|!refl-≈|} $A ${|!s|}) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) $A (Stream__hd $A ${|!s|});
rule {|!_≈___tl-≈|} _ _ _ ({|!refl-≈|} $A ${|!s|}) ↪ {|!refl-≈|} $A (Stream__tl $A ${|!s|});
 
symbol {|!sym-≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!s|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!s'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A {|!s|} {|!s'|}) (λ _0, ({|!_≈_|} A {|!s'|} {|!s|})))))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!sym-≈|} $A ${|!s|} ${|!s'|} $x) ↪ eqaux.sym $A (Stream__hd $A ${|!s|}) (Stream__hd $A ${|!s'|}) ({|!_≈___hd-≡|} $A ${|!s|} ${|!s'|} $x);
rule {|!_≈___tl-≈|} _ _ _ ({|!sym-≈|} $A ${|!s|} ${|!s'|} $x) ↪ {|!sym-≈|} $A (Stream__tl $A ${|!s|}) (Stream__tl $A ${|!s'|}) ({|!_≈___tl-≈|} $A ${|!s|} ${|!s'|} $x);
 
symbol {|!trans-≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ {|!z|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A x y) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) ({|!_≈_|} A y {|!z|}) (λ _0, ({|!_≈_|} A x {|!z|})))))))))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!trans-≈|} $A $x1 $y ${|!z|} $x0 $x) ↪ eqaux.trans $A (Stream__hd $A $x1) (Stream__hd $A $y) (Stream__hd $A ${|!z|}) ({|!_≈___hd-≡|} $A $x1 $y $x0) ({|!_≈___hd-≡|} $A $y ${|!z|} $x);
rule {|!_≈___tl-≈|} _ _ _ ({|!trans-≈|} $A $x1 $y ${|!z|} $x0 $x) ↪ {|!trans-≈|} $A (Stream__tl $A $x1) (Stream__tl $A $y) (Stream__tl $A ${|!z|}) ({|!_≈___tl-≈|} $A $x1 $y $x0) ({|!_≈___tl-≈|} $A $y ${|!z|} $x);
 
symbol {|!≡to≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) (Stream A) x y) (λ _0, ({|!_≈_|} A x y)))))))));
rule {|!≡to≈|} $A $x _ (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) ↪ {|!refl-≈|} $A $x;
 
symbol {|!cong-≈|} : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ B, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (Stream B))) (λ f, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) A x y) (λ _0, ({|!_≈_|} B (f x) (f y))))))))))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!cong-≈|} $A $B $x0 $y $f $x) ↪ eqaux.cong $A $B $x0 $y (λ x1, Stream__hd $B ($f x1)) $x;
rule {|!_≈___tl-≈|} _ _ _ ({|!cong-≈|} $A $B $x0 $y $f $x) ↪ {|!cong-≈|} (Stream $B) $B ($f $x0) ($f $y) (λ r, Stream__tl $B r) (eqaux.cong $A (Stream $B) $x0 $y $f $x);
 
symbol {|!_⊕_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (Stream Agda__Builtin__Nat.Nat)))));
rule Stream__hd _ ({|!_⊕_|} $x0 $x) ↪ Agda__Builtin__Nat.{|!_+_|} (Stream__hd Agda__Builtin__Nat.Nat $x0) (Stream__hd Agda__Builtin__Nat.Nat $x);
rule Stream__tl _ ({|!_⊕_|} $x0 $x) ↪ {|!_⊕_|} (Stream__tl Agda__Builtin__Nat.Nat $x0) (Stream__tl Agda__Builtin__Nat.Nat $x);
 
symbol {|!⊕-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ y, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ {|!z|}, ({|!_≈_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} ({|!_⊕_|} x y) {|!z|}) ({|!_⊕_|} x ({|!_⊕_|} y {|!z|})))))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!⊕-assoc|} $x $y ${|!z|}) ↪ nataux.{|!+-assoc|} (Stream__hd Agda__Builtin__Nat.Nat $x) (Stream__hd Agda__Builtin__Nat.Nat $y) (Stream__hd Agda__Builtin__Nat.Nat ${|!z|});
rule {|!_≈___tl-≈|} _ _ _ ({|!⊕-assoc|} $x $y ${|!z|}) ↪ {|!⊕-assoc|} (Stream__tl Agda__Builtin__Nat.Nat $x) (Stream__tl Agda__Builtin__Nat.Nat $y) (Stream__tl Agda__Builtin__Nat.Nat ${|!z|});
 
symbol {|!⊕-com|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ x, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ y, ({|!_≈_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} x y) ({|!_⊕_|} y x))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!⊕-com|} $x $y) ↪ nataux.{|!+-com|} (Stream__hd Agda__Builtin__Nat.Nat $x) (Stream__hd Agda__Builtin__Nat.Nat $y);
rule {|!_≈___tl-≈|} _ _ _ ({|!⊕-com|} $x $y) ↪ {|!⊕-com|} (Stream__tl Agda__Builtin__Nat.Nat $x) (Stream__tl Agda__Builtin__Nat.Nat $y);
 
symbol {|!⊕-zeros|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ x, ({|!_≈_|} Agda__Builtin__Nat.Nat ({|!_⊕_|} zeros x) x)));
rule {|!_≈___hd-≡|} _ _ _ ({|!⊕-zeros|} $x) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Stream__hd Agda__Builtin__Nat.Nat ({|!_⊕_|} zeros $x));
rule {|!_≈___tl-≈|} _ _ _ ({|!⊕-zeros|} $x) ↪ {|!⊕-zeros|} (Stream__tl Agda__Builtin__Nat.Nat $x);
 
symbol tailn : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream A) (λ _0, (Stream A)))))));
rule tailn $A Agda__Builtin__Nat.Nat__zero $x ↪ $x;
rule tailn $A (Agda__Builtin__Nat.Nat__suc $n) $x ↪ Stream__tl $A (tailn $A $n $x);
 
symbol tailNatS : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, ({|!_≈_|} Agda__Builtin__Nat.Nat (tailn Agda__Builtin__Nat.Nat n (natStream Agda__Builtin__Nat.Nat__zero)) (natStream n))));
rule tailNatS Agda__Builtin__Nat.Nat__zero ↪ {|!refl-≈|} Agda__Builtin__Nat.Nat (tailn Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero (natStream Agda__Builtin__Nat.Nat__zero));
rule tailNatS (Agda__Builtin__Nat.Nat__suc $n) ↪ {|!_≈___tl-≈|} Agda__Builtin__Nat.Nat (tailn Agda__Builtin__Nat.Nat $n (natStream Agda__Builtin__Nat.Nat__zero)) (natStream $n) (tailNatS $n);
 
symbol plusS : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ _0, (Stream Agda__Builtin__Nat.Nat)))));
rule Stream__hd _ (plusS $n $x) ↪ Agda__Builtin__Nat.{|!_+_|} $n (Stream__hd Agda__Builtin__Nat.Nat $x);
rule Stream__tl _ (plusS $n $x) ↪ plusS $n (Stream__tl Agda__Builtin__Nat.Nat $x);
 
symbol etaPlusS : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ x, ({|!_≈_|} Agda__Builtin__Nat.Nat x (plusS Agda__Builtin__Nat.Nat__zero x))));
rule {|!_≈___hd-≡|} _ _ _ (etaPlusS $x) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (Stream__hd Agda__Builtin__Nat.Nat $x);
rule {|!_≈___tl-≈|} _ _ _ (etaPlusS $x) ↪ etaPlusS (Stream__tl Agda__Builtin__Nat.Nat $x);
 
symbol {|!plusS+|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Stream Agda__Builtin__Nat.Nat) (λ x, ({|!_≈_|} Agda__Builtin__Nat.Nat (plusS (Agda__Builtin__Nat.{|!_+_|} n m) x) (plusS n (plusS m x)))))))));
rule {|!_≈___hd-≡|} _ _ _ ({|!plusS+|} $n $m $x) ↪ nataux.{|!+-assoc|} $n $m (Stream__hd Agda__Builtin__Nat.Nat $x);
rule {|!_≈___tl-≈|} _ _ _ ({|!plusS+|} $n $m $x) ↪ {|!plusS+|} $n $m (Stream__tl Agda__Builtin__Nat.Nat $x);
 
symbol posNatS2 : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ m, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat n (Stream__tl Agda__Builtin__Nat.Nat (natStream m))) (Agda__Builtin__Nat.Nat__suc (nth Agda__Builtin__Nat.Nat n (natStream m))))))));
rule posNatS2 Agda__Builtin__Nat.Nat__zero $m ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero (Stream__tl Agda__Builtin__Nat.Nat (natStream $m)));
rule posNatS2 (Agda__Builtin__Nat.Nat__suc $n) $m ↪ posNatS2 $n (Agda__Builtin__Nat.Nat__suc $m);
 
symbol posNatS : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ m, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc n) (natStream m)) (nth Agda__Builtin__Nat.Nat n (natStream (Agda__Builtin__Nat.Nat__suc m))))))));
rule posNatS $m $n ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc $n) (natStream $m));
 
symbol {|!posNatS+|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ n, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Nat.Nat (λ m, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat n (natStream m)) (Agda__Builtin__Nat.{|!_+_|} n m))))));
rule {|!posNatS+|} Agda__Builtin__Nat.Nat__zero $m ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat__zero (natStream $m));
rule {|!posNatS+|} (Agda__Builtin__Nat.Nat__suc $n) $m ↪ eqaux.trans Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat (Agda__Builtin__Nat.Nat__suc $n) (natStream $m)) (Agda__Builtin__Nat.Nat__suc (nth Agda__Builtin__Nat.Nat $n (natStream $m))) (Agda__Builtin__Nat.{|!_+_|} (Agda__Builtin__Nat.Nat__suc $n) $m) (posNatS2 $n $m) (eqaux.cong Agda__Builtin__Nat.Nat Agda__Builtin__Nat.Nat (nth Agda__Builtin__Nat.Nat $n (natStream $m)) (Agda__Builtin__Nat.{|!_+_|} $n $m) Agda__Builtin__Nat.Nat__suc ({|!posNatS+|} $n $m));
 
