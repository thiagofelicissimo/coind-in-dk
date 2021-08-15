require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

require tests.Agda__Builtin__Bool as Agda__Builtin__Bool;
require tests.Agda__Builtin__Equality as Agda__Builtin__Equality;
symbol not : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool));
rule not Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Bool.Bool__true;
rule not Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Bool.Bool__false;
 
symbol {|!_∨_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool))));
rule {|!_∨_|} Agda__Builtin__Bool.Bool__false $x ↪ $x;
rule {|!_∨_|} Agda__Builtin__Bool.Bool__true $x ↪ Agda__Builtin__Bool.Bool__true;
 
symbol {|!_∧_|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, Agda__Builtin__Bool.Bool))));
rule {|!_∧_|} Agda__Builtin__Bool.Bool__false $x ↪ Agda__Builtin__Bool.Bool__false;
rule {|!_∧_|} Agda__Builtin__Bool.Bool__true $x ↪ $x;
 
symbol if_then_else_ : El (set (s (sₙ 0ₙ) z)) (⇝ (set (s (sₙ 0ₙ) z)) (set (s 0ₙ z)) (⋄ (set (s 0ₙ z))) (λ A, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) A (λ _0, A))))))));
rule if_then_else_ $A Agda__Builtin__Bool.Bool__false $x0 $x ↪ $x;
rule if_then_else_ $A Agda__Builtin__Bool.Bool__true $x0 $x ↪ $x0;
 
symbol {|!∨-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ c, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} ({|!_∨_|} a b) c) ({|!_∨_|} a ({|!_∨_|} b c)))))))));
rule {|!∨-assoc|} Agda__Builtin__Bool.Bool__false $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} ({|!_∨_|} Agda__Builtin__Bool.Bool__false $b) $c);
rule {|!∨-assoc|} Agda__Builtin__Bool.Bool__true $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} ({|!_∨_|} Agda__Builtin__Bool.Bool__true $b) $c);
 
symbol {|!∧-assoc|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ c, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} ({|!_∧_|} a b) c) ({|!_∧_|} a ({|!_∧_|} b c)))))))));
rule {|!∧-assoc|} Agda__Builtin__Bool.Bool__false $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} ({|!_∧_|} Agda__Builtin__Bool.Bool__false $b) $c);
rule {|!∧-assoc|} Agda__Builtin__Bool.Bool__true $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} ({|!_∧_|} Agda__Builtin__Bool.Bool__true $b) $c);
 
symbol {|!∨-comm|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} a b) ({|!_∨_|} b a))))));
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false);
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__true);
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__false);
rule {|!∨-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true);
 
symbol {|!∨-cong|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!a'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!b'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool a {|!a'|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool b {|!b'|}) (λ _0, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} a b) ({|!_∨_|} {|!a'|} {|!b'|}))))))))))))));
rule {|!∨-cong|} _ _ $a $b (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} $a $b);
 
symbol {|!∧-comm|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} a b) ({|!_∧_|} b a))))));
rule {|!∧-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false);
rule {|!∧-comm|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__true);
rule {|!∧-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__false);
rule {|!∧-comm|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true);
 
symbol {|!∨-idem|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} a a) a)));
rule {|!∨-idem|} Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false);
rule {|!∨-idem|} Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true);
 
symbol {|!∧-idem|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} a a) a)));
rule {|!∧-idem|} Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__false Agda__Builtin__Bool.Bool__false);
rule {|!∧-idem|} Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__true Agda__Builtin__Bool.Bool__true);
 
symbol {|!∧-cong|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!a'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ {|!b'|}, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool a {|!a'|}) (λ _0, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool b {|!b'|}) (λ _0, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} a b) ({|!_∧_|} {|!a'|} {|!b'|}))))))))))))));
rule {|!∧-cong|} _ _ $a $b (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) (Agda__Builtin__Equality.{|!_≡___refl|} _ _ _) ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} $a $b);
 
symbol {|!∨-∧-dist|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ c, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} a ({|!_∧_|} b c)) ({|!_∧_|} ({|!_∨_|} a b) ({|!_∨_|} a c)))))))));
rule {|!∨-∧-dist|} Agda__Builtin__Bool.Bool__false $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__false ({|!_∧_|} $b $c));
rule {|!∨-∧-dist|} Agda__Builtin__Bool.Bool__true $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__true ({|!_∧_|} $b $c));
 
symbol {|!∧-∨-dist|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ b, (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ c, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} a ({|!_∨_|} b c)) ({|!_∨_|} ({|!_∧_|} a b) ({|!_∧_|} a c)))))))));
rule {|!∧-∨-dist|} Agda__Builtin__Bool.Bool__false $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__false ({|!_∨_|} $b $c));
rule {|!∧-∨-dist|} Agda__Builtin__Bool.Bool__true $b $c ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__true ({|!_∨_|} $b $c));
 
symbol {|!∨-comp|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} a (not a)) Agda__Builtin__Bool.Bool__true)));
rule {|!∨-comp|} Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__false (not Agda__Builtin__Bool.Bool__false));
rule {|!∨-comp|} Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∨_|} Agda__Builtin__Bool.Bool__true (not Agda__Builtin__Bool.Bool__true));
 
symbol {|!∧-comp|} : El (set (s 0ₙ z)) (⇝ (set (s 0ₙ z)) (set (s 0ₙ z)) Agda__Builtin__Bool.Bool (λ a, (Agda__Builtin__Equality.{|!_≡_|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} a (not a)) Agda__Builtin__Bool.Bool__false)));
rule {|!∧-comp|} Agda__Builtin__Bool.Bool__false ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__false (not Agda__Builtin__Bool.Bool__false));
rule {|!∧-comp|} Agda__Builtin__Bool.Bool__true ↪ Agda__Builtin__Equality.{|!_≡___refl|} (s 0ₙ z) Agda__Builtin__Bool.Bool ({|!_∧_|} Agda__Builtin__Bool.Bool__true (not Agda__Builtin__Bool.Bool__true));
 
