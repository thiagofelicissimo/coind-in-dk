require open AgdaTheory.noEta.Base;
require open AgdaTheory.Levels;

constant symbol {|!TYPE__⊤|} : TYPE;
constant symbol {|!⊤|} : El (set (s (sₙ 0ₙ) z)) (⋄ (set (s 0ₙ z)));
rule El _ {|!⊤|} ↪ {|!TYPE__⊤|};
constant symbol tt : El (set (s 0ₙ z)) {|!⊤|};


