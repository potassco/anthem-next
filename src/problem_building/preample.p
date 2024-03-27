tff(type, type, object: $tType).
tff(type, type, f__integer__: ($int) > object).
tff(type, type, f__symbolic__: ($i) > object).
tff(type, type, c__infimum__: object).
tff(type, type, c__supremum__: object).
tff(type, type, p__is_integer__: (object) > $o).
tff(type, type, p__is_symbolic__: (object) > $o).
tff(type, type, p__less_equal__: (object * object) > $o).
tff(type, type, p__less__: (object * object) > $o).
tff(type, type, p__greater_equal__: (object * object) > $o).
tff(type, type, p__greater__: (object * object) > $o).
tff(axiom, axiom, ![X: object]: (p__is_integer__(X) <=> (?[N: $int]: (X = f__integer__(N))))).
tff(axiom, axiom, ![X1: object]: (p__is_symbolic__(X1) <=> (?[X2: $i]: (X1 = f__symbolic__(X2))))).
tff(axiom, axiom, ![X: object]: ((X = c__infimum__) | p__is_integer__(X) | p__is_symbolic__(X) | (X = c__supremum__))).
tff(axiom, axiom, ![N1: $int, N2: $int]: ((f__integer__(N1) = f__integer__(N2)) <=> (N1 = N2))).
tff(axiom, axiom, ![S1: $i, S2: $i]: ((f__symbolic__(S1) = f__symbolic__(S2)) <=> (S1 = S2))).
tff(axiom, axiom, ![N1: $int, N2: $int]: (p__less_equal__(f__integer__(N1), f__integer__(N2)) <=> $lesseq(N1, N2))).
tff(axiom, axiom, ![X1: object, X2: object]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X1)) => (X1 = X2))).
tff(axiom, axiom, ![X1: object, X2: object, X3: object]: ((p__less_equal__(X1, X2) & p__less_equal__(X2, X3)) => p__less_equal__(X1, X3))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__less_equal__(X1, X2) | p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__less__(X1, X2) <=> (p__less_equal__(X1, X2) & (X1 != X2)))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__greater_equal__(X1, X2) <=> p__less_equal__(X2, X1))).
tff(axiom, axiom, ![X1: object, X2: object]: (p__greater__(X1, X2) <=> (p__less_equal__(X2, X1) & (X1 != X2)))).
tff(axiom, axiom, ![N: $int]: p__less__(c__infimum__, f__integer__(N))).
tff(axiom, axiom, ![N: $int, S: $i]: p__less__(f__integer__(N), f__symbolic__(S))).
tff(axiom, axiom, ![S: $i]: p__less__(f__symbolic__(S), c__supremum__)).
