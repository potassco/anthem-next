forall V1 (sqrtb(V1) <-> exists I (V1 = I and (
    exists Z Z1 (Z = I and 
        exists I$i J$i K$i (I$i = 1 and J$i = b and Z1 = K$i and I$i <= K$i <= J$i) 
        and Z = Z1
    ) and 
    exists Z Z1 (
        exists I1$i J$i (Z = I1$i * J$i and I1$i = I and J$i = I) 
        and Z1 = b and Z <= Z1
    ) and 
    exists Z Z1 (
        exists I1$i J$i (
            Z = I1$i * J$i and 
            exists I2$i J$i (I1$i = I2$i + J$i and I2$i = I and J$i = 1) and 
            exists I1$i J1$i (J$i = I1$i + J1$i and I1$i = I and J1$i = 1)
        ) 
        and Z1 = b and Z > Z1
    )
)))



Formula after basic simplification: 
    forall V1 (sqrtb(V1) <-> exists I (V1 = I and (
        exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 1 and J$i = b and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and 
        exists Z Z1 (exists I1$i J$i (Z = I1$i * J$i and I1$i = I and J$i = I) and Z1 = b and Z <= Z1) and 
        exists Z Z1 (exists I1$i J$i (Z = I1$i * J$i and 
            exists I2$i J$i (I1$i = I2$i + J$i and I2$i = I and J$i = 1) and exists I1$i J1$i (J$i = I1$i + J1$i and I1$i = I and J1$i = 1)) and Z1 = b and Z > Z1))))
    
Formula after redundant quantifier elimination: 
    forall V1 (sqrtb(V1) <-> exists Z1 (exists J$i K$i (J$i = b and Z1 = K$i and 1 <= K$i <= J$i) and V1 = Z1) and exists Z (exists I1$i J$i (Z = I1$i * J$i and I1$i = V1 and J$i = V1) and Z <= b) and exists Z (exists I1$i J$i (Z = I1$i * J$i and exists I2$i (I1$i = I2$i + 1 and I2$i = V1) and exists I1$i (J$i = I1$i + 1 and I1$i = V1)) and Z > b))

Formula after extending quantifier scope: 
    forall V1 (sqrtb(V1) <-> exists Z1 (exists J$i K$i (J$i = b and Z1 = K$i and 1 <= K$i <= J$i and V1 = Z1) and exists Z exists I1$i J$i (Z = I1$i * J$i and I1$i = V1 and J$i = V1 and Z <= b) and exists Z exists I1$i J$i (exists I2$i (Z = I1$i * J$i and (I1$i = I2$i + 1 and I2$i = V1) and exists I1$i (J$i = I1$i + 1 and I1$i = V1)) and Z > b)))
    
Formula after nested quantifier joining: 
    forall V1 (sqrtb(V1) <-> exists Z1 (exists J$i K$i (J$i = b and Z1 = K$i and 1 <= K$i <= J$i and V1 = Z1) and exists I1$i J$i Z (Z = I1$i * J$i and I1$i = V1 and J$i = V1 and Z <= b) and exists I1$i J$i Z (exists I2$i (Z = I1$i * J$i and (I1$i = I2$i + 1 and I2$i = V1) and exists I1$i (J$i = I1$i + 1 and I1$i = V1)) and Z > b)))