------------------------------- MODULE model -------------------------------
EXTENDS Integers, Naturals, Sequences, TLC, TLAPS

CONSTANT N

ASSUME NNAT == N \in Nat



BVN == [0..N -> {TRUE, FALSE}]

ANDN == [f,g \in BVN |-> [i \in 0..N |-> f[i] /\ g[i]]]

ANDN2(f,g) == [i \in 0..N |-> f[i] /\ g[i]]

ORN == [f,g \in BVN |-> [i \in 0..N |-> f[i] \/ g[i]]]

EXPANDN == [b \in {TRUE, FALSE} |-> [i \in 0..N |-> b]]

bv4 == [0..3 -> {TRUE,FALSE}]


AND4 == [f,g \in bv4 |-> [i \in 0..3 |-> (i=0 /\ f[0] /\ g[0]) \/ 
                                         (i=1 /\ f[1] /\ g[1]) \/
                                         (i=2 /\ f[2] /\ g[2]) \/
                                         (i=3 /\ f[3] /\ g[3])     ]]
                                         
OR4 ==  [f,g \in bv4 |-> [i \in 0..3 |-> (i=0 /\ (f[0] \/ g[0])) \/ 
                                         (i=1 /\ (f[1] \/ g[1])) \/
                                         (i=2 /\ (f[2] \/ g[2])) \/
                                         (i=3 /\ (f[3] \/ g[3]))     ]]                                       
                     
EXPAND4 == [b \in {TRUE, FALSE} |-> [i \in 0..3 |-> b] ]                                       
                                         

r11 == [x \in {TRUE,  FALSE} |-> (x /\ [ k \in 0..3 |-> FALSE]) \/ (~x /\ [ k \in 0..3 |-> TRUE]) ]

xor[b_0, b_1 \in {TRUE,FALSE}]  == (b_0 /\ ~b_1) \/ (~b_0 /\ b_1)

cmp_bv4[bv4_0, bv4_1 \in bv4] ==  ~xor[bv4_0[0], bv4_1[0]] /\ 
                                  ~xor[bv4_0[1], bv4_1[1]] /\  
                                  ~xor[bv4_0[2], bv4_1[2]] /\ 
                                  ~xor[bv4_0[3], bv4_1[3]]



THEOREM ANDN2_CORRECT==
    \A f,g \in BVN : \A i \in 0..N :
    ANDN2(f,g)[i] <=> f[i] /\ g[i]
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 TAKE i \in 0..N
    <1>3 ANDN2(f,g)[i] <=> f[i] /\ g[i]
        BY DEF BVN, ANDN2
    <1> QED BY <1>3
    
THEOREM ANDN2_EQ_ANDN ==
    \A f,g \in BVN : 
    ANDN2(f,g) = ANDN[f,g]
PROOF 
    <1>1 TAKE f,g \in BVN
    <1>2 ANDN2(f,g) = ANDN[f,g]
        BY DEF ANDN2, ANDN
    <1>3 QED

THEOREM ANDN_CORRECT==
    \A f,g \in BVN : \A i \in 0..N : 
    ANDN[f,g][i] <=> f[i] /\ g[i]
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 TAKE i \in 0..N
    <1>3 ANDN[f,g][i] <=> f[i] /\ g[i]
        BY DEF BVN, ANDN
    <1> QED BY <1>3
    
THEOREM OR4_CORRECT==
    \A f,g \in bv4 : OR4[f,g] <=> \A i \in 0..3 : f[i] \/ g[i]
    
THEOREM EXPAND4_CORRECT ==
    \A b \in {TRUE, FALSE} : EXPAND4[b] <=> \A i \in 0..3, f \in bv4 : f[i] = b

THEOREM NOT_XOR_EQ ==
    ASSUME \A a,b \in {TRUE, FALSE} : 
           xor[a,b] = ((a /\ ~b) \/ (~a /\ b))
           PROVE  \A a, b \in {TRUE, FALSE} : ~xor[a,b] <=> (a=b)
           
           
PROOF
    <1>1 TAKE a,b \in {TRUE, FALSE}
    <1>2 ASSUME a /= b PROVE xor[a,b]
        <2>1 xor[a,b] = ((a /\ ~b) \/ (~a /\ b))
            OBVIOUS
        <2>2 (a /= b) => ((a /\ ~b) \/ (~a /\ b))
            OBVIOUS
        <2>3 ((a /\ ~b) \/ (~a /\ b)) = TRUE
            BY <2>2, <1>2
        <2>4 QED BY <2>1, <2>3

    <1>3 QED BY <1>2


   
 (*       
    
  THEOREM NOT_XOR_EQ ==
    ASSUME NEW a \in {TRUE, FALSE},
           NEW b \in {TRUE, FALSE},
           xor[a,b] = ((a /\ ~b) \/ (~a /\ b))
          \* PROVE \A x,y \in {TRUE, FALSE} : ~xor[x,y] => (x=y)
           PROVE  ~xor[a,b] => (a=b)
           
           
PROOF
    <1>1 ASSUME a /= b PROVE xor[a,b]
        <2>1 xor[a,b] = ((a /\ ~b) \/ (~a /\ b))
            OBVIOUS
        <2>2 (a /= b) => ((a /\ ~b) \/ (~a /\ b))
            OBVIOUS
        <2>3 ((a /\ ~b) \/ (~a /\ b)) = TRUE
            BY <2>2, <1>1
        <2>4 ((a /\ ~b) \/ (~a /\ b)) = xor[a,b]
            BY <2>1
        <2>5 QED BY <2>1, <2>3

    <1> QED BY <1>1  *)
    
\*******************************************************************************
\* THEOREM CMP_CORRECT == \A x,y \in bv4 : cmp_bv4[x,y] => x[0]=y[0] /\ 
\*                                                        x[1]=y[1] /\ 
\*                                                        x[2]=y[2] /\ 
\*                                                        x[3]=y[3]                                               
\*PROOF 
\*    <1>  USE DEF cmp_bv4, xor, bv4
\*   <1>1 TAKE x,y \in bv4
\*   <1>2 cmp_bv4[x,y] /\ x=y BY DEF xor
\*    <1>3 QED BY <1>2                                                         
    
                                                      
\*PROOF
\*    <1>1. TAKE x,y \in bv4
\*    <1>2. cmp_bv4[x,y] /\ x[0]=y[0] /\ x[1]=y[1] /\ x[2]=y[2] /\ x[3]=y[3] BY DEF cmp_bv4, xor
\*    <1>3. QED BY <1>1

\*******************************************************************************
=============================================================================
\* Modification History
\* Last modified Thu Nov 10 06:29:41 CST 2022 by mjhomefolder
\* Created Thu Nov 03 00:11:52 CDT 2022 by mjhomefolder
