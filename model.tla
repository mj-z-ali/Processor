------------------------------- MODULE model -------------------------------
EXTENDS Integers, Sequences, TLAPS

bv4 == [ 0..3 -> {TRUE,FALSE} ]

xor[b_0, b_1 \in {TRUE,FALSE}]  == (b_0 /\ ~b_1) \/ (~b_0 /\ b_1)

cmp_bv4[bv4_0, bv4_1 \in bv4] ==  ~xor[bv4_0[0], bv4_1[0]] /\ 
                                  ~xor[bv4_0[1], bv4_1[1]] /\  
                                  ~xor[bv4_0[2], bv4_1[2]] /\ 
                                  ~xor[bv4_0[3], bv4_1[3]]



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
\* Last modified Mon Nov 07 07:10:53 CST 2022 by mjhomefolder
\* Created Thu Nov 03 00:11:52 CDT 2022 by mjhomefolder
