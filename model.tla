------------------------------- MODULE model -------------------------------
EXTENDS Integers, Naturals, Sequences, TLC, TLAPS

CONSTANT N

ASSUME NNAT == N \in Nat



BVN == [0..N -> {TRUE,FALSE}]

ANDN == [f \in BVN |-> [g \in BVN |-> [i \in 0..N |-> f[i] /\ g[i]]]]

ORN == [f \in BVN |-> [g \in BVN |-> [i \in 0..N |-> f[i] \/ g[i]]]]

EXPANDN == [b \in {TRUE,FALSE} |-> [i \in 0..N |-> b]]
                                                                                                                     
r11 == [x \in {TRUE,FALSE} |-> (x /\ [ k \in 0..3 |-> FALSE]) \/ (~x /\ [ k \in 0..3 |-> TRUE]) ]

XORN == [f \in BVN |-> [g \in BVN |-> [i \in 0..N |-> ((f[i] /\ ~g[i]) \/ (~f[i] /\ g[i]))]]]

CMP32 == [f \in BVN |-> [g \in BVN |->  
                                       ~XORN[f][g][0]  /\ ~XORN[f][g][1]  /\ ~XORN[f][g][2]  /\ 
                                       ~XORN[f][g][3]  /\ ~XORN[f][g][4]  /\ ~XORN[f][g][5]  /\ 
                                       ~XORN[f][g][6]  /\ ~XORN[f][g][7]  /\ ~XORN[f][g][8]  /\
                                       ~XORN[f][g][9]  /\ ~XORN[f][g][10] /\ ~XORN[f][g][11] /\
                                       ~XORN[f][g][12] /\ ~XORN[f][g][13] /\ ~XORN[f][g][14] /\
                                       ~XORN[f][g][15] /\ ~XORN[f][g][16] /\ ~XORN[f][g][17] /\
                                       ~XORN[f][g][18] /\ ~XORN[f][g][19] /\ ~XORN[f][g][20] /\
                                       ~XORN[f][g][21] /\ ~XORN[f][g][22] /\ ~XORN[f][g][23] /\
                                       ~XORN[f][g][24] /\ ~XORN[f][g][25] /\ ~XORN[f][g][26] /\
                                       ~XORN[f][g][27] /\ ~XORN[f][g][28] /\ ~XORN[f][g][29] /\
                                       ~XORN[f][g][30] /\ ~XORN[f][g][31] ]]

THEOREM ANDN_CORRECT==
    \A f,g \in BVN : \A i \in 0..N : 
    ANDN[f][g][i] <=> f[i] /\ g[i]
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 TAKE i \in 0..N
    <1>3 ANDN[f][g][i] <=> f[i] /\ g[i]
        BY DEF BVN, ANDN
    <1> QED BY <1>3
    
THEOREM ORN_CORRECT==
    \A f,g \in BVN : \A i \in 0..N : 
    ORN[f][g][i] <=> f[i] \/ g[i]
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 TAKE i \in 0..N
    <1>3 ORN[f][g][i] <=> f[i] \/ g[i]
        BY DEF BVN, ORN
    <1> QED BY <1>3
    
THEOREM EXPANDN_CORRECT ==
    \A b \in {TRUE,FALSE} : \A i \in 0..N : 
    EXPANDN[b][i] <=> b
PROOF
    <1>1 TAKE b \in {TRUE,FALSE}
    <1>2 TAKE i \in 0..N
    <1>3 EXPANDN[b][i] <=> b
        BY  DEF EXPANDN
    <1> QED BY <1>3

THEOREM NOT_XORN_EQ ==
    \A f,g \in BVN : \A i \in 0..N :
    ~XORN[f][g][i] <=> f[i]=g[i]
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 TAKE i \in 0..N
    <1>3 ASSUME f[i] /= g[i] PROVE XORN[f][g][i]
        <2>1 f[i] \in {TRUE,FALSE}
            BY DEF BVN
        <2>2 g[i] \in {TRUE,FALSE}
            BY DEF BVN
        <2>3 (f[i] /= g[i]) => ((f[i] /\ ~g[i]) \/ (~f[i] /\ g[i]))
            BY <2>1, <2>2
        <2>4 ((f[i] /\ ~g[i]) \/ (~f[i] /\ g[i]))
            BY <1>3, <2>3
        <2>5 XORN[f][g][i]
            BY <2>4 DEF XORN
        <2>6 QED BY <2>5
    <1>4 ASSUME XORN[f][g][i] PROVE (f[i] /= g[i])
        <2>7 ((f[i] /\ ~g[i]) \/ (~f[i] /\ g[i]))
            BY <1>4 DEF XORN
        <2>8 f[i] /= g[i]
            BY <2>7
        <2>9 QED BY <2>8
    <1> QED BY <1>3, <1>4
    
THEOREM CMP32_F_EQ_G ==
    ASSUME N=31 PROVE
    \A f,g \in BVN :
    CMP32[f][g] <=> f=g
PROOF
    <1>1 TAKE f,g \in BVN
    <1>2 ASSUME CMP32[f][g] PROVE f=g
        <2>1 
             (~XORN[f][g][0] /\ ~XORN[f][g][1]  /\ ~XORN[f][g][2]  /\ 
             ~XORN[f][g][3]  /\ ~XORN[f][g][4]  /\ ~XORN[f][g][5]  /\ 
             ~XORN[f][g][6]  /\ ~XORN[f][g][7]  /\ ~XORN[f][g][8]  /\
             ~XORN[f][g][9]  /\ ~XORN[f][g][10] /\ ~XORN[f][g][11] /\
             ~XORN[f][g][12] /\ ~XORN[f][g][13] /\ ~XORN[f][g][14] /\
             ~XORN[f][g][15] /\ ~XORN[f][g][16] /\ ~XORN[f][g][17] /\
             ~XORN[f][g][18] /\ ~XORN[f][g][19] /\ ~XORN[f][g][20] /\
             ~XORN[f][g][21] /\ ~XORN[f][g][22] /\ ~XORN[f][g][23] /\
             ~XORN[f][g][24] /\ ~XORN[f][g][25] /\ ~XORN[f][g][26] /\
             ~XORN[f][g][27] /\ ~XORN[f][g][28] /\ ~XORN[f][g][29] /\
             ~XORN[f][g][30] /\ ~XORN[f][g][31]) => 
             (f[0]=g[0]   /\ f[1]=g[1]   /\ f[2]=g[2]   /\ f[3]=g[3]   /\
              f[4]=g[4]   /\ f[5]=g[5]   /\ f[6]=g[6]   /\ f[7]=g[7]   /\
              f[8]=g[8]   /\ f[9]=g[9]   /\ f[10]=g[10] /\ f[11]=g[11] /\
              f[12]=g[12] /\ f[13]=g[13] /\ f[14]=g[14] /\ f[15]=g[15] /\
              f[16]=g[16] /\ f[17]=g[17] /\ f[18]=g[18] /\ f[19]=g[19] /\
              f[20]=g[20] /\ f[21]=g[21] /\ f[22]=g[22] /\ f[23]=g[23] /\
              f[24]=g[24] /\ f[25]=g[25] /\ f[26]=g[26] /\ f[27]=g[27] /\
              f[28]=g[28] /\ f[29]=g[29] /\ f[30]=g[30] /\ f[31]=g[31])        
             BY NOT_XORN_EQ
        <2>2  
             (f[0]=g[0]   /\ f[1]=g[1]   /\ f[2]=g[2]   /\ f[3]=g[3]   /\
              f[4]=g[4]   /\ f[5]=g[5]   /\ f[6]=g[6]   /\ f[7]=g[7]   /\
              f[8]=g[8]   /\ f[9]=g[9]   /\ f[10]=g[10] /\ f[11]=g[11] /\
              f[12]=g[12] /\ f[13]=g[13] /\ f[14]=g[14] /\ f[15]=g[15] /\
              f[16]=g[16] /\ f[17]=g[17] /\ f[18]=g[18] /\ f[19]=g[19] /\
              f[20]=g[20] /\ f[21]=g[21] /\ f[22]=g[22] /\ f[23]=g[23] /\
              f[24]=g[24] /\ f[25]=g[25] /\ f[26]=g[26] /\ f[27]=g[27] /\
              f[28]=g[28] /\ f[29]=g[29] /\ f[30]=g[30] /\ f[31]=g[31])  =>
              (f=g)
            BY DEF BVN
        <2>3 f=g
            BY <1>2,<2>1,<2>2 DEF CMP32
        <2>4 QED BY <2>3
    <1>3 ASSUME f=g PROVE CMP32[f][g]
        <2>5 (f=g) => 
             (f[0]=g[0]   /\ f[1]=g[1]   /\ f[2]=g[2]   /\ f[3]=g[3]   /\
              f[4]=g[4]   /\ f[5]=g[5]   /\ f[6]=g[6]   /\ f[7]=g[7]   /\
              f[8]=g[8]   /\ f[9]=g[9]   /\ f[10]=g[10] /\ f[11]=g[11] /\
              f[12]=g[12] /\ f[13]=g[13] /\ f[14]=g[14] /\ f[15]=g[15] /\
              f[16]=g[16] /\ f[17]=g[17] /\ f[18]=g[18] /\ f[19]=g[19] /\
              f[20]=g[20] /\ f[21]=g[21] /\ f[22]=g[22] /\ f[23]=g[23] /\
              f[24]=g[24] /\ f[25]=g[25] /\ f[26]=g[26] /\ f[27]=g[27] /\
              f[28]=g[28] /\ f[29]=g[29] /\ f[30]=g[30] /\ f[31]=g[31])
            OBVIOUS
        <2>6 
             (f[0]=g[0]   /\ f[1]=g[1]   /\ f[2]=g[2]   /\ f[3]=g[3]   /\
              f[4]=g[4]   /\ f[5]=g[5]   /\ f[6]=g[6]   /\ f[7]=g[7]   /\
              f[8]=g[8]   /\ f[9]=g[9]   /\ f[10]=g[10] /\ f[11]=g[11] /\
              f[12]=g[12] /\ f[13]=g[13] /\ f[14]=g[14] /\ f[15]=g[15] /\
              f[16]=g[16] /\ f[17]=g[17] /\ f[18]=g[18] /\ f[19]=g[19] /\
              f[20]=g[20] /\ f[21]=g[21] /\ f[22]=g[22] /\ f[23]=g[23] /\
              f[24]=g[24] /\ f[25]=g[25] /\ f[26]=g[26] /\ f[27]=g[27] /\
              f[28]=g[28] /\ f[29]=g[29] /\ f[30]=g[30] /\ f[31]=g[31]) =>
             (~XORN[f][g][0] /\ ~XORN[f][g][1]  /\ ~XORN[f][g][2]  /\ 
             ~XORN[f][g][3]  /\ ~XORN[f][g][4]  /\ ~XORN[f][g][5]  /\ 
             ~XORN[f][g][6]  /\ ~XORN[f][g][7]  /\ ~XORN[f][g][8]  /\
             ~XORN[f][g][9]  /\ ~XORN[f][g][10] /\ ~XORN[f][g][11] /\
             ~XORN[f][g][12] /\ ~XORN[f][g][13] /\ ~XORN[f][g][14] /\
             ~XORN[f][g][15] /\ ~XORN[f][g][16] /\ ~XORN[f][g][17] /\
             ~XORN[f][g][18] /\ ~XORN[f][g][19] /\ ~XORN[f][g][20] /\
             ~XORN[f][g][21] /\ ~XORN[f][g][22] /\ ~XORN[f][g][23] /\
             ~XORN[f][g][24] /\ ~XORN[f][g][25] /\ ~XORN[f][g][26] /\
             ~XORN[f][g][27] /\ ~XORN[f][g][28] /\ ~XORN[f][g][29] /\
             ~XORN[f][g][30] /\ ~XORN[f][g][31])
            BY NOT_XORN_EQ
        <2>7 CMP32[f][g]
            BY <1>3,<2>5,<2>6 DEF CMP32
        <2>8 QED BY <2>7  
    <1> QED BY <1>2,<1>3


   

=============================================================================
\* Modification History
\* Last modified Sun Nov 13 04:28:43 CST 2022 by mjhomefolder
\* Created Thu Nov 03 00:11:52 CDT 2022 by mjhomefolder
