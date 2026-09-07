---- MODULE EncryptThenAuthenticate_Proof ----
(***************************************************************************
  TLAPS proof of safety for the EncryptThenAuthenticate composition (AEAD).

  Discharges the cfg-checked subset of the THEOREM declared in
  EncryptThenAuthenticate.tla:
      Spec => [](TypeInvariant /\ PhaseOrdering
                 /\ CiphertextLenTracksEncIdx
                 /\ CiphertextEntryCorrect
                 /\ TagDerivedFromAcc)

  Inductive strengthening: none. The five cfg invariants are jointly
  inductive without further strengthening. The AuthAccChainAad and
  AuthAccChainCt invariants in the .tla (which use existential
  quantification over auxiliary acc_seq sequences) are not in the cfg's
  TLC-checked set and not addressed by this proof.

  This proof module artifact per the TLA+ study contract
 ***************************************************************************)
EXTENDS EncryptThenAuthenticate, Naturals, Sequences, FiniteSets, TLAPS

ASSUME NumBlocksAss == NumBlocks \in Nat /\ NumBlocks >= 1
ASSUME AADBlocksAss == AADBlocks \in Nat /\ AADBlocks >= 1

\* Helper lemmas.
LEMMA AuthH0Type == AuthH0 \in AuthState
  BY DEF AuthH0, AuthState, BlockValue

LEMMA TagMixConstType == TagMixConst \in BlockValue
  BY DEF TagMixConst, BlockValue

LEMMA PlaintextType ==
    \A i \in 1..NumBlocks : Plaintext[i] \in BlockValue
  BY NumBlocksAss DEF Plaintext, BlockValue

LEMMA KeyStreamAtType ==
    \A i \in 1..NumBlocks : KeyStreamAt[i] \in BlockValue
  BY NumBlocksAss DEF KeyStreamAt, BlockValue

LEMMA AADType ==
    \A i \in 1..AADBlocks : AAD[i] \in BlockValue
  BY AADBlocksAss DEF AAD, BlockValue

LEMMA XorType ==
    \A a \in BlockValue, b \in BlockValue : Xor[<<a, b>>] \in BlockValue
  BY DEF Xor, BlockValue

LEMMA AuthHashType ==
    \A a \in AuthState, b \in BlockValue : AuthHash[<<a, b>>] \in AuthState
  BY DEF AuthHash, AuthState, BlockValue

LEMMA TagMixType ==
    \A a \in AuthState : TagMix[a] \in BlockValue
  BY TagMixConstType, XorType DEF TagMix, AuthState

\* Inductive invariant.
Inv == TypeInvariant /\ PhaseOrdering /\ CiphertextLenTracksEncIdx
       /\ CiphertextEntryCorrect /\ TagDerivedFromAcc

(*-------------------------------------------------------------------------*)
(* Lemma: Init establishes the inductive invariant.                        *)
(*-------------------------------------------------------------------------*)
LEMMA InitInv == Init => Inv
  <1> SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. TypeInvariant
    BY AuthH0Type, NumBlocksAss, AADBlocksAss DEF Init, TypeInvariant, AuthState, BlockValue
  <1>2. PhaseOrdering
    BY DEF Init, PhaseOrdering
  <1>3. CiphertextLenTracksEncIdx
    BY DEF Init, CiphertextLenTracksEncIdx
  <1>4. CiphertextEntryCorrect
    \* ciphertext = <<>>; the universal is vacuous.
    BY DEF Init, CiphertextEntryCorrect
  <1>5. TagDerivedFromAcc
    \* phase = "encrypt"; antecedent of the implication is false.
    BY DEF Init, TagDerivedFromAcc
  <1> QED  BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Inv

(*-------------------------------------------------------------------------*)
(* Lemma: every Next step preserves the inductive invariant.               *)
(*-------------------------------------------------------------------------*)
LEMMA NextInv == Inv /\ [Next]_vars => Inv'
  <1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1> USE DEF Inv, TypeInvariant, PhaseOrdering, CiphertextLenTracksEncIdx,
              CiphertextEntryCorrect, TagDerivedFromAcc
  <1>0. CASE UNCHANGED vars
    BY <1>0 DEF vars
  <1>A. CASE EncryptBlock
    <2>a. phase = "encrypt"                                BY <1>A DEF EncryptBlock
    <2>b. enc_idx < NumBlocks                              BY <1>A DEF EncryptBlock
    <2> DEFINE ct == Xor[<<Plaintext[enc_idx + 1], KeyStreamAt[enc_idx + 1]>>]
    <2>c. ciphertext' = Append(ciphertext, ct)             BY <1>A DEF EncryptBlock
    <2>d. enc_idx' = enc_idx + 1                           BY <1>A DEF EncryptBlock
    <2>e. UNCHANGED <<phase, auth_idx, auth_acc, tag>>     BY <1>A DEF EncryptBlock
    <2>f. enc_idx + 1 \in 1..NumBlocks                     BY <2>b, NumBlocksAss
    <2>g. Plaintext[enc_idx + 1] \in BlockValue            BY <2>f, PlaintextType
    <2>h. KeyStreamAt[enc_idx + 1] \in BlockValue          BY <2>f, KeyStreamAtType
    <2>i. ct \in BlockValue                                BY <2>g, <2>h, XorType
    <2>j. Len(ciphertext) = enc_idx                        OBVIOUS
    <2>k. ciphertext \in Seq(BlockValue)                   OBVIOUS
    <2>l. ciphertext' \in Seq(BlockValue) /\ Len(ciphertext') = enc_idx + 1
      BY <2>c, <2>i, <2>j, <2>k
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>d, <2>e, <2>l, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      <3>1. phase' = "encrypt"                              BY <2>a, <2>e
      <3>2. Len(ciphertext') = enc_idx'                     BY <2>d, <2>l
      <3>3. auth_acc' = AuthH0
        \* From PhaseOrdering pre: phase = "encrypt" => auth_acc = AuthH0.
        BY <2>a, <2>e
      <3> QED  BY <3>1, <3>2, <3>3
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>d, <2>l
    <2>4. CiphertextEntryCorrect'
      <3> SUFFICES ASSUME NEW i \in 1..Len(ciphertext')
                   PROVE  ciphertext'[i] = Xor[<<Plaintext[i], KeyStreamAt[i]>>]
        OBVIOUS
      <3>A. CASE i \in 1..Len(ciphertext)
        <4>1. ciphertext'[i] = ciphertext[i]
          BY <2>c, <2>j, <2>k, <3>A
        <4>2. ciphertext[i] = Xor[<<Plaintext[i], KeyStreamAt[i]>>]
          BY <3>A
        <4> QED  BY <4>1, <4>2
      <3>B. CASE i = Len(ciphertext) + 1
        <4>1. ciphertext'[i] = ct
          BY <2>c, <2>j, <2>k, <3>B
        <4>2. i = enc_idx + 1
          BY <2>j, <3>B
        <4> QED  BY <4>1, <4>2
      <3> QED  BY <2>j, <2>l, <3>A, <3>B
    <2>5. TagDerivedFromAcc'
      \* phase' = "encrypt", antecedent false.
      BY <2>a, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>B. CASE FinishEncrypt
    <2>a. phase = "encrypt"                                BY <1>B DEF FinishEncrypt
    <2>b. enc_idx = NumBlocks                              BY <1>B DEF FinishEncrypt
    <2>c. phase' = "auth_aad"                              BY <1>B DEF FinishEncrypt
    <2>d. auth_idx' = 0                                    BY <1>B DEF FinishEncrypt
    <2>e. UNCHANGED <<enc_idx, ciphertext, auth_acc, tag>> BY <1>B DEF FinishEncrypt
    <2>1. TypeInvariant'
      BY <2>b, <2>c, <2>d, <2>e, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      <3>1. Len(ciphertext') = NumBlocks
        BY <2>b, <2>e
      <3> QED  BY <2>c, <3>1
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>b, <2>c, <2>e
    <2>4. CiphertextEntryCorrect'
      BY <2>e
    <2>5. TagDerivedFromAcc'
      BY <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>C. CASE AuthAadBlock
    <2>a. phase = "auth_aad"                               BY <1>C DEF AuthAadBlock
    <2>b. auth_idx < AADBlocks                             BY <1>C DEF AuthAadBlock
    <2>c. auth_acc' = AuthHash[<<auth_acc, AAD[auth_idx + 1]>>]
      BY <1>C DEF AuthAadBlock
    <2>d. auth_idx' = auth_idx + 1                         BY <1>C DEF AuthAadBlock
    <2>e. UNCHANGED <<phase, enc_idx, ciphertext, tag>>    BY <1>C DEF AuthAadBlock
    <2>f. auth_idx + 1 \in 1..AADBlocks                    BY <2>b, AADBlocksAss
    <2>g. AAD[auth_idx + 1] \in BlockValue                 BY <2>f, AADType
    <2>h. auth_acc \in AuthState                           OBVIOUS
    <2>i. auth_acc' \in AuthState                          BY <2>c, <2>g, <2>h, AuthHashType
    <2>j. Len(ciphertext) = NumBlocks
      \* From PhaseOrdering pre: phase = "auth_aad" => Len(ciphertext) = NumBlocks.
      BY <2>a
    <2>k. Len(ciphertext') = NumBlocks                     BY <2>e, <2>j
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>d, <2>e, <2>i, <2>k, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      BY <2>a, <2>e, <2>k
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>a, <2>e, <2>k
    <2>4. CiphertextEntryCorrect'
      BY <2>e
    <2>5. TagDerivedFromAcc'
      BY <2>a, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>D. CASE FinishAuthAad
    <2>a. phase = "auth_aad"                               BY <1>D DEF FinishAuthAad
    <2>b. auth_idx = AADBlocks                             BY <1>D DEF FinishAuthAad
    <2>c. phase' = "auth_ct"                               BY <1>D DEF FinishAuthAad
    <2>d. auth_idx' = 0                                    BY <1>D DEF FinishAuthAad
    <2>e. UNCHANGED <<enc_idx, ciphertext, auth_acc, tag>> BY <1>D DEF FinishAuthAad
    <2>f. Len(ciphertext) = NumBlocks
      \* From PhaseOrdering pre: phase = "auth_aad" => Len(ciphertext) = NumBlocks.
      BY <2>a
    <2>g. Len(ciphertext') = NumBlocks                     BY <2>e, <2>f
    <2>1. TypeInvariant'
      BY <2>c, <2>d, <2>e, <2>g, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      BY <2>a, <2>c, <2>e, <2>g
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>a, <2>c, <2>e, <2>g
    <2>4. CiphertextEntryCorrect'
      BY <2>e
    <2>5. TagDerivedFromAcc'
      BY <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>E. CASE AuthCtBlock
    <2>a. phase = "auth_ct"                                BY <1>E DEF AuthCtBlock
    <2>b. auth_idx < NumBlocks                             BY <1>E DEF AuthCtBlock
    <2>c. auth_acc' = AuthHash[<<auth_acc, ciphertext[auth_idx + 1]>>]
      BY <1>E DEF AuthCtBlock
    <2>d. auth_idx' = auth_idx + 1                         BY <1>E DEF AuthCtBlock
    <2>e. UNCHANGED <<phase, enc_idx, ciphertext, tag>>    BY <1>E DEF AuthCtBlock
    <2>f. Len(ciphertext) = NumBlocks
      \* From PhaseOrdering pre: phase = "auth_ct" => Len(ciphertext) = NumBlocks.
      BY <2>a
    <2>g. auth_idx + 1 \in 1..NumBlocks                    BY <2>b, NumBlocksAss
    <2>h. ciphertext[auth_idx + 1] \in BlockValue
      \* From TypeInvariant pre: ciphertext \in Seq(BlockValue).
      BY <2>f, <2>g
    <2>i. auth_acc \in AuthState                           OBVIOUS
    <2>j. auth_acc' \in AuthState                          BY <2>c, <2>h, <2>i, AuthHashType
    <2>1. TypeInvariant'
      BY <2>a, <2>b, <2>d, <2>e, <2>j, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      BY <2>a, <2>e
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>a, <2>e, <2>f
    <2>4. CiphertextEntryCorrect'
      BY <2>e
    <2>5. TagDerivedFromAcc'
      BY <2>a, <2>e
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>F. CASE FinishAuthCt
    <2>a. phase = "auth_ct"                                BY <1>F DEF FinishAuthCt
    <2>b. auth_idx = NumBlocks                             BY <1>F DEF FinishAuthCt
    <2>c. phase' = "tag"                                   BY <1>F DEF FinishAuthCt
    <2>d. UNCHANGED <<enc_idx, ciphertext, auth_idx, auth_acc, tag>>
      BY <1>F DEF FinishAuthCt
    <2>e. Len(ciphertext) = NumBlocks
      \* From PhaseOrdering pre: phase = "auth_ct" => Len(ciphertext) = NumBlocks.
      BY <2>a
    <2>f. Len(ciphertext') = NumBlocks                     BY <2>d, <2>e
    <2>1. TypeInvariant'
      BY <2>b, <2>c, <2>d, <2>f, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      BY <2>a, <2>c, <2>d, <2>f
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>a, <2>c, <2>d, <2>f
    <2>4. CiphertextEntryCorrect'
      BY <2>d
    <2>5. TagDerivedFromAcc'
      BY <2>c
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>G. CASE TagStep
    <2>a. phase = "tag"                                    BY <1>G DEF TagStep
    <2>b. tag' = TagMix[auth_acc]                          BY <1>G DEF TagStep
    <2>c. phase' = "done"                                  BY <1>G DEF TagStep
    <2>d. UNCHANGED <<enc_idx, ciphertext, auth_idx, auth_acc>>
      BY <1>G DEF TagStep
    <2>e. auth_acc \in AuthState                           OBVIOUS
    <2>f. tag' \in BlockValue                              BY <2>b, <2>e, TagMixType
    <2>1. TypeInvariant'
      BY <2>a, <2>c, <2>d, <2>f, NumBlocksAss, AADBlocksAss
    <2>2. PhaseOrdering'
      BY <2>a, <2>b, <2>c, <2>d
    <2>3. CiphertextLenTracksEncIdx'
      BY <2>a, <2>c, <2>d
    <2>4. CiphertextEntryCorrect'
      BY <2>d
    <2>5. TagDerivedFromAcc'
      BY <2>b, <2>c, <2>d
    <2> QED  BY <2>1, <2>2, <2>3, <2>4, <2>5
  <1>H. CASE Done
    BY <1>H DEF Done, vars
  <1>I. CASE Next
    BY <1>I, <1>A, <1>B, <1>C, <1>D, <1>E, <1>F, <1>G, <1>H DEF Next
  <1> QED  BY <1>0, <1>I

(*-------------------------------------------------------------------------*)
(* Main safety theorem.                                                    *)
(*-------------------------------------------------------------------------*)
THEOREM Safety == Spec => []Inv
  <1>1. Init => Inv                       BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'        BY NextInv
  <1> QED  BY <1>1, <1>2, PTL DEF Spec

(*-------------------------------------------------------------------------*)
(* Per-invariant corollaries.                                              *)
(*-------------------------------------------------------------------------*)
THEOREM TypeInvariantSafety == Spec => []TypeInvariant
  BY Safety, PTL DEF Inv

THEOREM PhaseOrderingSafety == Spec => []PhaseOrdering
  BY Safety, PTL DEF Inv

THEOREM CiphertextLenTracksEncIdxSafety == Spec => []CiphertextLenTracksEncIdx
  BY Safety, PTL DEF Inv

THEOREM CiphertextEntryCorrectSafety == Spec => []CiphertextEntryCorrect
  BY Safety, PTL DEF Inv

THEOREM TagDerivedFromAccSafety == Spec => []TagDerivedFromAcc
  BY Safety, PTL DEF Inv

====
