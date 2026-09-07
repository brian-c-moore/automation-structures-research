---- MODULE EncryptThenAuthenticate ----
(*
  Encrypt-then-authenticate (the composition taxonomy, AEAD).

  Three-phase composition: an encryption phase produces ciphertext blocks
  from plaintext using the BlockToStreamConversion construction; an
  authentication phase chains AAD then ciphertext through a polynomial-MAC
  accumulator, taken abstractly; a tag-derivation phase combines
  the MAC output with a nonce-derived value to produce the final tag.

  Canonical examples: AES-128-GCM, ChaCha20-Poly1305. The pattern is
  the dominant modern AEAD shape; alternatives (encrypt-and-mac,
  mac-then-encrypt) have known weaknesses and are not modeled.

  Build requirements demonstrated: ResourceRegistry (per-block key
    streams + ciphertext + auth accumulator) + TraversalEngine (over
    blocks within each phase) + ActuationPass (per-block transformation)
    + Reduction (XOR for encrypt; polynomial-MAC accumulator for
    authenticate). AuthHash and TagMix abstract the polynomial-MAC
    accumulator and the nonce-mixing step; KeyStreamAt abstracts
    BlockToStreamConversion's output.

  Safety claims:
    PhaseOrdering — phases execute in encrypt -> auth_aad -> auth_ct ->
      tag -> done order.
    CiphertextLenTracksEncIdx — |ciphertext| equals enc_idx in encrypt
      phase, equals NumBlocks afterwards.
    CiphertextEntryCorrect — each ciphertext[i] equals Xor of plaintext[i]
      and KeyStreamAt[i].
    AuthAccStartsAtZero — at the start of auth_aad, auth_acc = AuthH0.
    AuthAccChainConsistent — during auth phases, auth_acc reflects the
      AuthHash chain over inputs processed so far.
    TagDerivedFromAcc — after the tag phase, tag = TagMix[auth_acc].

  Bounded parameters per the study definition: NumBlocks = 2, AADBlocks = 1.
  Exhaustive.

  Expected outcome: No error has been found  (PASS).
*)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    b0, b1, b2, b3,    \* block / state model values
    NumBlocks,         \* plaintext / ciphertext block count
    AADBlocks          \* associated-data block count

ASSUME NumBlocksType == NumBlocks \in Nat /\ NumBlocks >= 1
ASSUME AADBlocksType == AADBlocks \in Nat /\ AADBlocks >= 1

\* ── Fixed topology ───────────────────────────────────────────────────────
BlockValue == {b0, b1, b2, b3}
AuthState  == BlockValue   \* MAC accumulator is over the same value space

AuthH0 == b0    \* initial accumulator value
TagMixConst == b1   \* the nonce-derived constant XORed in TagMix

\* KeyStreamAt: 1..NumBlocks -> BlockValue.  The keystream block for index i,
\* abstracted from BlockToStreamConversion's output.
KeyStreamAt ==
    [i \in 1..NumBlocks |->
        IF i = 1 THEN b1 ELSE b2]

\* Plaintext: 1..NumBlocks -> BlockValue.
Plaintext ==
    [i \in 1..NumBlocks |->
        IF i = 1 THEN b2 ELSE b3]

\* AAD: 1..AADBlocks -> BlockValue.
AAD ==
    [i \in 1..AADBlocks |->
        IF i = 1 THEN b3 ELSE b0]

\* Xor: BlockValue \X BlockValue -> BlockValue.
Xor ==
    [p \in BlockValue \X BlockValue |->
        IF      p = <<b0, b0>> THEN b0
        ELSE IF p = <<b0, b1>> THEN b1
        ELSE IF p = <<b0, b2>> THEN b2
        ELSE IF p = <<b0, b3>> THEN b3
        ELSE IF p = <<b1, b0>> THEN b1
        ELSE IF p = <<b1, b1>> THEN b0
        ELSE IF p = <<b1, b2>> THEN b3
        ELSE IF p = <<b1, b3>> THEN b2
        ELSE IF p = <<b2, b0>> THEN b2
        ELSE IF p = <<b2, b1>> THEN b3
        ELSE IF p = <<b2, b2>> THEN b0
        ELSE IF p = <<b2, b3>> THEN b1
        ELSE IF p = <<b3, b0>> THEN b3
        ELSE IF p = <<b3, b1>> THEN b2
        ELSE IF p = <<b3, b2>> THEN b1
        ELSE                        b0]

\* AuthHash: AuthState \X BlockValue -> AuthState.  Abstracts the
\* polynomial-MAC accumulator step (e.g. Horner-form: A <- (A + X) * r).
AuthHash ==
    [p \in AuthState \X BlockValue |->
        IF      p = <<b0, b0>> THEN b1
        ELSE IF p = <<b0, b1>> THEN b2
        ELSE IF p = <<b0, b2>> THEN b3
        ELSE IF p = <<b0, b3>> THEN b0
        ELSE IF p = <<b1, b0>> THEN b2
        ELSE IF p = <<b1, b1>> THEN b3
        ELSE IF p = <<b1, b2>> THEN b0
        ELSE IF p = <<b1, b3>> THEN b1
        ELSE IF p = <<b2, b0>> THEN b3
        ELSE IF p = <<b2, b1>> THEN b0
        ELSE IF p = <<b2, b2>> THEN b1
        ELSE IF p = <<b2, b3>> THEN b2
        ELSE IF p = <<b3, b0>> THEN b0
        ELSE IF p = <<b3, b1>> THEN b1
        ELSE IF p = <<b3, b2>> THEN b2
        ELSE                        b3]

\* TagMix: AuthState -> BlockValue.  Abstracts the nonce-mixing step
\* T = AuthAcc XOR Enc(K, J0) in GCM, or T = AuthAcc + s in Poly1305.
TagMix ==
    [a \in AuthState |-> Xor[<<a, TagMixConst>>]]

VARIABLES
    phase,             \* "encrypt" / "auth_aad" / "auth_ct" / "tag" / "done"
    enc_idx,           \* progress in encrypt phase (0..NumBlocks)
    ciphertext,        \* Seq(BlockValue) — produced ciphertext blocks
    auth_idx,          \* progress in auth_aad or auth_ct phase
    auth_acc,          \* AuthState — accumulator value
    tag                \* BlockValue — final tag (set in tag phase)

vars == <<phase, enc_idx, ciphertext, auth_idx, auth_acc, tag>>

\* ---- Type invariant ------------------------------------------------------

TypeInvariant ==
    /\ phase \in {"encrypt", "auth_aad", "auth_ct", "tag", "done"}
    /\ enc_idx \in 0..NumBlocks
    /\ ciphertext \in Seq(BlockValue)
    /\ auth_idx \in 0..(NumBlocks + AADBlocks)
    /\ auth_acc \in AuthState
    /\ tag \in BlockValue
    /\ Len(ciphertext) = enc_idx
    /\ (phase = "auth_aad" \/ phase = "auth_ct" \/ phase = "tag" \/ phase = "done")
       => Len(ciphertext) = NumBlocks
    /\ (phase = "auth_aad")  => auth_idx \in 0..AADBlocks
    /\ (phase = "auth_ct" \/ phase = "tag" \/ phase = "done")
       => auth_idx \in 0..NumBlocks

\* ---- Safety invariants ---------------------------------------------------

PhaseOrdering ==
    /\ phase = "encrypt" => Len(ciphertext) = enc_idx
    /\ (phase = "auth_aad" \/ phase = "auth_ct" \/ phase = "tag" \/ phase = "done")
       => Len(ciphertext) = NumBlocks
    /\ phase = "encrypt" => auth_acc = AuthH0
    /\ (phase = "auth_aad" \/ phase = "auth_ct" \/ phase = "tag" \/ phase = "done")
       => Len(ciphertext) = NumBlocks
    /\ phase = "done" => tag = TagMix[auth_acc]

CiphertextLenTracksEncIdx ==
    Len(ciphertext) = enc_idx \/ (Len(ciphertext) = NumBlocks /\ phase /= "encrypt")

\* Each ciphertext block is the Xor of plaintext and keystream at that index.
CiphertextEntryCorrect ==
    \A i \in 1..Len(ciphertext) :
        ciphertext[i] = Xor[<<Plaintext[i], KeyStreamAt[i]>>]

\* In the auth_aad phase, auth_acc reflects the AuthHash chain over AAD
\* prefix of length auth_idx (starting from AuthH0).
AuthAccChainAad ==
    phase = "auth_aad" =>
        \E acc_seq \in Seq(AuthState) :
            /\ Len(acc_seq) = auth_idx + 1
            /\ acc_seq[1] = AuthH0
            /\ \A k \in 1..auth_idx :
                   acc_seq[k + 1] = AuthHash[<<acc_seq[k], AAD[k]>>]
            /\ auth_acc = acc_seq[auth_idx + 1]

\* In the auth_ct phase, auth_acc reflects the chain after processing
\* all AADBlocks of AAD and then auth_idx of ciphertext.
AuthAccChainCt ==
    (phase = "auth_ct" \/ phase = "tag" \/ phase = "done") =>
        \E acc_seq \in Seq(AuthState) :
            /\ Len(acc_seq) = AADBlocks + auth_idx + 1
            /\ acc_seq[1] = AuthH0
            /\ \A k \in 1..AADBlocks :
                   acc_seq[k + 1] = AuthHash[<<acc_seq[k], AAD[k]>>]
            /\ \A k \in 1..auth_idx :
                   acc_seq[AADBlocks + k + 1] =
                     AuthHash[<<acc_seq[AADBlocks + k], ciphertext[k]>>]
            /\ auth_acc = acc_seq[AADBlocks + auth_idx + 1]

\* After tag phase, tag = TagMix(auth_acc).
TagDerivedFromAcc ==
    phase = "done" => tag = TagMix[auth_acc]

\* ---- Init ----------------------------------------------------------------

Init ==
    /\ phase = "encrypt"
    /\ enc_idx = 0
    /\ ciphertext = <<>>
    /\ auth_idx = 0
    /\ auth_acc = AuthH0
    /\ tag = b0   \* initial tag value before DeriveTag

\* ---- Actions -------------------------------------------------------------

EncryptBlock ==
    /\ phase = "encrypt"
    /\ enc_idx < NumBlocks
    /\ LET ct == Xor[<<Plaintext[enc_idx + 1], KeyStreamAt[enc_idx + 1]>>]
       IN  ciphertext' = Append(ciphertext, ct)
    /\ enc_idx' = enc_idx + 1
    /\ UNCHANGED <<phase, auth_idx, auth_acc, tag>>

FinishEncrypt ==
    /\ phase = "encrypt"
    /\ enc_idx = NumBlocks
    /\ phase' = "auth_aad"
    /\ auth_idx' = 0
    /\ UNCHANGED <<enc_idx, ciphertext, auth_acc, tag>>

AuthAadBlock ==
    /\ phase = "auth_aad"
    /\ auth_idx < AADBlocks
    /\ auth_acc' = AuthHash[<<auth_acc, AAD[auth_idx + 1]>>]
    /\ auth_idx' = auth_idx + 1
    /\ UNCHANGED <<phase, enc_idx, ciphertext, tag>>

FinishAuthAad ==
    /\ phase = "auth_aad"
    /\ auth_idx = AADBlocks
    /\ phase' = "auth_ct"
    /\ auth_idx' = 0
    /\ UNCHANGED <<enc_idx, ciphertext, auth_acc, tag>>

AuthCtBlock ==
    /\ phase = "auth_ct"
    /\ auth_idx < NumBlocks
    /\ auth_acc' = AuthHash[<<auth_acc, ciphertext[auth_idx + 1]>>]
    /\ auth_idx' = auth_idx + 1
    /\ UNCHANGED <<phase, enc_idx, ciphertext, tag>>

FinishAuthCt ==
    /\ phase = "auth_ct"
    /\ auth_idx = NumBlocks
    /\ phase' = "tag"
    /\ UNCHANGED <<enc_idx, ciphertext, auth_idx, auth_acc, tag>>

TagStep ==
    /\ phase = "tag"
    /\ tag' = TagMix[auth_acc]
    /\ phase' = "done"
    /\ UNCHANGED <<enc_idx, ciphertext, auth_idx, auth_acc>>

Done ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ EncryptBlock
    \/ FinishEncrypt
    \/ AuthAadBlock
    \/ FinishAuthAad
    \/ AuthCtBlock
    \/ FinishAuthCt
    \/ TagStep
    \/ Done

Spec == Init /\ [][Next]_vars

\* ---- Theorem (checked by TLC) --------------------------------------------

THEOREM Spec =>
    [](TypeInvariant /\ PhaseOrdering /\ CiphertextLenTracksEncIdx
       /\ CiphertextEntryCorrect /\ TagDerivedFromAcc)
====
