%%%
Title = "draft-boneh-bls-signature-00.txt"
abbrev = "BLS-signature"
category = "info"
docName = "draft-boneh-bls-signature-00.txt"
ipr= "trust200902"
workgroup = "CFRG"

date = 2019-02-08


[[author]]
initials="D."
surname="Boneh"
fullname="Dan Boneh"
organization="Stanford University"
 [author.address]
 email = "dabo@cs.stanford.edu"
  [author.address.postal]
  city = ""
  country = "USA"
[[author]]
initials="R."
surname="Wahby"
fullname="Riad S. Wahby"
organization="Stanford University"
 [author.address]
 email = "rsw@cs.stanford.edu"
  [author.address.postal]
  city = ""
  country = "USA"
[[author]]
initials="S."
surname="Gorbunov"
fullname="Sergey Gorbunov"
organization="Algorand and University of Waterloo"
 [author.address]
 email = "sergey@algorand.com"
  [author.address.postal]
  city = "Boston, MA"
  country = "USA"
[[author]]
initials="H."
surname="Wee"
fullname="Hoeteck Wee"
organization="Algorand and ENS, Paris"
 [author.address]
 email = "wee@di.ens.fr"
  [author.address.postal]
  city = "Boston, MA"
  country = "USA"
[[author]]
initials="Z."
surname="Zhang"
fullname="Zhenfei Zhang"
organization="Algorand"
 [author.address]
 email = "zhenfei@algorand.com"
  [author.address.postal]
  city = "Boston, MA"
  country = "USA"
%%%


.# Abstract


BLS is a digital signature scheme with compression properties.
With a given set of signatures (signature\_1, ..., signature\_n) anyone can produce
a compressed signature signature\_compressed. The same is true for a set of
secret keys or public keys, while keeping the connection between sets
(i.e., a compressed public key is associated to its compressed secret key).
Furthermore, the BLS signature scheme is deterministic, non-malleable,
and efficient. Its simplicity and cryptographic properties allows it
to be useful in a variety of use-cases, specifically when minimal
storage space or bandwidth are required.


{mainmatter}


# Introduction

A signature scheme is a fundamental cryptographic primitive
that is used to protect authenticity and integrity of communication.
Only the holder of a secret key can sign messages, but anyone can
verify the signature using the associated public key.

Signature schemes are used in point-to-point secure communication
protocols, PKI, remote connections, etc.
Designing efficient and secure digital signature is very important
for these applications.

This document describes the BLS signature scheme. The scheme enjoys a variety
of important efficiency properties:

1. The public key and the signatures are encoded as single group elements.
1. Verification requires 2 pairing operations.
1. A collection of signatures (signature\_1, ..., signature\_n) can be compressed
into a single signature (signature). Moreover, the compressed signature can
be verified using only n+1 pairings (as opposed to 2n pairings, when verifying
n signatures separately).

Given the above properties,
the scheme enables many interesting applications.
The immediate applications include

* authentication and integrity for Public Key Infrastructure (PKI) and blockchains.

  * The usage is similar to classical digital signatures, such as ECDSA.

*  compressing signature chains for PKI and  Secure Border Gateway Protocol (SBGP).

   * Concretely, in a PKI signature chain of depth n, we have n signatures by n
certificate authorities on n distinct certificates. Similarly, in SBGP,
each router receives a list of n signatures attesting to a path of length n
in the network. In both settings, using the BLS signature scheme would allow us
to compress the n signatures into a single signature.

* consensus protocols for blockchains.

  * There, BLS signatures
are used for authenticating transactions as well as votes during the consensus
protocol, and the use of aggregation significantly reduces the bandwidth
and storage requirements.

## Comparison with ECDSA

The following comparison assumes BLS signatures with curve BLS12-381, targeting
128 bits security.

For 128 bits security, ECDSA takes 37 and 79 micro-seconds to sign and verify
a signature on a typical laptop. In comparison, for the same level of security,
BLS takes 370 and 2700 micro-seconds to sign and verify
a signature.

In terms of sizes, ECDSA uses 32 bytes for public keys and  64 bytes for signatures;
while BLS uses 96 bytes for public keys, and  48 bytes for signatures.
Alternatively, BLS can also be instantiated with 48 bytes of public keys and 96 bytes
of signatures.
BLS also allows for signature compression. In other words, a single signature is
sufficient to anthenticate multiple messages and public keys.


## Organization of this document

This document is organized as follows:

- The remainder of this section defines terminology and the high-level API.

- (#coreops) defines primitive operations used in the BLS signature scheme.
  These operations MUST NOT be used alone.

- (#schemes) defines three variants of the BLS Signature scheme.

- (#ciphersuites) gives recommended ciphersuites.

- The appendices give test vectors, etc.

## Terminology and definitions {#definitions}

The following terminology is used through this document:

* SK:  The secret key for the signature scheme.

* PK:  The public key for the signature scheme.

* message:  The input to be signed by the signature scheme.

* signature:  The digital signature output.

* aggregation:  Given a list of signatures for a list of messages and public keys,
an aggregation algorithm generates one signature that authenticates the same
list of messages and public keys.

* rogue key attack:
  An attack in which a specially crafted public key (the "rogue" key) is used
  to forge an aggregated signature.
  (#schemes) specifies methods for securing against rogue key attacks.


The following notation and primitives are used:

* a || b denotes the concatenation of octet strings a and b.

* A pairing-friendly elliptic curve defines the following primitives
  (see [I-D.pairing-friendly-curves] for detailed discussion):

  - E1, E2: elliptic curve groups defined over finite fields.
    This document assumes that E1 has a more compact representation than
    E2, i.e., because E1 is defined over a smaller field than E2.

  - G1, G2: subgroups of E1 and E2 (respectively) having prime order r.

  - P1, P2: distinguished points that generate of G1 and G2, respectively.

  - GT: a subgroup, of prime order r, of the multiplicative group of a field extension.

  - e : G1 x G2 -> GT: a non-degenerate bilinear map.

* For the above pairing-friendly curve, this document
  writes operations in E1 and E2 in additive notation, i.e.,
  P + Q denotes point addition and x \* P denotes scalar multiplication.
  Operations in GT are written in multiplicative notation, i.e., a \* b
  is field multiplication.

<!-- ISSUE(RSW): pairing-friendly curves uses x[P] for multiplication? -->

* For each of E1 and E2 defined by the above pairing-friendly curve,
  we assume that the pairing-friendly elliptic curve definition provides
  several primitives, described below.

    Note that these primitives are named generically.
    When referring to one of these primitives for a specific group,
    this document appends the name of the group, e.g.,
    point\_to\_octets\_E1, subgroup\_check\_E2, etc.

  - point\_to\_octets(P) -> ostr: returns the canonical representation of
    the point P as an octet string.
    This operation is also known as serialization.

  - octets\_to\_point(ostr) -> P: returns the point P corresponding to the
    canonical representation ostr, or INVALID if ostr is not a valid output
    of point\_to\_octets.
    This operation is also known as deserialization.

  - subgroup\_check(P) -> VALID or INVALID: returns VALID when the point P
    is an element of the subgroup of order r, and INVALID otherwise.
    This function can always be implemented by checking that r \* P is equal
    to the identity element. In some cases, faster checks may also exist,
    e.g., [Bowe19].

* I2OSP and OS2IP are the functions defined in [RFC3447, Section 4].

* hash\_to\_point(ostr) -> P: a cryptographic hash function that takes as input an
  arbitrary octet string and returns a point on an elliptic curve.
  Functions of this kind are defined in [I-D.hash-to-curve].
  Each of the ciphersuites in (#ciphersuites) specifies the hash\_to\_point
  algorithm to be used.

## API {#blsapi}

The BLS signature scheme defines the following API:

* KeyGen(IKM) -> PK, SK: a key generation algorithm that
  takes as input an octet string comprising secret keying material,
  and outputs a public key PK and corresponding secret key SK.


* Sign(SK, message) -> signature: a signing algorithm that generates a
  deterministic signature given a secret key SK and a message.


* Verify(PK, message, signature) -> VALID or INVALID: 
  a verification algorithm that outputs VALID if signature is a valid
  signature of message under public key PK, and INVALID otherwise.

* Aggregate(signature\_1, ..., signature\_n) -> signature:
  an aggregation algorithm that compresses a collection of signatures
  into a single signature.

* AggregateVerify((PK\_1, message\_1), ..., (PK\_n, message\_n), signature) -> VALID or INVALID:
  an aggregate verification algorithm that outputs VALID if signature
  is a valid aggregated signature for a collection of public keys and messages,
  and outputs INVALID otherwise.


## Dependencies

This draft depends on the following documents:

* [I-D.hash-to-curve] gives methods to hash from octet strings to group elements.

* [I-D.pairing-friendly-curves] defines pairing-friendly elliptic curves and related operations.


## Requirements

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "MAY", and "OPTIONAL" in this
document are to be interpreted as described in [@!RFC2119].


# Core operations {#coreops}

This section defines core operations used by the schemes defined in (#schemes).
These operations MUST NOT be used except as described in that section.

## Variants {#corevariants}

Each core operation has two variants that trade off signature
and public key size:

1. Minimal-signature-size: signatures are points in G1,
   public keys are points in G2.
   (Recall from (#definitions) that E1 has a more compact representation than E2.)

2. Minimal-pubkey-size: public keys are points in G1,
   signatures are points in G2.

    Implementations using signature aggregation SHOULD use this approach,
    since the size of (PK\_1, ..., PK\_n, signature) is dominated by
    the public keys even for small n.

<!--
    For instance, when instantiated with the pairing-friendly curve
    BLS12-381 [I-D.pairing-friendly-curves], this yields a 48-byte signature.
    For comparison, an EdDSA signature over curve25519 is 64 bytes [RFC8032].
-->

## Parameters {#coreparams}

The core operations in this section depend on several parameters:

- A signature variant, either minimal-signature-size or minimal-pubkey-size.
  These are defined in (#corevariants).

- A pairing-friendly elliptic curve, plus associated functionality
  given in (#definitions).

- H, a hash function H that MUST be a secure cryptographic hash function,
  e.g., SHA-256 [FIPS180-4].
  For security, H MUST output at least ceil(log2(r)) bits, where r is
  the order of the subgroups G1 and G2 defined by the pairing-friendly
  elliptic curve.

- hash\_to\_point, a function whose interface is described in (#definitions).
  When the signature variant is minimal-signature-size, this function
  MUST output a point in G1.
  When the signature variant is minimal-pubkey size, this function
  MUST output a point in G2.
  For security, this function MUST be either a random oracle encoding or a
  nonuniform encoding, as defined in [I-D.hash-to-curve].

In addition, the following primitives are determined by the above parameters:

- P, an elliptic curve point.
  When the signature variant is minimal-signature-size, P is the
  distinguished point P2 that generates the group G2 (see (#definitions)).
  When the signature variant is minimal-pubkey-size, P is the
  distinguished point P1 that generates the group G1.

- r, the order of the subgroups G1 and G2 defined by the pairing-friendly curve.

- pairing, a function that invokes the function e of (#definitions),
  with argument order depending on signature variant:

  - For minimal-signature-size:

        pairing(U, V) := e(U, V)

  - For minimal-pubkey-size:

        pairing(U, V) := e(V, U)

- point\_to\_pubkey and point\_to\_signature, functions that invoke the
  appropriate serialization routine ((#definitions)) depending on
  signature variant:

  - For minimal-signature-size:

        point\_to\_pubkey(P) := point\_to\_octets\_E2(P)

        point\_to\_signature(P) := point\_to\_octets\_E1(P)

  - For minimal-pubkey-size:

        point\_to\_pubkey(P) := point\_to\_octets\_E1(P)

        point\_to\_signature(P) := point\_to\_octets\_E2(P)

- pubkey\_to\_point and signature\_to\_point, functions that invoke the
  appropriate deserialization routine ((#definitions)) depending on
  signature variant:

  - For minimal-signature-size:

        pubkey\_to\_point(ostr) := octets\_to\_point\_E2(ostr)

        signature\_to\_point(ostr) := octets\_to\_point\_E1(ostr)

  - For minimal-pubkey-size:

        pubkey\_to\_point(ostr) := octets\_to\_point\_E1(ostr)

        signature\_to\_point(ostr) := octets\_to\_point\_E2(ostr)

- pubkey\_subgroup\_check and signature\_subgroup\_check, functions
  that invoke the appropriate subgroup check routine ((#definitions))
  depending on signature variant:

  - For minimal-signature-size:

        pubkey\_subgroup\_check(ostr) := subgroup\_check\_E2(ostr)

        signature\_subgroup\_check(ostr) := subgroup\_check\_E1(ostr)

  - For minimal-pubkey-size:

        pubkey\_subgroup\_check(ostr) := subgroup\_check\_E1(ostr)

        signature\_subgroup\_check(ostr) := subgroup\_check\_E2(ostr)

##  KeyGen {#keygen}

The KeyGen algorithm generates a pair (PK, SK) deterministically using
the secret octet string IKM.

KeyGen uses HKDF [@!RFC5869] instantiated with the hash function H.

For security, IKM MUST be infeasible to guess, e.g.,
generated by a trusted source of randomness.
IKM MUST be at least 32 bytes long, but it MAY be longer.

Because KeyGen is deterministic, implementations MAY choose either to
store the resulting (PK, SK) or to store IKM and call KeyGen to derive
the keys when necessary.

~~~
(PK, SK) = KeyGen(IKM)

Inputs:
- IKM, a secret octet string. See requirements above.

Outputs:
- PK, a public key encoded as an octet string.
- SK, the corresponding secret key, an integer 0 <= SK < r.

Definitions:
- HKDF-Extract is as defined in RFC5869, instantiated with hash H.
- HKDF-Expand is as defined in RFC5869, instantiated with hash H.
- L is the integer given by ceil((1.5 * ceil(log2(r))) / 8).
- "BLS-SIG-KEYGEN-SALT-" is an ASCII string comprising 20 octets.
- "" is the empty string.

Procedure:
1. PRK = HKDF-Extract("BLS-SIG-KEYGEN-SALT-", IKM)
2. OKM = HKDF-Expand(PRK, "", L)
3. x = OS2IP(OKM) mod r
4. xP = x * P
5. SK = x
6. PK = point_to_pubkey(xP)
7. return (PK, SK)
~~~

## KeyValidate {#keyvalidate}

The KeyValidate algorithm ensures that a public key is valid.

~~~
result = KeyValidate(PK)

Inputs:
- PK, a public key in the format output by KeyGen.

Outputs:
- result, either VALID or INVALID

Procedure:
1. xP = pubkey_to_point(PK)
2. If xP is INVALID, return INVALID
3. If pubkey_subgroup_check(xP) is INVALID, return INVALID
4. return VALID
~~~

## CoreSign {#coresign}

The CoreSign algorithm computes a signature from SK, a secret key,
and message, an octet string.

~~~
signature = CoreSign(SK, message)

Inputs:
- SK, the secret key output by an invocation of KeyGen.
- message, an octet string.

Outputs:
- signature, an octet string.

Procedure:
1. Q = hash_to_point(message)
2. R = SK * Q
3. signature = point_to_signature(R)
4. return signature
~~~

## CoreVerify {#coreverify}

The CoreVerify algorithm checks that a signature is valid for
the octet string message under the public key PK.

The public key PK must satisfy KeyValidate(PK) == VALID ((#keyvalidate)).

~~~
result = CoreVerify(PK, message, signature)

Inputs:
- PK, a public key in the format output by KeyGen.
- message, an octet string.
- signature, an octet string in the format output by CoreSign.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. R = signature_to_point(signature)
2. If R is INVALID, return INVALID
3. If signature_subgroup_check(R) is INVALID, return INVALID
4. xP = pubkey_to_point(PK)
5. Q = hash_to_point(message)
6. C1 = pairing(Q, xP)
7. C2 = pairing(R, P)
8. If C1 == C2, return VALID, else return INVALID
~~~

## Aggregate

The Aggregate algorithm compresses multiple signatures into one.

~~~
signature = Aggregate(signature_1, ..., signature_n)

Inputs:
- signature_1, ..., signature_n, octet strings output by
  either CoreSign or Aggregate.

Outputs:
- signature, an octet string encoding a compressed signature
  that compbines all inputs; or INVALID.

Procedure:
1. accum = signature_to_point(signature_1)
2. If accum is INVALID, return INVALID
3. for i in 2, ..., n:
4.     next = signature_to_point(signature_i)
5.     If next is INVALID, return INVALID
6.     accum = accum + next
7. signature = point_to_signature(accum)
8. return signature
~~~

## CoreAggregateVerify

The CoreAggregateVerify algorithm checks an aggregated signature
over several (PK, message) pairs.

All public keys PK\_i must satisfy KeyValidate(PK\_i) == VALID
((#keyvalidate)).

~~~
result = CoreAggregateVerify((PK_1, message_1), ..., (PK_n, message_n),
                             signature)

Inputs:
- PK_1, ..., PK_n, public keys in the format output by KeyGen.
- message_1, ..., message_n, octet strings.
- signature, an octet string output by Aggregate.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. R = signature_to_point(signature)
2. If R is INVALID, return INVALID
3. If signature_subgroup_check(R) is INVALID, return INVALID
4. C1 = 1 (the identity element in GT)
5. for i in 1, ..., n:
6.     xP = pubkey_to_point(PK_i)
7.     Q = hash_to_point(message_i)
8.     C1 = C1 * pairing(Q, xP)
9. C2 = pairing(R, P)
10. If C1 == C2, return VALID, else return INVALID
~~~

# BLS Signatures {#schemes}

This section defines three signature schemes: basic, message augmentation,
and proof of possession.
These schemes differ in the ways that they defend against rogue key
attacks ((#definitions)).

All of the schemes in this section are built on a set of core operations
defined in (#coreops).
Thus, defining a scheme requires fixing a set of parameters as
defined in (#coreparams).

All three schemes expose the KeyGen and Aggregate operations
that are defined in (#coreops).
The sections below define the other API functions ((#blsapi))
for each scheme.

## Basic scheme {#schemenul}

In a basic scheme, rogue key attacks are handled by requiring
all messages signed by an aggregate signature to be distinct.
This requirement is enforced in the definition of AggregateVerify.

The Sign and Verify functions are identical to CoreSign and
CoreVerify ((#coreops)), respectively.
AggregateVerify is defined below.

All public keys PK supplied as arguments to Verify and AggregateVerify
MUST satisfy KeyValidate(PK) == VALID ((#keyvalidate)).

### AggregateVerify

This function first ensures that all messages are distinct, and then
invokes CoreAggregateVerify.

~~~
result = AggregateVerify((PK_1, message_1), ..., (PK_n, message_n),
                         signature)

Inputs:
- PK_1, ..., PK_n, public keys in the format output by KeyGen.
- message_1, ..., message_n, octet strings.
- signature, an octet string output by Aggregate.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. If any two input messages are equal, return INVALID.
2. return CoreAggregateVerify((PK_1, message_1), ..., (PK_n, message_n),
                              signature)
~~~

## Message augmentation {#schemeaug}

In a message augmentation scheme, signatures are generated
over the concatenation of the public key and the message,
ensuring that messages signed by different public keys are
distinct.

All public keys PK supplied as arguments to Verify and AggregateVerify
MUST satisfy KeyValidate(PK) == VALID ((#keyvalidate)).

### Sign

To match the API for Sign defined in (#blsapi), this function
recomputes the public key corresponding to the input SK.
Implementations MAY instead implement an interface that takes
the public key as an input.

Note that the point P and the point\_to\_pubkey function are
defined in (#coreparams).

~~~
signature = Sign(SK, message)

Inputs:
- SK, a secret key output by an invocation of KeyGen.
- message, an octet string.

Outputs:
- signature, an octet string.

Procedure:
1. xP = SK * P
2. PK = point_to_pubkey(xP)
3. return CoreSign(SK, PK || message)
~~~

### Verify

~~~
result = Verify(PK, message, signature)

Inputs:
- PK, a public key in the format output by KeyGen.
- message, an octet string.
- signature, an octet string in the format output by CoreSign.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. return CoreVerify(PK, PK || message, signature)
~~~

### AggregateVerify

~~~
result = AggregateVerify((PK_1, message_1), ..., (PK_n, message_n),
                         signature)

Inputs:
- PK_1, ..., PK_n, public keys in the format output by KeyGen.
- message_1, ..., message_n, octet strings.
- signature, an octet string output by Aggregate.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. for i in 1, ..., n:
2.    mprime_i = PK_i || message_i
3. return CoreAggregateVerify((PK_1, mprime_1), ..., (PK_n, mprime_n),
                              signature)
~~~

## Proof of possession {#schemepop}


A proof of possession scheme uses a separate public key
validation step, called a proof of possession, to defend against
rogue key attacks.
This enables an optimization to aggregate signature verification
for the case that all signatures are on the same message.

The Sign, Verify, and AggregateVerify functions
are identical to CoreSign, CoreVerify, and CoreAggregateVerify
((#coreops)), respectively.
In addition, a proof of possession scheme defines three functions beyond
the standard API ((#blsapi)):

- PopProve(SK) -> proof: an algorithm that generates a proof of possession
  for the public key corresponding to secret key SK.

- PopVerify(PK, proof) -> VALID or INVALID:
  an algorithm that outputs VALID if proof is valid for PK, and INVALID otherwise.

- FastAggregateVerify(PK\_1, ..., PK\_n, message, signature) -> VALID or INVALID:
  a verification algorithm for the aggregate of multiple signatures on
  the same message.
  This function is faster than AggregateVerify.

All public keys used by Verify, AggregateVerify, and FastAggregateVerify
MUST be accompanied by a proof of possession generated by PopProve,
and the result of PopVerify on this proof MUST be VALID.

### Parameters {#popparams}

In addition to the parameters required to instantiate the core operations
((#coreparams)), a proof of possession scheme requires one further parameter:

- hash\_pubkey\_to\_point(PK) -> P: a cryptographic hash function that takes as
  input a public key and outputs a point in the same subgroup as the
  hash\_to\_point algorithm used to instantiate the core operations.

    For security, this function MUST be orthogonal to the hash\_to\_point function.
    In addition, this function MUST be either a random oracle encoding or a
    nonuniform encoding, as defined in [I-D.hash-to-curve].
    The RECOMMENDED way of instantiating hash\_pubkey\_to\_point is to use
    the same hash-to-curve function as hash\_to\_point, with a
    different domain separation tag (see [I-D.hash-to-curve], Section 5.1).

### PopProve

This function recomputes the public key coresponding to the input SK.
Implementations MAY instead implement an interface that takes the
public key as input.

Note that the point P and the point\_to\_pubkey and point\_to\_signature
functions are defined in (#coreparams).
The hash\_pubkey\_to\_point function is defined in (#popparams).

~~~
proof = PopProve(SK)

Inputs:
- SK, a secret key output by an invocation of KeyGen.

Outputs:
- proof, an octet string.

Procedure:
1. xP = SK * P
2. PK = point_to_pubkey(xP)
3. Q = hash_pubkey_to_point(PK)
4. R = SK * Q
5. proof = point_to_signature(R)
6. return signature
~~~

### PopVerify

Note that the following uses several functions defined in (#coreops).
The hash\_pubkey\_to\_point function is defined in (#popparams).

~~~
result = PopVerify(PK, proof)

Inputs:
- PK, a public key inthe format output by KeyGen.
- proof, an octet string in the format output by PopProve.

Outputs:
- result, either VALID or INVALID

Procedure:
1. R = signature_to_point(proof)
2. If R is INVALID, return INVALID
3. If signature_subgroup_check(R) is INVALID, return INVALID
4. If KeyValidate(PK) is INVALID, return INVALID
5. xP = pubkey_to_point(PK)
6. Q = hash_pubkey_to_point(PK)
7. C1 = pairing(Q, xP)
8. C2 = pairing(R, P)
9. If C1 == C2, return VALID, else return INVALID
~~~

### FastAggregateVerify

Note that the following uses several functions defined in (#coreops).

~~~
result = FastAggregateVerify(PK_1, ..., PK_n, message, signature)

Inputs:
- PK_1, ..., PK_n, public keys in the format output by KeyGen.
- message, an octet string.
- signature, an octet string output by Aggregate.

Outputs:
- result, either VALID or INVALID.

Procedure:
1. accum = pubkey_to_point(PK_1)
2. for i in 2, ..., n:
3.     next = pubkey_to_point(PK_i)
4.     accum = accum + next
5. PK = point_to_pubkey(accum)
6. return CoreVerify(PK, message, signature)
~~~

# Ciphersuites {#ciphersuites}


# Security Considerations

## Validating public keys {#pubkeyvalid}

When users register a public key, we should ensure that it is well-formed.
This requires a G2 membership test. In applications where we use aggregation,
we need to enforce security against rogue key attacks [Boneh-Drijvers-Neven 18a](https://crypto.stanford.edu/~dabo/pubs/papers/BLSmultisig.html).
This can be achieved in one of three ways:

* Message augmentation:    pk = g^sk,   sig = H(pk, m)^sk
(BGLS, [Bellare-Namprempre-Neven 07](https://eprint.iacr.org/2006/285)).

* Proof of possession:     pk = ( u=g^sk,  H'(u)^sk ),    sig = H(m)^sk
(see concrete mechanisms in [Ristenpart-Yilek 06])

* Linear combination:    agg =  sig\_1^t\_1 ... sig\_n^t\_n
(see [Boneh-Drijvers-Neven 18b](https://eprint.iacr.org/2018/483.pdf);
there, pre-processing public keys would speed up verification.)

## Skipping membership check
Several existing implementations skip steps 5-6 (membership in G1) in CoreVerify ((#coreverify)).
In this setting, the BLS signature remains unforgeable (but not strongly
unforgeable) under a stronger assumption:

given P1, a \* P1, P2, b \* P2, it is hard to compute U in E1 such that
pairing(U,P2) = pairing(a \* P1, b \* P2).

## Side channel attacks
It is important to protect the secret key in implementations of the
signing algorithm. We can protect against some side-channel attacks by
ensuring that the implementation executes exactly the same sequence of
instructions and performs exactly the same memory accesses, for any
value of the secret key. To achieve this, we require that
 point multiplication in G1 should run in constant time with respect to
the scalar.

## Randomness considerations
BLS signatures are deterministic. This protects against attacks
arising from signing with bad randomness, for example, the nonce reuse
attack on ECDSA [HDWH 12].

<!---
For signing, we require variable-base exponentiation in G1 to be constant-time, and
for key generation, we require fixed-base exponentiation in G2 to be constant-time.

#### Strong unforgeability.
Only variant 1 is strongly unforgeable; the basic variant and variant 2 are not if the
co-factor is greater than 1.
--->

## Implementing the hash function
The security analysis models the hash function H as a random oracle,
and it is crucial that we implement H using a cryptographically
secure hash function.

<!-- At the moment, hashing onto G1 is typically
implemented by hashing into E1 and then multiplying by the cofactor;
this needs to be taken into account in the security proof (namely, the
reduction needs to simulate the corresponding E1 element).-->


# Implementation Status

This section will be removed in the final version of the draft.
There are currently several implementations of BLS signatures using the BLS12-381 curve.

* Algorand: TBA

* Chia: [spec](https://github.com/Chia-Network/bls-signatures/blob/master/SPEC.md)
[python/C++](https://github.com/Chia-Network/bls-signatures). Here, they are
swapping G1 and G2 so that the public keys are small, and the benefits
of avoiding a membership check during signature verification would even be more
substantial. The current implementation does not seem to implement the membership check.
Chia uses the Fouque-Tibouchi hashing to the curve, which can be done in constant time.

* Dfinity: [go](https://github.com/dfinity/go-dfinity-crypto) [BLS](https://github.com/dfinity/bls).  The current implementations do not seem to implement the membership check.

* Ethereum 2.0: [spec](https://github.com/ethereum/eth2.0-specs/blob/master/specs/bls_signature.md)

# Related Standards

* Pairing-friendly curves [draft-yonezawa-pairing-friendly-curves](https://tools.ietf.org/html/draft-yonezawa-pairing-friendly-curves-00)

* Pairing-based Identity-Based Encryption [IEEE 1363.3](https://ieeexplore.ieee.org/document/6662370).

* Identity-Based Cryptography Standard [rfc5901](https://tools.ietf.org/html/rfc5091).

* Hashing to Elliptic Curves [draft-irtf-cfrg-hash-to-curve-02](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-02), in order to implement the hash function H. The current draft does not cover pairing-friendly curves, where we need to handle curves over prime power extension fields GF(p^k).

* Verifiable random functions [draft-irtf-cfrg-vrf-03](https://tools.ietf.org/html/draft-irtf-cfrg-vrf-03). Section 5.4.1 also discusses instantiations for H.

* EdDSA [rfc8032](https://tools.ietf.org/html/rfc8032)


<!---
# IANA Considerations

This document does not make any requests of IANA.
--->

{backmatter}

# Test Vectors


TBA: (i) test vectors for both variants of the signature scheme
(signatures in G2 instead of G1) , (ii) test vectors ensuring
membership checks, (iii) intermediate computations ctr, hm.

<!---
We generate test vectors for curve BLS12-381. The test vectors are in both raw form (as in octet strings)
and mathematical form (as in field elements and group elements). The raw form may vary in
different implementations due to encoding mechanisms.


The generator of G2 is set to P2 which is a string "93 e0 2b 60 52 71 9f 60 7d ac d3 a0 88 27 4f 65 59 6b d0 d0 99 20 b6 1a b5 da 61 bb dc 7f 50 49 33 4c f1 12 13 94 5d 57 e5 ac 7d 05 5d 04 2b 7e 02 4a a2 b2 f0 8f 0a 91 26 08 05 27 2d c5 10 51 c6 e4 7a d4 fa 40 3b 02 b4 51 0b 64 7a e3 d1 77 0b ac 03 26 a8 05 bb ef d4 80 56 c8 c1 21 bd b8"

that encodes a point whose projective form is

* x: Fq2 { c0: Fq(0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8), c1: Fq(0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e) },
* y: Fq2 { c0: Fq(0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801), c1: Fq(0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be) },
* z: Fq2 { c0: Fq(0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001), c1: Fq(0x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) } }


The key generation function performs the following steps to obtain a key pair:

* input keyseed = "this is the input to a hash"

* rngseed = SHA512-256(keyseed)

* instantiate XorShiftRng from rngseed

* generate a field element from XorShiftRng as the secret key
sk = "7d 79 2c 3a 49 ca e9 8c 13 00 c0 c3 75 c1 41 fe 7b 57 07 58 a0 21 b9 01 fb 32 be 6b 67 7f bd a8"

which encodes a field element "0xa8bd7f676bbe32fb01b921a05807577bfe41c175c3c000138ce9ca493a2c797d"

* compute sk*P2 to obtain public key pk = "a4 e0 6b 85 fb da 53 db 3b a6 60 92 b7 7e 16 86 d6 d6 ca ac e3 79 3c 20 e3 7b 80 4e 50 94 5f b9 9c 10 08 83 72 b4 fb 6c 82 00 c4 21 fc 6c 8d c2 0c e4 29 ef 08 d7 c6 64 cb 24 7f e6 4a f7 34 fb ed d6 a6 28 14 97 34 5c a8 1d 17 17 b2 09 e1 26 54 9c d1 fd 98 fb 0c 13 5a 9d 71 6f 9f b5 4b b1"

that encodes a point whose projective form is

* x: Fq2 { c0: Fq(0x145caaad2e9c9d814b06c612cd5fd9149575c4d692fd729dff38a49bb5f41bdee8be0024acc57776c4954c6439cda90e), c1: Fq(0x159362e375b67aa84b32ebf200f225ca582f75e2b7227c859d84e490d7dbdc6b0a5271846ef1c3f8ca58f8ebb7e8047f) },
* y: Fq2 { c0: Fq(0x18c53564406af055cd2cd1baf1abd8c1cc974c3bc0df8ccc8c123274af760f6a2856838dc0a033386b1abbf42fd97386), c1: Fq(0x04a13949876f767d334a98eb968bcffbf6b59b48ac316e53fb501f0598a4f5042802dc78aa51e2fd265ce35bc2295d99) },
* z: Fq2 { c0: Fq(0x00fcb7858e1f18ad9b1a8032d369f9a8a022d5794d49c73f908ac3e40f5ab60b100ec022214636b0eb6fcec185c9341e), c1: Fq(0x139ae75a9781efdf8babcd047d2166d9a3044256d811b4e4449ad791fe795b95ee4d01f032aa45ccd33342c6eef41785) } }


To sign a message message = "this is the message", the signing algorithm does the following:

* instantiate the Hash_to_G1 algorithm with SHA512 using try-and-increment method
* obtain hm = Hash_to_G1(message)
* compute x*hm as signature = "b2 b8 e3 8d ec 47 f9 4a bb a7 c1 95 64 bd ad 96 0a 9f 42 43 8c f4 98 06 11 da 82 bb 78 d6 de 53 cc f2 3a 29 a8 e2 87 b0 9f ce 91 7a 28 17 8a f3"
which encodes a point whose projective form is
  * x: Fq(0x0f7e27fe139e0d2ad38b25e0d34cc1445fcfb9375d5a7078a87458a6a98224584199ec0197392ff08e0be368b452ad65),
  * y: Fq(0x02424a69e9b6d9818fa99099f7f4fb56123587477bb1b992f478940b82cef401ff4bf96b77dec63826bf6c08addb08db),
  * z: Fq(0x18e24c7f7b34aa5f03fcfb6eee8293a00479f8ce9aef6c7184ea2f0e6b73e059865a3222936281881598b7436181627d)

To verify the signature with the public key and the message, the verification algorithm does the
following:

* instantiate the hash_to_G1 algorithm with SHA512 using try-and-increment method
* obtain hm = hash_to_G1(message)
* return pairing(hm, pk) ?= pairing(signature, P2)

The verification algorithm should return true for the testing vectors in this section.
--->

# Security

## Definitions
### Message Unforgeability

Consider the following game between an adversary and a challenger.
The challenger generates a key-pair (PK, SK) and gives PK to the adversary.
The adversary may repeatedly query the challenger on any message message to obtain
its corresponding signature signature. Eventually the adversary outputs a pair
(message', signature').

Unforgeability means no adversary can produce a pair (message', signature') for a message message' which he never queried the challenger and Verify(PK, message, signature) outputs VALID.


### Strong Message Unforgeability

In the strong unforgeability game, the game proceeds as above, except
no adversary should be able to produce a pair (message', signature') that verifies (i.e. Verify(PK, message, signature)
outputs VALID) given that he never queried the challenger on message', or if he did query and obtained
a reply signature, then signature != signature'.

More informally, the strong unforgeability means that no adversary can produce
a different signature (not provided by the challenger) on a message which he queried before.

### Aggregation Unforgeability

Consider the following game between an adversary and a challenger.
The challenger generates a key-pair (PK, SK) and gives PK to the adversary.
The adversary may repeatedly query the challenger on any message message to obtain
its corresponding signature signature.
Eventually the adversary outputs a sequence ((PK\_1, message\_1), ..., (PK\_n, message\_n), (PK, message), signature).

Aggregation unforgeability means that no adversary can produce a sequence
where it did not query the challenger on the message message, and
Verify-Aggregated((PK\_1, message\_1), ..., (PK\_n, message\_n), (PK, message), signature) outputs VALID.

We note that aggregation unforgeability implies message unforgeability.

TODO: We may also consider a strong aggregation unforgeability property.

## Security analysis

The BLS signature scheme achieves strong message unforgeability and aggregation
unforgeability under the co-CDH
assumption, namely that given P1, a \* P1, P2, b \* P2, it is hard to
compute {ab} \* P1. [BLS01, BGLS03]


# References

[BLS 01] Dan Boneh, Ben Lynn, Hovav Shacham:
Short Signatures from the Weil Pairing. ASIACRYPT 2001: 514-532.

[BGLS 03] Dan Boneh, Craig Gentry, Ben Lynn, Hovav Shacham:
Aggregate and Verifiably Encrypted Signatures from Bilinear Maps. EUROCRYPT 2003: 416-432.

[HDWH 12]
    Heninger, N., Durumeric, Z., Wustrow, E., Halderman, J.A.:
    "Mining your Ps and Qs: Detection of widespread weak keys in network devices.",
    USENIX 2012.

[I-D.irtf-cfrg-hash-to-curve]
    S. Scott, N. Sullivan, and C. Wood:
    "Hashing to Elliptic Curves",
    draft-irtf-cfrg-hash-to-curve-01 (work in progress),
    July 2018.

[I-D.pairing-friendly-curves]
    S. Yonezawa, S. Chikara, T. Kobayashi, T. Saito:
    "Pairing-Friendly Curves",
    draft-yonezawa-pairing-friendly-curves-00,
    Jan 2019.
