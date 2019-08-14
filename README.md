# BLS Standard Draft

The repo is maintained by a working group aiming to standardize BLS signature scheme.
This repo was moved from [here](https://github.com/pairingwg/bls_standard).

## News:

* This draft has been adopted by the CFRG as an active [work group draft](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-00)
* Major updates since [last version](https://datatracker.ietf.org/doc/draft-boneh-bls-signature/):
  * Changed serialization methods
  * Use HKDF to derive keys
  * Use hash to curve/group methods from [Hash to curve draft](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-04)

## Useful links:
* Pairing draft: [stable](https://datatracker.ietf.org/doc/draft-yonezawa-pairing-friendly-curves/), [dev](https://github.com/pairingwg/pfc_standard)
* Hash to curve draft: [stable](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-04), [dev](https://github.com/cfrg/draft-irtf-cfrg-hash-to-curve)
* Current reference implementations:
  * https://github.com/kwantam/bls_sigs_ref
  * https://github.com/sigp/milagro_bls/tree/experimental
  * https://github.com/hyperledger/ursa/blob/master/libursa/src/bls/mod.rs
  * https://github.com/mikelodder7/bls12-381-comparison



## Version control

Major milestone updates (version [0](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-00), 1, ...)
will be uploaded to [IETF webpage](https://datatracker.ietf.org/doc/draft-irtf-cfrg-bls-signature).
Minor advancement are released through subversions.

## Comments and feedbacks
Feel free to submit any feedback by
* creating issues (preferred method), or
* pull request (please use it for editorial only)

## Formatting
To generate txt/pdf:
1. use mmark to convert md to xml
2. use xml2rfc to convert xml to txt/pdf
