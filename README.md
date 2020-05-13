# BLS Standard Draft

The repo is maintained by a working group aiming to standardize BLS signature scheme.
This repo was moved from [here](https://github.com/pairingwg/bls_standard).

## News:

* Updated from -00 to -02. See changelog.

* This draft has been adopted by the CFRG as an active [work group draft](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-02)

## Changelog:
* Changes from draft-irtf-cfrg-bls-signature-01 to draft-irtf-cfrg-bls-signature-02:
  * No change, maintenance release only: fix broken bibliography entry for hash-to-curve.

* Changes from draft-irtf-cfrg-bls-signature-00 to draft-irtf-cfrg-bls-signature-01:
  * Improve APIs:
    * make API functions take array/tuple of keys/messages instead of being variadic
    * clarify that functions taking multiple inputs are only valid when n >= 1
  * Remove SK-to-PK functionality from KeyGen; moved it to SkToPk function.
  * Tweaks to KeyGen:
    * append a null byte to IKM (lets us prove indifferentiability)
    * add optional key_info parameter (lets one generate different keys from same IKM)
    * append I2OSP(L, 2) to the info argument to HKDF-Expand. Ensures that changing L gives orthogonal output.
  * Update ciphersuites to use new hash-to-curve suite naming convention

* Changes from draft-boneh-bls-signature to draft-irtf-cfrg-bls-signature-00:
  * Changed serialization methods
  * Use HKDF to derive keys
  * Use hash to curve/group methods from [Hash to curve draft](https://tools.ietf.org/html/draft-irtf-cfrg-hash-to-curve-04)

## Useful links:
* Pairing draft: [stable](https://datatracker.ietf.org/doc/draft-irtf-cfrg--pairing-friendly-curves/), [dev](https://github.com/pairingwg/pfc_standard)
* Hash to curve draft: [stable](https://tools.ietf.org/doc/draft-irtf-cfrg-hash-to-curve/), [dev](https://github.com/cfrg/draft-irtf-cfrg-hash-to-curve)
* Current reference implementations:
  * https://github.com/kwantam/bls_sigs_ref
  * https://github.com/sigp/milagro_bls/
  * https://github.com/hyperledger/ursa/blob/master/libursa/src/bls/mod.rs
  * https://github.com/mikelodder7/bls12-381-comparison



## Version control

Major milestone updates (version [0](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-00), [1](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-01), [2](https://tools.ietf.org/html/draft-irtf-cfrg-bls-signature-02), ...)
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
