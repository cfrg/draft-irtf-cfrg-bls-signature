# Meeting notes August 12, 2019

* Attendees:
Bram Cohen,
Carl Beekhuizen,
Dan Middleton,
Hoeteck Wee,
Justin Drake,
Mike Lodder,
Sergey Gorbunov,
Victor Servant,
Zaki Manian,
zhenfei Zhang,

------

Hoeteck: update of the new cfrg draft
* link: https://github.com/cfrg/draft-irtf-cfrg-bls-signature/blob/master/draft-irtf-cfrg-bls-signature-00.txt
* changes since last version:
  * rely on hash to curve draft on hash into groups
    * used as a black box
    * arbitrary length messages
    * hash to curve function will rehash the message
  * uses HKDF for hash into groups and secret key derivation during key generation
  * serialization - follows pairing-friendly draft; uses zkcrypto's encoding

Justin: hashing pk during proof of possession uses a different domain separator; need to be specific about this separator

Hoeteck: will checks this issue


------
Bram: shall we standardize hierarchical key derivation for BLS secret keys (with a different approach than Bitcoin's)?

Carl: is working on this; make sense to also use hkdf following this standard

discussion to be continued on Telegram channel

------
Justin: quantum safe back up - a master seed to derive both a seed for bls sk and a seed for Hash-based signatures

Bram: hash a seed to the sk; reveal the sk, and generate a zk proof between the seed and the sk

Justin & Bram: discussion on mitigations against quantum apocalypse. Discussion to be continued on Telegram channel


Sergey: Is there a good implementation of Lamport signature?

Bram: No good source

Sergey: Will Ethereum deploy BLS with quantum safe backups?

Justin: there are two pks in Ethereum, a hot secret key and a cold secret key; target deploying quantum safety for cold
secret key along with bls signature this October

---


Zhenfei: updates on Riad's code
* Use zkcrypto's serialization method
* Use hkdf during hash to group and key generation
* todos:
  * Signature aggregation and verification
  * Proof of possession

Justin: which POP identifier will be used?

Sergey: it will be taken care of with the ciphersuite identifier
