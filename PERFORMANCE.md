# Performance

We need to pick a good datastructure to hold facts and derivations. It is vital
understand the operations we need to perform:

* Reads

    lookupVKB
        :: Time -> VIx a -> MaybeKnown a
    lookupVKBTrace
        :: Time -> VIx a -> MaybeKnown (DerivationTrace a)
    lookupVFact
        :: Time -> VIx a -> MaybeKnown (ValueFact a)
    factsV
        :: VIx a -> [ValueFact a]


* benchmark `stack run bench -- 70 tf`
    * 597061766efc01ba79fe392df55ef8335455e3ab -> 10.07s user 0.32s system 100% cpu 10.381 total
