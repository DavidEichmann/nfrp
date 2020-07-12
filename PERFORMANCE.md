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
