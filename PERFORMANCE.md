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


* benchmark `stack run bench -- 70 tf`  output: 248430
    * 597061766efc01ba79fe392df55ef8335455e3ab -> 10.07s user 0.32s system 100% cpu 10.381 total
    * 5ab12e4753ecd474e1fa26bc5d39b9640dbcedc3 -> 10.07s user 0.32s system 100% cpu 10.381 total

    * At this point I implemented tracking dependencies but haven't yet taken advantage of the to guid poking derivations
    * 777202a62be14ccaa246c0f5aacd69cd0fd1d579 -> 21.56s user 0.41s system 100% cpu 21.945 total
    * 0695e1ce846b125632d62bb19c5e4f434726de1d -> 21.01s user 0.48s system 100% cpu 21.465 total

