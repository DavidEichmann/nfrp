TODO

1. [ ] Request updates from dependant nodes else you'll never get there in cases where e.g.
        a = source NodeA
        b = source NodeB
        c = a + b -- On NodeC
        -- a updates, but c is still waiting for an update from b
    Perhaps get rid of code that tries to infer this?

    4. [ ] Make sure to request initial values of behaviors!

2. [X] Listeners are getting invalid value? as in the case above:
    -- c { a = 0@00, b=0@0, c=0@0 }
    -- a = 1 (t = 10)
    -- c { a = 1@10, b=0@0, c=0@0 } is waiting for update on b
    -- b = 2 (t = 15)
    -- c { a = 1@10, b=2@15, c=1@10 } only know full history until t=10, should fire listener with c=1@10, but gives c=3@??? instead
    -- c requests update of a till 15 (or greater)    (after implementing 1.)
    -- c { a = 1@17, b=2@15, c=3@15 } fire listener with c=3@15

3. [ ] Replace real clock with vector clock
