def split [DecidableEq V] (x : V) (s: List V) : (List V × List V) := match s with
| [] => ([], [])
| y :: s => if x = y then
              (x :: [], s)
            else
              let (s1, s2) := split x s
              (y :: s1, s2)


-- ensures {let (s1, s2) = result in s1 ++ s2 = s}
-- ensures {let (s1, _) = result in lmem x s -> is_last x s1}
