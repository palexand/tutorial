use vstd::prelude::*;

verus!{

pub closed spec fn min(x:int,y:int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

pub proof fn lemma_min(x:int,y:int)
    ensures
        min(x,y) <= x,
        min(x,y) <= y,
        min(x,y) == x || min(x,y) == y,
{
}

}