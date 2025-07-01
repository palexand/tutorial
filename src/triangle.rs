use vstd::prelude::*;

verus!{

spec fn triangle(n:nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle(n - 1)
    }
}

fn test_triangle_fail() {
    assert(triangle(0) == 0);
    assert(triangle(10) == 55);
}

}