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

proof fn triangle_is_monotonic(i:nat,j:nat)
    ensures
        i<=j ==> triangle(i) <= triangle(j),
    decreases j,
{
    if j == 0 {

    } else {
        triangle_is_monotonic(i,(j-1) as nat)
    }
}

fn test_triangle_fail() {
    assert(triangle(0) == 0);
    assert(triangle(10) == 55);
}

exec fn triangle_loop(n: u32) -> (sum: u32)
    requires 
        triangle(n as nat) < 0x1_0000_0000,
    ensures
        sum == triangle(n as nat),
    {
        let mut sum: u32 = 0;
        let mut idx: u32 = 0;
        while idx < n
            invariant
                idx <= n,
                sum = triangle(idx as nat),
                triangle(n as nat) < 0x1_0000_0000,
            decreases n - idx,
        {
            idx = idx+1;
            assert(sum + idx < 0x1_0000_0000) by {
                triangle_is_monotonic(idx as nat, n as nat);
            }
            sum = sum + idx;
        }
        sum
    }
}
