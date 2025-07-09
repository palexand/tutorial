use vstd::prelude::*;

verus!{

spec fn triangle(n:nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
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

fn triangle_loop(n: u32) -> (sum: u32)
    requires 
        triangle(n as nat) < 0x1_0000_000,
    ensures
        sum == triangle(n as nat),
    {
        let mut sum: u32 = 0;
        let mut idx: u32 = 0;
        while idx < n
            invariant
                idx <= n,
                sum == triangle(idx as nat),
                triangle(n as nat) < 0x1_0000_0000,
            decreases n - idx,
        {
            idx = idx+1;
            assert(sum + idx < 0x1_0000_0000) by {
                triangle_is_monotonic(idx as nat, n as nat);
            }
            sum = sum + idx;
        }
        return sum
    } 

    fn test_triangle_assert_by() {
        assert(triangle(3) < 0x1_0000_0000) by {
            reveal_with_fuel(triangle,20);}
        }

    fn rec_triangle(n:u32) -> (z:u32)
        requires
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            z == triangle(n as nat),
        decreases n,
    {
        if n == 0 {
            0
        } else { n + rec_triangle(n - 1) }
    }

fn mut_triangle(n: u32, z: &mut u32)
        requires
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *z == triangle(n as nat),
        decreases n,
    {
        if n == 0 {
            *z = 0
        } else { mut_triangle(n - 1,z);
                *z = *z + n }
    }

fn tail_triangle(n: u32, idx: u32, sum: &mut u32)
        requires
            idx <= n,
            *old(sum) == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        ensures
            *sum == triangle(n as nat),
        decreases n - idx,
    {
        if idx < n {
            let idx = idx + 1;
            assert(*sum + idx < 0x1_0000_0000) by {
                triangle_is_monotonic(idx as nat, n as nat);
            }
            // assert(*sum + idx < 0x1_0000_0000)
            *sum = *sum + idx;
            tail_triangle(n,idx,sum);
        }
    }

fn loop_triangle(n:u32) -> (sum:u32)
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
            sum == triangle(idx as nat),
            triangle(n as nat) < 0x1_0000_0000,
        decreases n - idx,
    {
        idx = idx + 1;
        assert(sum + idx < 0x1_0000_0000) by {
            triangle_is_monotonic(idx as nat, n as nat);
        }
        sum = sum + idx;
    }
    return sum
}

    fn main(){
//        assert(triangle(3) < 0x1_0000_0000) by
//            {reveal_with_fuel(triangle,20)};
//        assert(triangle(3) == 6) by
//            {reveal_with_fuel(triangle,20)};
        assert(triangle(0) == 0);
        assert(triangle(1) == 1);
        assert(triangle(2) == 3);
//        assert(triangle(3) == 6);
        let x = triangle_loop(3) + triangle_loop(4);
        let t4: u32 = triangle_loop(4);
    }
}  
