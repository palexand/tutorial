mod octuple;
mod triangle;

use vstd::prelude::*;

verus!{

#[verifier::external_body]
fn print_two_digit_number(x:i8)
    requires x < 100 && x > -99,
{
    println!("The answer is {}",x);
}

spec fn octuple_req(x1:int) -> (x8:int) 
{
  (8 * x1)
}

fn octuple(x1:i8) -> (x8:i8)
        requires -16 <= x1 < 16,
        ensures x8 == 8 * x1,
{
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}

fn main() {
    let n= octuple(10);
    print_two_digit_number(n);
    assert(n==80)
}

/* Define an ideal secification for incremenet over naturals. */
spec fn inc(n: nat) -> nat
{
    if n == 0 {
        1
    } else {
        n + 1
    }
}  

/* define an increment definition for an implementation */
exec fn inc_exec(x:i32) -> (z:i32)
    requires 0 <= x < 100,
    ensures z == inc(x as nat) && z>x,
{
    return x+1
}

/* Define an ideal specification for factorial over naturals. Ideal in that overflow and underflow are quite allowed. */
spec fn fact(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n * fact((n - 1) as nat)
    }
}

/*
Define an implementation of factorial using machine oriented numbers.  What's going on is interesting as this specification must account for overflow and underflow.  Note the addition of `wrapping_mul` which will solve the overflow problem, but will not match the specification without accounting for various errors.
*/

exec fn fact_exec(x:i32) -> (z:i32)
    requires 0<=x<5,
    ensures z==fact(x as nat),
{
    let mut c: i32 = x;
    let mut i: i32 = 1;
    let mut acc: i32 = 1;
    while i <= x
        invariant
            1 <= i && i <= x + 1,
            // && 1 <= acc
            // && (acc as nat) * fact((x - i + 1) as nat) == fact(x as nat),
        decreases x - i + 1,
    {
        acc = acc * i;
        i = i + 1;
    }
    return acc;
}


spec fn factorialc(n: int) -> (result: int)
    decreases n,
{        
    if n == 0 {
        1
    } else {
        n * factorialc((n - 1) as int)
    }   
}

exec fn factorialcp(n: i64) -> (res: i64)
    ensures
        res == if n == 0 { 1 } else { n * factorialc(n - 1) },
{
    let mut i: i64 = 1;
    let mut acc: i64 = 1;

    while i <= n
        invariant
            1 <= i && i <= n + 1,
            acc == factorialc(i - 1),
        decreases n - i + 1,
    {
        acc = (acc * i) as i64;
        i = (i - 1) as i64;
    }

    acc
}

}
