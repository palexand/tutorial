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

spec fn fact(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n * fact((n - 1) as nat)
    }
}

exec fn fact_exec(x:i8) -> (z:i32)
    requires 0<=x<5,
    ensures z==fact(x as nat),
{
    let mut c: i8 = x;
    let mut acc: i32 = 1;
    while c > 0
        invariant c >= 0,
        decreases c,
    {
        c = c-1;
        acc =  (c as i32) * acc;
    }
    return acc as i32;
}

}