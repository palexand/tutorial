use vstd::prelude::*;

verus!{

#[verifier::external_body]
fn print_two_digit_number(x:i8)
    requires -99 <= x < 100,
{
    println!("The answer is {}",x)
}

fn octuple(x1:i8) -> (x8:i8)
    requires -16 <= x1 < 16,
    ensures x8 == 8*x1,
{
    let x2: i8 = x1 + x1;
    let x4: i8 = x2 + x2;
    x4 + x4
}

fn main() {
    let n: i8 = octuple(10);
    assert(n==80);
    print_two_digit_number(n);
}

fn test_consts() {
 let u: u8 = 1;
    assert({
        let i: int = 2;
        let n: nat = 3;
        0int <= u < i < n < 4
    });
}

spec fn min(x: int, y: int) -> (z: int) {
    if x <= y {
        x
    } else { 
        y
    }
}

fn test() {
    assert(min(10,20) == 10);
    assert(min(100,200)== 100);
}

}