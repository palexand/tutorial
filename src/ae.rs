// generate an abstract syntax data structure and evaluator for a simple
// arithmetic language (numbers, addition, subtraction) in rust.  Decorate the
// rust code with verus specifications.  In Rust, using Verus specifications for
// verifying properties can be helpful for asserting correctness properties in
// your code. Here's a simple example of how you could structure an abstract
// syntax for a simple arithmetic language that supports only numbers, addition,
// and subtraction. Additionally, I will include Verus specifications for some
// straightforward properties.

// To use the Verus features, we assume that the Verus environment and
// dependencies are configured.  This code is a representation and will require
// the Verus setup to verify the correctness.

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::prelude::*; // Added for Verus post-synthesis

verus! {

// Define an enum to represent the abstract syntax tree (AST) of our arithmetic
// language
#[derive(Debug)]
pub enum Expr<Carrier> {
    Num(Carrier),
    Add(Box<Expr<Carrier>>, Box<Expr<Carrier>>),
    Sub(Box<Expr<Carrier>>, Box<Expr<Carrier>>),
}

spec fn eval_spec(e:Expr<int>) -> (v:int)
    decreases e,
{
    match e {
        Expr::Num(n) => n,
        Expr::Add(left,right) =>    
            eval_spec(*left) + eval_spec(*right),
        Expr::Sub(left,right) => 
            eval_spec(*left) - eval_spec(*right),
    }
}

// Prove a simple commutative property for addition in the AE language.
proof fn add_comm(l: Box<Expr<int>>, r: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(l,r)) == eval_spec(Expr::Add(r,l)),
    {}

proof fn add_assoc_ex(x: Box<Expr<int>>, y: Box<Expr<int>>, z: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(
                Box::new(Expr::Add(
                    Box::new(Expr::Num(1int)),
                    Box::new(Expr::Num(2int)))),
                Box::new(Expr::Num(3int))))
         == eval_spec(Expr::Add(
                    Box::new(Expr::Num(1int)),
                    Box::new(Expr::Add(
                             Box::new(Expr::Num(2int)),
                             Box::new(Expr::Num(3int)))))),
{   reveal_with_fuel(eval_spec,5);
}

proof fn add_assoc_no_fuel_ex(x: Box<Expr<int>>, y: Box<Expr<int>>, z: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(
                Box::new(Expr::Add(
                    Box::new(Expr::Num(1int)),
                    Box::new(Expr::Num(2int)))),
                Box::new(Expr::Num(3int))))
         == eval_spec(Expr::Add(
                    Box::new(Expr::Num(1int)),
                    Box::new(Expr::Add(
                             Box::new(Expr::Num(2int)),
                             Box::new(Expr::Num(3int)))))),
{   
    assert( eval_spec(Expr::Num(1int))==1);
    assert( eval_spec(Expr::Num(2int))==2);
    assert( eval_spec(Expr::Num(3int))==3);
    assert( eval_spec(Expr::Add(Box::new(Expr::Num(1int)),(Box::new(Expr::Num(2int)))))==3int);
    assert( eval_spec(Expr::Add(Box::new(Expr::Num(2int)),(Box::new(Expr::Num(3int)))))==5int);
}

// The trick was fuel.  Forgot about that.  Solvers will limit unroll depth
// to 1 if fuel is not specified.
proof fn add_assoc(x: Box<Expr<int>>, y: Box<Expr<int>>, z: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(
                Box::new(Expr::Add(
                    x,
                    y)),
                z))
         == eval_spec(Expr::Add(
                    x,
                    Box::new(Expr::Add(
                             y,
                             z)))),
{   reveal_with_fuel(eval_spec,5);
}

// In Verus, we'll need to use specifications to describe properties of our
// structures Here is an example of how you might specify properties using Verus
// for evaluation
impl Expr<i32> {
    spec fn to_int_expr(self) -> Expr<int> 
    decreases self,
    {
        match self {
            Expr::Num(n) => Expr::Num(n as int),
            Expr::Add(l, r) =>
                Expr::Add(Box::new(l.to_int_expr()), Box::new(r.to_int_expr())),
            Expr::Sub(l, r) =>
                Expr::Sub(Box::new(l.to_int_expr()), Box::new(r.to_int_expr())),
        }
    }
}

fn checked_eval(e: Expr<i32>) -> (v:Option<i32>)
    ensures match v {
        Some(n) => (n as int)==eval_spec(e.to_int_expr()),
        None => true
    },
    decreases e,
{
    match e {
        Expr::Num(n) => Some(n),
        Expr::Add(left,right) =>
            checked_eval(*left)?.checked_add(checked_eval(*right)?),
        Expr::Sub(left,right) => 
            checked_eval(*left)?.checked_sub(checked_eval(*right)?) 
    }
}

// Use the following main function to demonstrate creating and evaluating
// expressions
#[verifier::external_body]
fn main() {
    // Should evaluate to 3
    let expr: Expr<i32> = Expr::Num(3);
    let result = match checked_eval(expr) 
                        {
                            Some(x) => std::println!("{}",x),
                            None => std::println!("{}",0)
                        };
    // Should evaluate to 25
    let expr = Expr::Add(Box::new(Expr::Num(10)), Box::new(Expr::Sub(Box::new(Expr::Num(20)), Box::new(Expr::Num(5)))));
    let result = match checked_eval(expr) 
                        {
                            Some(x) => std::println!("{}",x),
                            None => std::println!("{}",0)
                        };
    }
}
