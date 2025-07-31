// generate an abstract syntax data structure and evaluator for a simple
// arithmetic language (numbers, addition, subtraction) in rust.  Decorate the
// rust code with verus specifications.  In Rust, using Verus specifications for
// verifying properties can be helpful for asserting correctness properties in
// your code. Here's a simple example of how you could structure an abstract
// syntax for a simple arithmetic language that supports only numbers, addition,
// and subtraction. Additionally, I will include Verus specifications for some
// straightforward properties.

// To use the Verus features, we assume that the Verus environment and dependencies are configured.
// This code is a representation and will require the Verus setup to verify the correctness.

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use vstd::prelude::*; // Added for Verus post-synthesis

verus! {

// Define an enum to represent the abstract syntax tree (AST) of our arithmetic language
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


proof fn add_comm(l: Box<Expr<int>>, r: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(l,r)) == eval_spec(Expr::Add(r,l)),
{}

// In Verus, we'll need to use specifications to describe properties of
// our structures Here is an example of how you might specify properties
// using Verus for evaluation
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
        Some(n) => match e {
                    Expr::Num(x) =>
                        (n as int)==eval_spec(e.to_int_expr()),
                    Expr::Add(l,r) =>
                        (n as int)==eval_spec(e.to_int_expr()),
                    Expr::Sub(l,r) =>
                        (n as int)==eval_spec(e.to_int_expr()),
                    }
        None => true
    },
    decreases e,
{
    match e {
        Expr::Num(n) => Some(n),
        Expr::Add(left,right)
        =>
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
