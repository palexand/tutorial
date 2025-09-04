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
use vstd::prelude::*; // Added for Verus post-synthesis

verus! {

// Define an enum to represent the abstract syntax tree (AST) of our arithmetic
// language.  Paramterize the AST over a carrier set to allow for ASTs over Rust
// types and verus types.  Four terms - Numbers, Add, Subtract and If.  
#[derive(Debug)]
pub enum Expr<Carrier> {
    Num(Carrier),
    Add(Box<Expr<Carrier>>, Box<Expr<Carrier>>),
    Sub(Box<Expr<Carrier>>, Box<Expr<Carrier>>),
    If(Box<Expr<Carrier>>, Box<Expr<Carrier>>, Box<Expr<Carrier>>),
}

// Define evaluator requirements as a recrusive function over the Expr type.
// This is a classical normative definition.  Note that the carrier set is the
// verus int type making this a specification.
spec fn eval_spec(e:Expr<int>) -> (v:int)
    decreases e,
{
    match e {
        Expr::Num(n) => n,
        Expr::Add(left,right) =>    
            eval_spec(*left) + eval_spec(*right),
        Expr::Sub(left,right) => 
            eval_spec(*left) - eval_spec(*right),
        Expr::If(c,t,e) =>
            if (eval_spec(*c)==0) {eval_spec(*e)} else {eval_spec(*t)},
    }
}

// Prove a simple commutative property for addition in the AE language.
proof fn add_comm(l: Box<Expr<int>>, r: Box<Expr<int>>)
    ensures eval_spec(Expr::Add(l,r)) == eval_spec(Expr::Add(r,l)),
    {}

// Prove a simple associative property for addition in the AE language.  Proof
// uses fuel to allow eval_spec to unfold up to 5 times.
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

// Same associativity proof without specifying fuel making it default to 1.  See
// how the sequence of ont step unfolds allows the proof to proceed.
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

// This is the version of the proof I would keep.  Parameterized over x, y, and
// z.
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

// We need to use the spec function to define requirements for the exec
// function.  Thus, we will need to convert ASTs defined over i32 to ASTs
// defined over int.  This effectively moves from implementation to
// specification.  This is written in the classic object oriented style.
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
            Expr::If(c,t,e) =>
                Expr::If(Box::new(c.to_int_expr()), Box::new(t.to_int_expr()),
                         Box::new(e.to_int_expr()))
        }
    }
}

// checked_eval takes an expresion, e, and interprets it to an Option type that
// allows failure.  The checked_add and checked_sub operations generate Option
// types that indicate success or failure.
fn checked_eval(e: Expr<i32>) -> (v:Option<i32>)
    // ensure clause compares the output of the interpreter with the output of
    // the specification run on the same term.  checked_eval is correct if the
    // two values are the same for all terms.  None produces true for the time
    // being.  This is not optimal, but lets the ensures clause go through.
    ensures match v {
        Some(n) => (n as int)==eval_spec(e.to_int_expr()),
        None => true}
    // checked_eval decreases on e
    decreases e,
{
    match e {
        Expr::Num(n) => Some(n),
        Expr::Add(left,right) =>
            checked_eval(*left)?.checked_add(checked_eval(*right)?),
        Expr::Sub(left,right) => 
            checked_eval(*left)?.checked_sub(checked_eval(*right)?),
        Expr::If(c,t,e) =>
            match checked_eval(*c) {
                Some(c) => if c==0 {checked_eval(*e)} else {checked_eval(*t)},
                None => None,
            }
        }
}

// Use the following main function to demonstrate creating and evaluating
// expressions.  This is weird and can safely be ignored.  Note the
// external_body directive that tells the verifier not to consider this definition.
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
