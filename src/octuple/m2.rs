use vstd::prelude::*;

verus!{

use crate::octuple::m1::*;

// This is a nifty way to import properties of min without importing the
// implementation of min.
proof fn test() {
    lemma_min(10,20);
    assert(min(10,20)==10);
    lemma_min(100,200);
    assert(min(100,200)==100);
}

}
