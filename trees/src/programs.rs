// A tail-recursive, stack-based implementation of tree calculus
//
// Barry Jay 

// use std::fmt;
use std::rc::Rc;
// use syn::{parse_str, parenthesized, bracketed, braced};
// use syn::parse::{Parse, ParseStream, Result};


/// Programs may be a leaf, stem or fork, with branches that are values, 
/// i.e. programs with reference counters.
#[derive(Debug)]
pub enum Program { 
    Leaf,
    Stem(Rc<Program>),
    Fork(Rc<Program>, Rc<Program>),
}

use crate::Program::{Leaf, Stem, Fork};


/// Trees are either values (i.e. programs), or applications. 

#[derive(Debug)]
pub struct Tree {
    head : Link
}
#[derive(Debug)]
enum Link {
    Value(Program),
    Application(Box<Tree>, Box<Tree>),
}

use crate::Link::{Value,Application};


impl Tree {

    pub fn val(v:Program) -> Self {
        Tree { head: Link::Value(v) }
    }

    pub fn app (t1:Tree,t2:Tree) -> Tree {
         Tree {
	     head: Application (Box::new(t1),Box::new(t2))
	 }
     }

   // apply_values takes two programs and produces a tree.
    
    pub fn apply_values(v1:Program,v2:Program) -> Tree {
        match v1 {
            Leaf => val(Stem(Rc::new(v2))),
            Stem(v11) => val(Fork(Rc::clone(&v11),Rc::new(v2))),
            Fork(v11,v12) => {
		match &*Rc::clone(&v11) {
		    Leaf => Value(Rc::clone(&v12)),  // k-rule 
		    Stem(v111) => {                  // s-rule
			let v2c: Rc<Program> = Rc::new(v2); 
			Tree::app(Tree::app(Value(Rc::clone(&v12)),Value(Rc::clone(&v2c))),
				  Tree::app(Value(Rc::clone(&v111)),Value(Rc::clone(&v2c)))
			)
		    }, 
		    Fork(v111,v112) => {            // f-rule
			Tree::app(Tree::app(Value(Rc::new(v2)),Value(Rc::clone(&v111))),
				  Value(Rc::clone(&v112)))
		    },
		}
	    }
	}
    }
}



