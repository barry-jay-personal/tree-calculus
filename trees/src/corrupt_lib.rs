// A tail-recursive, stack-based implementation of tree calculus
//
// Barry Jay 


use std::fmt;
use std::rc::Rc;
// use syn::{parse_str, parenthesized, bracketed, braced};
// use syn::parse::{Parse, ParseStream, Result};


/// Programs may be a leaf, stem or fork, with branches that are values, 
/// i.e. programs with reference counters.
#[derive(Debug)]
pub enum Program {
    Leaf,
    Stem(Rc<Program>),
    Fork(Rc <Program>, Rc<Program>),
}

/// Trees are either values (i.e. programs with reference counters), or applications of boxed trees. 
#[derive(Debug)]
pub enum Tree {
    Value (Rc<Program>),
    Application (Box<Tree>, Box<Tree>),
}

/// Kin may be either a child tree, or a parent value
pub enum Kin {
    Child(Tree),
    Parent(Rc<Program>)
}


impl Kin {

    /// evaluation is eager; 
    pub fn eval_kin(mut graft:Program, mut host:Vec<Kin>) -> Program {

	// pop the next of kin from the host
	while let Some(k) = host.pop() {
	    match k {
		Kin::Parent(f) => {                                      // if the kin is a parent then
		    host.push(Kin::Child(graft));                    // push the graft as a child
		    graft = Tree::Value(f);                            // graft the parent
		},
		Kin::Child(t1) => {                                      // if the kin is a child then 
		    match t1 {
			Tree::Value(v2) => {                     // if the child is a value 
			    let mut reduct = Tree::apply_values(&graft,v2); // then apply the evaluation rules
			    // push the children of the graft, until it is a value
			    while let Tree::Application(t1,t2) = reduct {
				reduct = *t1;
				host.push(Kin::Child(*t2));
			    };
			    graft = reduct;
			},
			_ => {			                 // else (since evaluation is eager)
			    host.push(Kin::Parent(graft));        // push the parent
			    graft = t1;                        // graft the child 
			},
		    }
		},
	    }
	};
	graft
    }		
}

impl Program {

    pub fn eval (v1:Program, v2:Program) -> Program {
	let mut host = vec![Kin::Child(Tree::Value(Rc::new(v2)))]; 
	Kin::eval_kin(v1,host)
    }
}



impl fmt::Display for Program {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Program::Leaf => write!(f, "~"), 
            Program::Stem(v) => write!(f,"~({})",*v),
            Program::Fork(v1,v2) => write!(f,"~({},{})", *v1, *v2),
        }
    }
}


impl Program {
    pub fn leaf () -> Program {
        Program::Leaf 
    }

    pub fn stem(t:Program) -> Program {
        Program::Stem(Rc::new(t))
    }

    pub fn fork(t1:Program,t2:Program) -> Program {
        Program::Fork(Rc::new(t1),Rc::new(t2))
    }

 }

impl fmt::Display for Tree {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Tree::Value(v) =>  write!(f, "({})",*v), 
            Tree::Application(t1,t2) => write!(f,"{}{}",  *t1, *t2),
        }
    }
}

// fix!
// impl Parse for Tree {
//    fn parse(input: ParseStream) -> Result<Tree> {
//        let content;
//        parenthesized!(content in input);
//        dbg!(content.to_string());
//        dbg!(input.is_empty());
//        Ok(A {})
//    }
// }


#[macro_export]
macro_rules! tree {
    ( ~ ( ( $t1:expr ,  $t2:expr ) ) ) => {  Tree::Application(Box::new(t1), Box::new(t2)) } ;
    ( ~ ( ( $t:expr ) ) ) => {  Tree::Application(Tree::Value(Program::Leaf), Box::new(t)) } ;
    (~) => { Tree::Value(Rc::new(Program::Leaf)) };
}

impl Tree {
     pub fn app (t1:Tree,t2:Tree) -> Tree {
        Tree ::Application (Box::new(t1),Box::new(t2))
    }

   // apply_rules takes three programs and produces a tree.
    
    pub fn apply_rules(v1:Rc<Program>,v2:Rc<Program>,v3:Rc<Program>) -> Tree {
        match &*v1 {
            Program::Leaf => Tree::Value(v2),
            Program::Stem(v11) => {
		Tree::app(Tree::app(Tree::Value(v2),Tree::Value(Rc::clone(&v3))),
			  Tree::app(Tree::Value(Rc::clone(v11)),Tree::Value(Rc::clone(&v3)))
		)
	    }, 
            Program::Fork(v11,v12) => {
		Tree::app(Tree::app(Tree::Value(v3),Tree::Value(Rc::clone(&v11))),
			  Tree::Value(Rc::clone(&v12)))
	    },
        }
    }

    pub fn apply_values(v1:Rc<Program>,v2:Rc<Program>) -> Tree {
        match &*v1 {
            Program::Leaf => Tree::Value(Rc::new(Program::Stem(v2))),
            Program::Stem(v11) => Tree::Value(Rc::new(Program::Fork(Rc::clone(v11),v2))),
            Program::Fork(v11,v12) => Tree::apply_rules(Rc::clone(v11),Rc::clone(v12),v2),
	}
    }
}


