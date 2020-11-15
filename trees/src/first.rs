// A tail-recursive, stack-based implementation of tree calculus
//
// Barry Jay


/*
struct Node {
    elem : Program,
    left: Link,
    right: Link 
    Label: Program,
    Children: Option<Box<Branches>>
}

#[derive(Debug)]
struct Branches {
    Left: Tree,
    Right: Tree,
}

use crate::Tree::{Label, Children};
use crate::Branches::{Left, Right};


/// Kin may be either a child tree, or a parent value
pub enum Kin {
    Child(Tree),
    Parent(Rc<Program>)
}


impl Kin {

    fn val (t:Tree) -> Rc<Program> {
	match t {
	    Value(v) => v,
	    _ => panic! {"this tree is not a value"}
	}
    }

    fn push_children (mut t:Tree, mut host:Vec<Kin>)  {
			    while let Application(t1,t2) = t {
				t = *t1;
				host.push(Kin::Child(*t2));
			    };
    }


 	
    /// evaluation is eager; 
    pub fn eval(v1:Program, v2:Program) -> Program {

	let mut graft: Rc<Program> = Rc::new(v1);
	let mut host = vec![Kin::Child(Value(Rc::new(v2)))]; 

	// pop the next of kin from the host
	while let Some(k) = host.pop() { 
	    match k {
		Kin::Parent(f) => {                                                      // if the kin is a parent then
		    host.push(Kin::Child(Value(graft)));                  // push the graft as a child
		    graft = Rc::clone(&f);                            // graft the parent
		},
		Kin::Child(t1) => {                                      // if the kin is a child then 
		    mxb
atch t1 {
			Value(v2) => {                     // if the child is a value 
			    let mut reduct = Tree::apply_values(*Rc::clone(&graft),*Rc::clone(&v2)); // then apply the evaluation rules
			    // push the children of the graft, until it is a value
			    while let Application(t1,t2) = reduct {
				reduct = *t1;
				host.push(Kin::Child(*t2));
			    };
			    graft = Kin::val(reduct);
			},
			_ => {			                 // else (since evaluation is eager)
			    host.push(Kin::Parent(Rc::clone(&graft)));        // push the parent
			    let mut parent = t1;
			    while let Application(t1,t2) = parent {
				parent = *t1;
				host.push(Kin::Child(*t2));
			    };
			    graft = Kin::val(parent); 
			},
		    }
		},
	    }
	};    
	*Rc::clone(&graft)
    }
}

     */
    
