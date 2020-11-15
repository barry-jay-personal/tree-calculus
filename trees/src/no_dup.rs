// A tail-recursive, stack-based implementation of tree calculus
//
// Barry Jay 

// use std::fmt;
// use std::rc::Rc;
// use syn::{parse_str, parenthesized, bracketed, braced};
// use syn::parse::{Parse, ParseStream, Result};

use std::mem;


/// Trees have zero, one or two branches 

#[derive(Debug)]
pub struct Tree {
    head : Link
}

/// None represents a leaf 
pub type Link = Option<Box<App>>;

/// other trees are (boxed) applications
#[derive(Debug)]
pub struct App {
    left: Tree,
    right: Tree,
}

impl Tree {

    pub fn new() -> Self {
        Tree { head: None }
    }

    pub fn app (t1:Tree, t2:Tree) -> Tree {
	Tree { head: Some(Box::new(App {left:t1,right:t2}))}
    }

     pub fn push (mut self, t:Tree) {
       let new_node = Box::new(App {
            left:  mem::replace(&mut self, Tree::new()),
	    right: t
        });

        self.head = Some(new_node);
    }

    pub fn pop (mut self) -> Option <Tree> {
        self.head.take().map(|node| {
            self = node.left;
            node.right 
        })
    }

    pub fn peek_left(&self) -> Option<&Tree> {
	self.head.as_ref().map(|node| {
            &node.left
	})
    }
    
    pub fn peek_right(&self) -> Option<&Tree> {
	self.head.as_ref().map(|node| {
            &node.right
	})
    }

    pub fn is_leaf (&self) -> bool {
	match self.head.as_ref() {
	    None => true,
	    _ => false
	}
    }
    
    pub fn is_stem (&self) -> bool {
	match self.head.as_ref() {
	    Some(node) => Tree::is_leaf (&node.left),
	    _ => false,
	}
    }
	
    pub fn is_fork (&self) -> bool {
	match self.head.as_ref() {
	    Some(node) => Tree::is_stem (&node.left),
	    _ => false,
	}
    }

    pub fn is_factorable (&self) -> bool {
	Tree::is_leaf(self) || Tree::is_stem(self) || Tree::is_fork(self)
    }

 
}

pub enum Factorable { 
    Leaf,
    Stem(Tree),
    Fork(Tree,Tree),
}

use crate::Factorable::{Leaf, Stem, Fork};

impl Factorable {

    pub fn tree2factorable (t:Tree) -> Self {
	match t.head { 
	    None => Leaf, 
	    Some(mut node) => {
		let nr = mem::replace(&mut node.right, Tree::new());
		match node.left.head  {
		    None => Factorable::Stem(nr),
		    Some(mut node1) => {
			let nr1 = mem::replace(&mut node1.right, Tree::new());
			match node1.left.head  {
			    None => Factorable::Fork(nr1,nr),
			    Some(_) => panic! {"tree2factorable failed"},
			}
		    },		    
		}
	    }
	}
    }
    
    pub fn factorable2tree (v:Factorable) -> Tree {
	match v { 
	    Leaf => Tree::new(), 
	    Stem(v1) => Tree { head: Some(Box::new(App {left:Tree::new(), right: v1})) },
	    Fork(v1,v2) => Tree { head: Some(Box::new(App {left:Tree::new(), right: v1})) },
	}
    }
}



/// Kin are either parents or children. 
/// Parents are always programs.
pub struct Kin {
    parent: bool,
    tree: Tree,
}

/// a configuration consists of a subject program and a list of kin 
pub struct Config {
    graft : Tree,
    host: Vec<Kin> 
}


impl Config {

    pub fn restore_invariant(mut self) -> Self {
	while !(Tree::is_factorable(&self.graft)) {
	    match self.graft.head {
		Some(node) => {
		    self.graft = node.left;
		    self.host.push(Kin {parent:false, tree:node.right} );
		},
		None => panic! {"graft is not yet a program"},
	    }
	}
	; self
    }
 
    pub fn new(g:Tree, h:Vec<Kin>) -> Self {
	Config::restore_invariant(Config { graft:g, host:h} )
    }

    pub fn apply_graft_to_value(mut self, v:Tree) -> Self {
	let graft = mem::replace(&mut self.graft, Tree::new()); 
	match Factorable::tree2factorable(graft) {
	    Leaf => {
		self.graft = Tree::app (Tree::new(), v) ;
		self
	    },
	    Stem (v1) => {
		self.graft = Tree::app (Tree::app(Tree::new(), v1), v); 
		self
	    },
	    Fork (v1,v2) => {
		match Factorable::tree2factorable(v1) {
		    Leaf => { // K-rule 
			self.graft = v2;
			self
		    },
		    Stem (v11) => { // S-rule
 			self.host.push( Kin {
			    parent:false,
			    tree: Tree::app(v11,v)
			});
			self.host.push( Kin {
			    parent:false,
			    tree:v
			});
			self.graft = v2;
			self
		    },
		    Fork (v11,v12) => { // F-rule
			self.host.push( Kin {
			    parent:false,
			    tree: v12
			});
			self.host.push( Kin {
			    parent:false,
			    tree:v11
			});
			self.graft = v2;
			self
		    },
		}
	    }
	}
    }
}

		    /*
Some(node1) => { // a fork, so match on the first argument
			match node1.left.head {
			    None => { // K-rule
				self.graft = node.right;
				self
			    },
			    Some(mut node2) => {
				let node22 =mem::replace(&mut node2.right, Tree::new());
				match node2.left.head  {
				    None => { // S-rule
					self.host.push( Kin {
						parent:false,
						tree: Tree {
						    head : Some ( Box::new(App {
							left: Tree { head: Some(node2)},
							right: v
						    } ))
						}
					});
					self.graft = node22;
					self
				    },
				    Some(node3) => { // F-rule
					self
				    }
				}
			    }
			}
			
		    },
		 
		    
	    }
	}
    }
}


impl Tree {
	
    /// evaluation is eager; 
    pub fn eval(t:Tree) -> Tree {

	let mut config = Config::new(t, vec![]); 
	
	while let Some(k) = config.host.pop() { 
	    if k.parent {  // swap child and parent
		config.host.push(
		    Kin { parent:false, tree :mem::replace(&mut config.graft, k.tree) }
		);
	    }
	    else {
		if !(Tree::is_program(&k.tree)) { // swap parent and child 
		    config.host.push(
			Kin { parent:true, tree :mem::replace(&mut config.graft, k.tree) }
		    );
		}
		else { config = config.apply_graft_to_value(k.tree) }
	    }
	};
	config.graft
    }
}

    /* Kin::Parent(f) => {                                       // if the kin is a parent then
		   

			host.push(Kin::Child(Value(graft)));                  // push the graft as a child
		    graft = Rc::clone(&f);                            // graft the parent
		},
		Kin::Child(t1) => {                                      // if the kin is a child then 
		    match t1 {
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

   // apply_values takes two programs and produces a tree.
    
    pub fn apply_values(t1:Tv1:Program,v2:Program) -> Tree {
        match v1 {
            Leaf => Value(Rc::new(Stem(Rc::new(v2)))),
            Stem(v11) => Value(Rc::new(Fork(Rc::clone(&v11),Rc::new(v2)))),
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

*/


*/

