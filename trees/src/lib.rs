/**********************************************************************/
/* Copyright 2020 Barry Jay                                           */
/*                                                                    */ 
/* Permission is hereby granted, free of charge, to any person        */ 
/* obtaining a copy of this software and associated documentation     */ 
/* files (the "Software"), to deal in the Software without            */ 
/* restriction, including without limitation the rights to use, copy, */ 
/* modify, merge, publish, distribute, sublicense, and/or sell copies */ 
/* of the Software, and to permit persons to whom the Software is     */ 
/* furnished to do so, subject to the following conditions:           */ 
/*                                                                    */ 
/* The above copyright notice and this permission notice shall be     */ 
/* included in all copies or substantial portions of the Software.    */ 
/*                                                                    */ 
/* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    */ 
/* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF */ 
/* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              */ 
/* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        */ 
/* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       */ 
/* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, */ 
/* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      */ 
/* DEALINGS IN THE SOFTWARE.                                          */ 
/**********************************************************************/

/**********************************************************************/
/*            Reflective Programming in Tree Calculus                 */
/*               Implementation in Rust                               */
/*                                                                    */
/*                     Barry Jay                                      */
/*                                                                    */
/**********************************************************************/


// See main.rs for an overview. 



extern crate nom;

use nom::{
  branch::alt,
  character::complete::{char, multispace0},
  error::ParseError,
  multi::{fold_many0},
  sequence::{delimited},
  IResult, Parser,
};

use std::fmt;
use std::rc::Rc;
use std::mem;


/// Programs may be a leaf, stem or fork, with branches that are values, 
/// i.e. programs with reference counters.
#[derive(Debug,Clone,PartialEq)]
pub enum Program { 
    Leaf,
    Stem(Rc<Program>),
    Fork(Rc<Program>, Rc<Program>),
}

use crate::Program::{Leaf, Stem, Fork};


/// Trees are either values (i.e. programs), or applications. 

#[derive(Debug,Clone,PartialEq)]
pub enum Tree {
    Value(Rc<Program>),
    Apply(Box<Tree>, Box<Tree>),
}

use crate::Tree::{Value,Apply};


/// Kin are either parents or children. 
/// Parents are always programs.
pub struct Kin {
    parent: bool,
    tree: Tree,
}


/// a configuration consists of a graft program and a list of kin,
/// from which the original tree can be reconstructed 
pub struct Config {
    graft : Rc<Program>,
    host: Vec<Kin> 
}


impl Config {

 
    pub fn new(g:Rc<Program>, h:Vec<Kin>) -> Self {
	Config { graft:g, host:h} 
    }

    pub fn enforce_invariant(mut graft:Tree, mut host:Vec<Kin>) -> Self {
	while let Apply(t1,t2) = graft {
	    graft = *t1;
	    host.push(Kin {parent:false, tree:*t2} );
	}; 
	if let Value(v) = graft {
	    Config::new(v,host)
	}
	else { panic! {"enforce_invariant"} }
    }
}

kimpl Tree {
	
    pub fn val(v:Rc<Program>) -> Self {
        Value(v) }

    pub fn new () -> Self {
	Value(Rc::new(Leaf))
    }

    pub fn app (t1:Tree,t2:Tree) -> Tree {
         Apply (Box::new(t1),Box::new(t2))
    }

   /// apply_values takes two programs and produces a tree.
    pub fn apply_values(v1:Rc<Program>, v2:Rc<Program>) -> Tree {

        match &*v1 {
            Leaf => Value(Rc::new(Stem(v2))),
            Stem(v11) => Value(Rc::new(Fork(Rc::clone(&v11),v2))),
            Fork(v11,v12) => {
		match &*Rc::clone(&v11) {
		    Leaf => Value(Rc::clone(&v12)),  // k-rule 
		    Stem(v111) => {                  // s-rule
			let v2c: Rc<Program> = Rc::clone(&v2); 
			Tree::app(Tree::app(Value(Rc::clone(&v12)),Value(Rc::clone(&v2c))),
				  Tree::app(Value(Rc::clone(&v111)),Value(Rc::clone(&v2c)))
			)
		    }, 
		    Fork(v111,v112) => {            // f-rule
			Tree::app(Tree::app(Value(Rc::clone(&v2)),Value(Rc::clone(&v111))),
				  Value(Rc::clone(&v112)))
		    },
		}
	    }
	}
    }


    /// evaluation is eager; 
    pub fn eval(t:Tree) -> Tree {

	let mut config = Config:: enforce_invariant(t, vec![]); 
	
	while let Some(k) = config.host.pop() {
	    
	    if k.parent {  // swap child and parent
		match k.tree {
		    Value(v) => 
			config.host.push(
			    Kin { parent:false, tree : Tree::val(mem::replace(&mut config.graft, v)) }
			),
		    _ => {}, // can't happen, since parents are values 
		}
	    }
	    else {
		match k.tree {
		    Value(v) => 
		    {config = Config:: enforce_invariant(Tree::apply_values(config.graft, v), config.host)
		    },
		    _ => { // push the graft as parent 
			config.host.push(
			    Kin { parent:true, tree : Tree::val(mem::replace(&mut config.graft, Rc::new(Leaf))) }
			);
			config = Config:: enforce_invariant(k.tree, config.host);  //  enforce the graft invariant from the child 
		    },
		}
	    }
	};
	Tree::val(config.graft)
    }



}

// Display of programs and trees 


impl fmt::Display for Program {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Leaf => write!(f, "~"), 
            Stem(v) => {
		match &*(Rc::clone(&v)) {
		    Leaf => write!(f,"K"),
		    _ => write!(f,"~({})", *v),
		}
	    },
            Fork(v1,v2) => 
		match &*(Rc::clone(&v1)) {
		    Leaf => {
			match &*(Rc::clone(&v2)) {
			    Leaf => write!(f,"K~"),
			    _ => write!(f,"K({})", *v2),
			}
		    },
 		    _ =>
			match &*(Rc::clone(&v2)) {
			    Leaf => write!(f,"~({})~",*v1),
			    _ => write!(f,"~({})({})", *v1, *v2),
			}
		}
	}
    }
}


impl fmt::Display for Tree {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value(v) => v.fmt(f),
            Apply(t1,t2) =>  write!(f,"{}({})", t1, t2),
        }
    }
}


// parsing of trees 

impl Tree {
     
    pub fn leaf_p(i: &str) -> IResult<&str, Tree> {
	match nom::bytes::complete::tag("~")(i) {
	    Ok((remaining_input,_)) => Ok((remaining_input,Tree::Value(Rc::new(Leaf)))),
	    Err(e) => Err(e)
	}
    }

    pub(self) fn ws<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(f: F) -> impl Parser<&'a str, O, E> {
	delimited(multispace0, f, multispace0)
    }


    pub(self) fn delimited_tree_p(input: &str) -> IResult<&str, Tree> {
	Tree::ws(
	    alt((
		Tree::leaf_p,
		delimited(
		    char('('),
		    Tree::parser, 
		    char(')')
		)
	    ))).parse(input)
    }

    pub fn parser(input: &str) -> IResult<&str, Tree> {
	match Tree::delimited_tree_p(input) {
	    Ok((remainder, t)) =>
		fold_many0 (Tree::delimited_tree_p,t, Tree::app)(remainder),
	    e => e,
	}
    }
    


}

// read_eval_print

impl Tree {
    
    pub fn read_eval_print ( input: &str) {
	match Tree::parser(input) {
	    Ok (("", t)) => println!("{} = {}", input, Tree::eval(t)),
	    e => panic! {"parsing failed: {:?}",e},
	}
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use super::Tree;
    use crate::Program::{Leaf, Stem, Fork};


    fn leaf() -> Tree { Tree::new() }
    fn k_op() -> Tree { Tree::val (Rc::new(Stem(Rc::new(Leaf) ) )) }
    fn k_op_t() -> Tree { Tree::app(leaf(),leaf()) }
    fn id() -> Tree { Tree::val (Rc::new(Fork(Rc::new(Stem(Rc::new(Leaf))), Rc::new(Stem(Rc::new(Leaf)))))) }
    fn id_t() -> Tree {Tree::app (Tree::app(leaf(), k_op_t()), k_op_t()) }
    
    #[test]
    fn parser_test() {
	assert_eq!(Tree::parser("~"), Ok(("",leaf())));
	assert_eq!(Tree::parser("  ( ~)\t  "), Ok(("",leaf())));
	
	assert_eq!(Tree::parser("~(~~)(~~)"), Ok(("",id_t())));
    }

    #[test]
    fn eval_test() {
	assert_eq!(Tree::eval(id_t()), id()); 
	assert_eq!(Tree::eval(Tree::app(id_t(),leaf())), leaf());
	assert_eq!(Tree::eval(Tree::app(id_t(),k_op())), k_op());
    }

 }

  
