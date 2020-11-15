// A tail-recursive, stack-based implementation of tree calculus
//
// Barry Jay 

#![cfg(feature = "alloc")]
extern crate nom;


use nom::{
  branch::alt,
  bytes::complete::{tag, take},
  character::complete::{anychar, char, multispace0, none_of},
  combinator::{map, map_opt, map_res, value, verify},
  error::ParseError,
  multi::{fold_many0, separated_list0},
  number::complete::double,
  sequence::{delimited, preceded, separated_pair},
  IResult, Parser,
};

use std::fmt;
use std::rc::Rc;
use std::mem;
//use syn::{parenthesized};
// use syn::{parse_str, parenthesized, bracketed, braced};
//use syn::parse::{Parse, ParseStream, Result};


/// Programs may be a leaf, stem or fork, with branches that are values, 
/// i.e. programs with reference counters.
#[derive(Debug)]
pub enum Program { 
    Leaf,
    Stem(Rc<Program>),
    Fork(Rc<Program>, Rc<Program>),
}

use crate::Program::{Leaf, Stem, Fork};



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


/// Trees are either values (i.e. programs), or applications. 

#[derive(Debug)]
pub enum Tree {
    Value(Rc<Program>),
    Apply(Box<Tree>, Box<Tree>),
}

use crate::Tree::{Value,Apply};



impl fmt::Display for Tree {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value(v) => v.fmt(f),
            Apply(t1,t2) =>  write!(f,"{}({})", t1, t2),
        }
    }
}



#[macro_export]
macro_rules! tree {
    ( ~ ( ( $t1:expr ,  $t2:expr ) ) ) => {  Apply(Box::new(t1), Box::new(t2)) } ;
    ( ~ ( ( $t:expr ) ) ) => {  Apply(Value(Leaf), Box::new(t)) } ;
    (~) => { Value(Rc::new(Leaf)) };
}


impl Tree {

    pub fn val(v:Rc<Program>) -> Self {
        Value(v) }

    pub fn new () -> Self {
	Value(Rc::new(Leaf))
    }

    pub fn app (t1:Tree,t2:Tree) -> Tree {
         Apply (Box::new(t1),Box::new(t2))
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
    graft : Rc<Program>,
    host: Vec<Kin> 
}


impl Config {

 
    pub fn new(g:Rc<Program>, h:Vec<Kin>) -> Self {
	Config { graft:g, host:h} 
    }

    pub fn restore_invariant(mut graft:Tree, mut host:Vec<Kin>) -> Self {
	while let Apply(t1,t2) = graft {
	    graft = *t1;
	    host.push(Kin {parent:false, tree:*t2} );
	}; 
	if let Value(v) = graft {
	    Config::new(v,host)
	}
	else { panic! {"restore_invariant"} }
    }
    pub fn apply_graft_to_value(mut self, v:Rc<Program>) -> Self {
	
	match &*Rc::clone(&self.graft) {
	    Leaf => {
		self.graft = Rc::new(Stem(v)); 
		self
	    },
	    Stem (v1) => {
		self.graft = Rc::new(Fork(Rc::clone(v1),v));
		self
	    },
	    Fork (v1,v2) => {
		match &*Rc::clone(&v1) {
		    Leaf => { // K-rule 
			self.graft = Rc::clone(&v2);
			self
		    },
		    Stem (v11) => { // S-rule
 			self.host.push( Kin {
			    parent:false,
			    tree: Tree::app(Tree::val(Rc::clone(&v11)),Tree::val(Rc::clone(&v)))
			});
			self.host.push( Kin {
			    parent:false,
			    tree:Tree::val(v)
			});
			self.graft = Rc::clone(v2);
			self
		    },
		    Fork (v11,v12) => { // F-rule
			self.host.push( Kin {
			    parent:false,
			    tree: Tree::val(Rc::clone(v12))
			});
			self.host.push( Kin {
			    parent:false,
			    tree:Tree::val(Rc::clone(v11))
			});
			self.graft = v;
			self
		    },
		}
	    }
	}
    }
}


impl Tree {
	

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
    pub fn eval(v1:Program,v2:Program) -> Tree {

	let mut config = Config::new(Rc::new(v1), vec![Kin { parent:false, tree: Tree::val(Rc::new(v2)) } ]); 
	
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
		    {config = Config:: restore_invariant(Tree::apply_values(config.graft, v), config.host)
		    },
		    _ => { // push the graft as parent 
			config.host.push(
			    Kin { parent:true, tree : Tree::val(mem::replace(&mut config.graft, Rc::new(Leaf))) }
			);
			config = Config:: restore_invariant(k.tree, config.host);  //  restore the graft invariant from the child 
		    },
		}
	    }
	};
	Tree::val(config.graft)
    }

}

impl Tree {
    
fn leaf_parser(i: &str) -> IResult<&str, Program> {
    match complete::tag("~")(i) {
	Ok((remaining_input,_)) => Ok((remaining_input,Leaf)),
	Err(e) => Err(e)
    }
}


fn ws<'a, O, E: ParseError<&'a str>, F: Parser<&'a str, O, E>>(f: F) -> impl Parser<&'a str, O, E> {
  delimited(multispace0, f, multispace0)
}


fn object(input: &str) -> IResult<&str, HashMap<String, Tree>> {
  map(
    delimited(
      char('{'),
      ws(separated_list0(
        ws(char(',')),
        separated_pair(string, ws(char(':')), json_value),
      )),
      char('}'),
    ),
    |key_values| key_values.into_iter().collect(),
  )(input)
}

fn json_value(input: &str) -> IResult<&str, Tree> {

    alt((
	leaf_parser, 
//    map(object, Object),
  ))(input)
}

fn json(input: &str) -> IResult<&str, Tree> {
  ws(json_value).parse(input)
}

}
