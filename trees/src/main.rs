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

// A tail-recursive implementation of tree calculus
//
// Trees are represented by a configuration consisting of a program (a binary tree) and its kin.
/// The kin form a list of parent programs and child trees.
/// If the next of kin is a child that is a program then a reduction rule is applied to produce a new tree,
/// and then a new configuration,
/// else the program and child are swapped, to produce a new configuration.

/// The functionality is developedin lib.rs.
/// A leaf is given by "~" so that K is "~~". Application is left-associative. 
/// main.rs can be adapted to try experiments. 


use std::rc::Rc;
use crate::Program::{Leaf, Stem, Fork};
use trees::*;

 fn main()  {

     fn leaf() -> Tree { Tree::new() }
     fn k_op() -> Tree { Tree::val (Rc::new(Stem(Rc::new(Leaf) ) )) }
     fn id() -> Tree { Tree::val (Rc::new(Fork(Rc::new(Stem(Rc::new(Leaf))), Rc::new(Stem(Rc::new(Leaf)))))) }
     fn d(t:Tree) -> Tree {Tree::app (leaf(), Tree::app(leaf(), t)) }
     fn wait(s:Tree, t:Tree) -> Tree { Tree::app (d(id()), Tree::app (d(Tree::app (k_op(), s)),Tree::app (k_op(), t))) }

     

     Tree::read_eval_print ("~");
     Tree::read_eval_print ("~~");
     Tree::read_eval_print ("~~~");
     Tree::read_eval_print ("~~~~");
     Tree::read_eval_print ("~(~~)(~~)~");
     Tree::read_eval_print ("~");
     Tree::read_eval_print ("~");

     println!{"wait(K,K) is: {}", Tree::eval(wait(k_op(), k_op()))} ;
     println!{"wait(K,K)I is: {}", Tree::eval(Tree::app(wait(k_op(), k_op()), id())) } ;

  
 }

 
