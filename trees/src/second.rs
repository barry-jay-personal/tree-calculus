use std::fmt;
use std::rc::Rc;
use std::mem;

// use syn::{parse_str, parenthesized, bracketed, braced};
// use syn::parse::{Parse, ParseStream, Result};


/// Programs may be a leaf, stem or fork, with branches that are values, 
/// i.e. programs with reference counters, to allow sharing.
#[derive(Debug)]
pub enum Program { 
    Leaf,
    Stem(Rc<Program>),
    Fork(Rc<Program>, Rc<Program>),
}

use crate::Program::{Leaf, Stem, Fork};

pub struct Tree {
    label: Program,
    branches: Option<Box<Node>>; 

struct Node {
    left: Tree,
    right: Tree,
}

    /*
impl Tree {
    pub fn new() -> Self {
        Tree { root: None }
    }

    pub fn push(&mut self, elem: T) {
    let new_node = Box::new(Node {
        elem: elem,
 	self.root.take().map(|node| {
	    self.root = node.next; 
	    node.elem
         next: self.root.take(), 
    });

    self.root = Some(new_node);
    }

    pub fn pop(&mut self) -> Option {
	self.root.take().map(|node| {
	    self.root = node.next; 
	    node.elem
        })
    }

    pub fn peek(&self) -> Option<&T> {
    self.root.as_ref().map(|node| {
        &node.elem
    })
}

    pub fn peek_mut(&mut self) -> Option<&mut T> {
    self.root.as_mut().map(|node| {
        &mut node.elem
    })
}
}

impl Drop for Tree {
    fn drop(&mut self) {
        let mut cur_link = mem::replace(&mut self.root, None);
        // `while let` == "do this thing until this pattern doesn't match"
        while let Some(mut boxed_node) = cur_link {
            cur_link =  boxed_node.next.take(); 
            // boxed_node goes out of scope and gets dropped here;
            // but its Node's `next` field has been set to None
            // so no unbounded recursion occurs.
        }
    }
}


#[cfg(test)]
mod test {
    use super::Tree;
    #[test]
    fn basics() {
        let mut list = Tree::new();

        // Check empty list behaves right
        assert_eq!(list.pop(), None);

        // Populate list
        list.push(1);
        list.push(2);
        list.push(3);

        // Check normal removal
        assert_eq!(list.pop(), Some(3));
        assert_eq!(list.pop(), Some(2));

        // Push some more just to make sure nothing's corrupted
        list.push(4);
        list.push(5);

        // Check normal removal
        assert_eq!(list.pop(), Some(5));
        assert_eq!(list.pop(), Some(4));

        // Check exhaustion
        assert_eq!(list.pop(), Some(1));
        assert_eq!(list.pop(), None);
    }

    #[test]
    fn peek() {
	let mut list = Tree::new();
	assert_eq!(list.peek(), None);
	assert_eq!(list.peek_mut(), None);
	list.push(1); list.push(2); list.push(3);
	
	assert_eq!(list.peek(), Some(&3));
	assert_eq!(list.peek_mut(), Some(&mut 3));
	list.peek_mut().map(|value| {
            *value = 42
	});
	
	assert_eq!(list.peek(), Some(&42));
	assert_eq!(list.pop(), Some(42));
}  
}


*/
