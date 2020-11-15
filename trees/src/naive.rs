// use fixpoint::fix;

/// Trees are either nodes or applications of trees. 

#[derive(Debug)]
pub enum Tree {
    Node,
    App(Box <Tree>, Box<Tree>),
}


impl Tree {
    pub fn node() -> Tree { Tree::Node }
    
    pub fn app (t1:Tree,t2:Tree) -> Tree {
        Tree::App(Box::new(t1),Box::new(t2))
    }

}

/// Programs may be a leaf, stem or fork, with branches that are programs. 

#[derive(Debug)]
pub enum Program {
    Leaf,
    Stem(Box < Program>),
    Fork(Box <Program>, Box<Program>),
}

/// Computations are represented by a vector of programs that are the arguments of an implicit node.
/// Vectors with 0,1 and 2 entries correspond to binary trees, and so will evaluate to programs directly.
/// Vectors with 3 or more entries must be evlauated eagerly, so  all thunks evauate to programs. 

#[derive(Debug)]
pub struct Computation {
    programs: Vec <Program >,
}

impl Program {
    pub fn leaf () -> Program {
        Program::Leaf 
    }

    pub fn stem(t:Program) -> Program {
        Program::Stem(Box::new(t))
    }

    pub fn fork(t1:Program,t2:Program) -> Program {
        Program::Fork(Box::new(t1),Box::new(t2))
    }

}

