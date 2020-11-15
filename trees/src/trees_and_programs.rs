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

impl Tree {

    pub fn eval (t:Tree) -> Program {
        match t {
            Tree::Node => Program::leaf(),
            Tree::App(t1,t2) => Program::leaf(),
        }
    }
}
