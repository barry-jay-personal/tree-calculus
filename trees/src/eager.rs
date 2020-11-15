// use fixpoint::fix;

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


impl Computation {
    pub fn new (ps: Vec <Program>) -> Computation {
        Computation {programs : ps}
    }

    
    pub fn eval1 (x:Computation) -> Program  {
        let v = x.programs;
        match (v.get(0), v.get(1), v.get(2)) {
            (Some (x0), Some(x1), Some(x2)) => {
                match x0 {
                    Program::Leaf => x1,
                    Program::Stem(y1) => Program::fork eval( Computation::new(vec![&x2,&y1,&x1,&y1])),
                    Program::Fork(y1,y2) => eval( Computation::new(vec![&x2, &y1,&y2])),
                }
            },
            (Some (x0), Some(x1), None) => Program::fork(x0, x1),
            (Some (x0), _,_) => Program:: stem(x0),
            _ => Program::leaf, 
        }
    }

    
}
