

/// Programs may be a leaf, stem or fork, with branches that are programs. 

#[derive(Debug)]
pub enum Program<'a> {
    Leaf,
    Stem(&'a Program<'a>),
    Fork(&'a Program<'a>, &'a Program<'a>),
}

impl <'a> Program<'a> {
    pub fn leaf () -> Program <'a> {
        Program::Leaf 
    }

    pub fn stem(t:Program) -> Program<'a> {
        Program::Stem(&t)
    }

    pub fn fork(t1:Program,t2:Program) -> Program<'a> {
        Program::Fork(&t1,&t2)
    }

}

/// Trees are either programs or unevaluated applications of trees. 

#[derive(Debug)]
pub enum Tree<'a> {
    Value (&'a Program<'a>),
    Application (&'a Tree<'a>, Tree<'a>),
}


impl <'a> Tree<'a> {
    pub fn node() -> Tree<'a> {
        Tree :: Value (Box::new(Program::Leaf)) 
    }
    
    pub fn app (t1:Tree,t2:Tree) -> Tree<'a> {
        Tree ::Application (Box::new(t1),Box::new(t2))
    }

}

/// fixpoints as per the separate crate fixpoints


type Lazy<'a, T> = Box<dyn FnOnce() -> T + 'a>;

// fix: (Lazy<T> -> T) -> T
fn fix<'a, T, F>(f: F) -> T
where F: Fn(Lazy<'a, T>) -> T + Copy + 'a
{
    f(Box::new(move || fix(f)))
}

impl <'a> Tree<'a> {

 
    pub fn eval (t:Tree<'a>) -> Tree<'a> {

        fn apply_rules<'a>(v1:Program<'a>,v2:Program<'a>,v3:Program<'a>) -> Tree<'a> {
            match *v1 {
                Program::Leaf => Tree::Value(v2),
                Program::Stem(v11) => Tree::Application(
                    Box::new(Tree::Application(Box::new(Tree::Value(v2)),
                                               Box::new(Tree::Value(v3)))),
                    Box::new(Tree::Application(Box::new(Tree::Value(v11)),
                                               Box::new(Tree::Value(v3))))
                ),
                Program::Fork(v11,v12) => Tree::Application(
                    Box::new(Tree::Application(Box::new(Tree::Value(v3)),
                                               Box::new(Tree::Value(v11)))),
                   Box::new(Tree::Value(v12))
                ),
            }
        }

        fn f <'a> (ev: Lazy<'static,Box<dyn FnOnce(Tree<'a>) -> Tree<'a> >>) -> Box<dyn FnOnce(Tree<'a>) -> Tree<'a> > {
            Box::new(move |t| {
                match t {
                    Tree:: Value (v) =>  Tree::Value(v), 
                    Tree::Application(t1,t2) => {
                        match *t1 {
                            Tree::Application(t11,t12) => 
                                Tree::Application(Box::new(ev()(Tree::Application(t11,t12))),t2),
                            Tree::Value(v1) => {
                                match *t2 {
                                    Tree::Application(t21,t22) => 
                                        Tree::Application(Box::new(Tree::Value(v1)),
                                                          Box::new(ev()(Tree::Application(t21,t22)))),
                                    Tree::Value(v2) =>
                                        match *v1 {
                                            Program::Leaf => Tree::Value(Box::new(Program::Stem(v2))),
                                            Program::Stem(v11) => Tree::Value(Box::new(Program::Fork(v11,v2))),
                                            Program::Fork(v11,v12) => ev()(apply_rules(v11,v12,v2)),
                                        }
                                            
                                }
                            }
                        }
                    }
                }
            })
        }    
        fix(f)(t)
     }
}
