use std::cell::{RefCell};
use std::rc::Rc;
use std::fmt;
use crate::inputs::Inputs;
use crate::tree::Tree;
#[derive(Clone, Copy)]
pub struct Operator<T> {
    x:fn(&Inputs, &Vec<Rc<RefCell<Tree<T>>>>) -> Option<T>,
    n:&'static str, // FIXME Need to find a way of automatically setting this
}
impl std::fmt::Debug for Operator<f64> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.n)
    }
}

impl Operator<f64> {
    pub fn evaluate(&self, input:&Inputs,
                children:&Vec<Rc<RefCell<Tree<f64>>>>) -> Option<f64> {
        (self.x)(input, children)
    }

    fn o_prod(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>) -> Option<f64> {
        // If any child returns `None` reset this and return `None`
        let mut return_some = true;
        let mut ret = 1.0;
        for c in children.iter() {
            match c.borrow().evaluate(input) {
                Some(n) => ret *=  n,
                None => {
                    return_some = false;
                    break;
                },
            };
        }
        if return_some {
            Some(ret)
        }else{
            None
        }
    }
    fn o_neg(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
             -> Option<f64> {
        match children[0].borrow().evaluate(input){
            Some(n) => Some(-1.0 * n),
            None => None,
        }
    }

    fn o_inv(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
             -> Option<f64> {
        match children[0].borrow().evaluate(input){
            Some(n) => if n > 0.0 || n < 0.0 {
                Some(1.0/n)
            }else{
                None
            },
            None => None,
        }
    }

    fn o_if(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
            -> Option<f64> {
        match children[0].borrow().evaluate(input) {
            Some(c) => if c > 0.0 {
                children[1].borrow().evaluate(input)
            }else{
                children[2].borrow().evaluate(input) 
            },
            None => None,
        }
    }
    fn o_log(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>) -> Option<f64> {
        match children[0].borrow().evaluate(input) {
            Some(c) => if c > 0.0 {
                Some(c.ln())
            }else{
                None
            },
            None => None,
        }
    }
    fn o_mod(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
                   -> Option<f64> {
        match children[0].borrow().evaluate(input) {
            Some(l) => match children[1].borrow().evaluate(input) {
                Some(r) => Some(l % r),
                None => None,
            },
            None => None,        
        }
    }
    fn o_gt(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
            -> Option<f64> {
        match children[0].borrow().evaluate(input) {
            Some(l) => match children[1].borrow().evaluate(input) {
                Some(r) => if l > r {
                    Some(1.0)
                }else if l < r {
                    Some(-1.0)
                }else{
                    Some(0.0)
                },
                None => None,
            },
            None => None,
        }        
    }

    fn o_lt(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>)
            -> Option<f64> {
        match children[0].borrow().evaluate(input) {
            Some(l) => match children[1].borrow().evaluate(input) {
                Some(r) => if l < r {
                    Some(1.0)
                }else if l > r {
                    Some(-1.0)
                }else{
                    Some(0.0)
                },
                None => None,
            },
            None => None,
        }        
    }
    fn o_sum(input:&Inputs, children:&Vec<Rc<RefCell<Tree<f64>>>>) -> Option<f64> {

        // If any child returns `None` reset this and return `None`
        let mut return_some = true;
        let mut ret = 0.0;
        for c in children.iter() {
            match c.borrow().evaluate(input) {
                Some(n) => ret += n,
                None => {
                    return_some = false;
                    break;
                },
            };
        }
        if return_some {
            Some(ret)
        }else{
            None
        }
    }

    pub fn new(name:&'static str) -> Operator<f64> {
        Operator {
            x:match name {
                "Sum" => Operator::o_sum,
                "Lt" => Operator::o_lt,
                "Gt" => Operator::o_gt,
                "Mod" => Operator::o_mod,
                "Prod" => Operator::o_prod,
                "Log" => Operator::o_log,
                "If" => Operator::o_if,
                "Inv" => Operator::o_inv,
                "Neg" => Operator::o_neg,
                _ => panic!("{}", name),

            },
            n:name,
        }
    }
}
#[cfg(test)]
mod test {
    use crate::tree::Tree;
    use crate::tree::TerminalType;
    use crate::inputs::Inputs;
    use super::Operator;
    use std::cell::{RefCell};
    use std::rc::Rc;
    #[test]
    fn _if() {
        let t1 = Rc::new(RefCell::new(
            Tree::Terminal(TerminalType::Input("A".to_string()))));
        let t2 = Rc::new(RefCell::new(Tree::Terminal(TerminalType::Constant(1.1))));
        let t3 = Rc::new(RefCell::new(Tree::Terminal(TerminalType::Constant(1.2))));
        let tree = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("If"),
            children:vec![t1.clone(), t2.clone(), t3.clone(), ],
        }));

        let mut inputs = Inputs::new();
        inputs.insert("A", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.1));
        inputs.insert("A", -1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.2));
    }
    #[test]
    fn gt(){
        let t1 = Rc::new(RefCell::new(Tree::Terminal(
            TerminalType::Input("A".to_string()))));
        let t2 = Rc::new(RefCell::new(Tree::Terminal(
            TerminalType::Input("B".to_string()))));
        let tree = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Gt"),
            children:vec![t1.clone(), t2.clone(),],
        }));
        let mut inputs = Inputs::new();
        inputs.insert("A", -1.0);
        inputs.insert("B", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(-1.0));
        inputs.insert("A", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(0.0));
        inputs.insert("A", 2.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.0));
        
    }
    #[test]
    fn lt(){
        let t1 = Rc::new(RefCell::new(Tree::Terminal(TerminalType::Input("A".to_string()))));
        let t2 = Rc::new(RefCell::new(Tree::Terminal(TerminalType::Input("B".to_string()))));
        let tree = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Lt"),
            children:vec![t1.clone(), t2.clone(),],
        }));
        let mut inputs = Inputs::new();
        inputs.insert("A", -1.0);
        inputs.insert("B", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.0));
        inputs.insert("A", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(0.0));
        inputs.insert("A", 2.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(-1.0));
        
    }
    #[test]
    fn negate(){
        let t1 = Rc::new(RefCell::new(Tree::Terminal(TerminalType::Input("A".to_string()))));
        let tree = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Neg"),
            children:vec![t1.clone(),],
        }));
        let mut inputs = Inputs::new();
        inputs.insert("A", -1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.0));
        inputs.insert("A", 0.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(0.0));
        inputs.insert("A", 2.334);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(-2.334));      
    }
    #[test]
    fn remainder () {
        let t1 =
            Rc::new(RefCell::new(
                Tree::Terminal(TerminalType::Input("A".to_string()))));
        let t2 =
            Rc::new(RefCell::new(
                Tree::Terminal(TerminalType::Input("B".to_string()))));
        let tree = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Mod"),
            children:vec![t1.clone(), t2.clone(),],
        }));
        let mut inputs = Inputs::new();
        inputs.insert("A", -1.0);
        inputs.insert("B", 1.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(0.0));
        inputs.insert("A", 10.0);
        inputs.insert("B", 3.0);
        assert_eq!(tree.borrow_mut().evaluate(&inputs), Some(1.0));
        
    }
}    
