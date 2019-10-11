use std::cell::{RefCell};
use std::rc::Rc;
use regex::Regex;
use crate::inputs::Inputs;
use crate::operator::Operator;
#[derive(Clone)]
pub enum Tree<T> {
    Terminal(TerminalType<T>),
    // https://doc.rust-lang.org/std/rc/index.html
    Internal { operator:Operator<T>,
               children:Vec<Rc<RefCell<Tree<T>>>>
    },
}

// The type of data that can be a terminal
#[derive(Debug, Clone)]
/// Leaf nodes
pub enum TerminalType<T> {
    Constant(T),

    // Input from the outside world comes as strings.  Always (at time
    // of writing) a T. The string names the input field that
    // contains the value
    Input(String),
}

impl Tree<f64> {
    /// Recursive evaluation of the tree FIXME `evaluate` must take
    /// inputs as a parameter.
    pub fn evaluate(&self, input:&Inputs) -> Option<f64> {
        match self {
            Tree::Terminal(t) => match t {
                TerminalType::Constant(c) => Some(*c),
                // FIXME Look `s` up in inputs.
                TerminalType::Input(s) =>
                    Some(*input.get(s).unwrap()),
            },
            Tree::Internal{operator, children} => {
                operator.evaluate(input, children)
            },
        }
    }

    /// A internal function to copy just the data out of a tree.  If
    /// it is a internal node the copy will not have children.
    fn _light_copy(&self) -> Rc<RefCell<Tree<f64>>> {
        match self {
            Tree::Terminal(t) => Rc::new(RefCell::new(Tree::Terminal(t.clone()))),
            Tree::Internal{operator, children:_} => {
                // A copy of the node ready to add children
                Rc::new(RefCell::new(Tree::Internal{
                    operator:*operator, children:Vec::new()
                }))
            },
        }
    }
        
    fn _add_child(&mut self, c:Rc<RefCell<Tree<f64>>>){
        //eprintln!("add_child: {} -> {}", c.borrow().to_string(), self.to_string());
        match self {
            Tree::Terminal(_) => panic!("Tree::_add_child(..) called on a terminal"),
            Tree::Internal{operator:_, children} => children.push(c),
        };
    }
            
    /// Make a deep copy of a tree.  Danger, cycles!
    pub fn clone(&self) -> Rc<RefCell<Tree<f64>>> {
        // eprintln!("clone: {}", self.to_string());
        // To avoid cycles each node that is copied is put here.
        // Complicates things as have to do a binary search on this
        // for each node. ** UNIMPLEMENTED **
        let _copied:Vec<Rc<RefCell<Tree<f64>>>> = Vec::new();
        // let copied:HashMap<Rc<RefCell<Tree<f64>>>, bool> =
        //     HashMap::new(); Fails to compile

        // Tree walking. Use these stacks.  `stackf` is nodes that are
        // being copied. `stack_t` is nodes that are being constructed
        let mut fs:Vec<Vec<Rc<RefCell<Tree<f64>>>>> = Vec::new();
        fs.push(match self {
            Tree::Terminal(_) => Vec::new(),
            Tree::Internal{operator:_, children} => {
                let c = children;
                let i = c.iter();
                let r = i.rev();
                let mut ret:Vec<Rc<RefCell<Tree<f64>>>> = Vec::new();
                for _r in r {
                    ret.push(_r.clone());
                }
                ret
            },
        });
        let mut ts:Vec<Rc<RefCell<Tree<f64>>>> = Vec::new();

        ts.push(self._light_copy());

        loop {
            // eprintln!("ts: {}", ts.first().unwrap().borrow().to_string());
            if fs.last().unwrap().is_empty() {
                // Processed all the children
                fs.pop();
                if fs.is_empty() {
                    // Finished
                    break
                };
                let _n = ts.pop().unwrap();
                // Finished adding to the node on the top of `ts`
                // eprintln!("Finished rhs node: {}", _n.borrow().to_string());
            }else{
                // Still children to process.  Pop off the next child
                let c = fs.last_mut().unwrap().pop().unwrap();
                //eprintln!("Processing child: {}", c.borrow().to_string());
                // The children to process
                let t:&Tree<f64> = &c.borrow();
                fs.push(match t {

                    // If it is a terminal node it has no children so
                    // put empty list on to stack
                    Tree::Terminal(_) => Vec::new(),

                    Tree::Internal{operator:_, children} =>
                        children.iter().rev().map(|x| x.clone()).collect()
                });

                // Add the child to the receiving tree
                // eprintln!("Add {} -> {}", c.borrow().to_string(),
                //           ts.last_mut().unwrap().borrow().to_string());
                let tt = c.borrow()._light_copy();
                ts.last_mut().unwrap().borrow_mut().
                    _add_child(tt.clone());
                ts.push(tt.clone());
            }
        }
        ts.pop().unwrap()
    }

    fn from_str(inp: &'static str) -> Rc<RefCell<Tree<f64>>> {
        // Prod( 0.5 Neg( 0.5 )Neg A )Prod

        // E.g. `Prod(` C like identifier naming a operator
        let re_op_start = Regex::new(r"^([[:alpha:]][[:alnum:]]+)\(").unwrap();

        // E.g. `)Prod` C like identifier naming a operator
        let re_op_end = Regex::new(r"^\)([[:alpha:]][[:alnum:]]+)").unwrap();

        // E.g. `FooBar21` A input
        let re_inp = Regex::new(r"^([[:alpha:]][[:alnum:]]*)$").unwrap();

        // A terminal constant. f64
        let re_num = Regex::new(r"^([\+\-]?[[:digit:]]+\.[[:digit:]]+)$").unwrap();
        
        let mut ret:Rc<RefCell<Tree<f64>>> =
            Rc::new(RefCell::new(Tree::Terminal(TerminalType::Constant(0.0))));
        let mut stack:Vec<Rc<RefCell<Tree<f64>>>> = Vec::new();
        let split = inp.split_whitespace();
        // E.g: "Sum( A Prod( A 0.5 12.0 )Prod 0.5 -1.5 )Sum"
        for w in split {
            // eprintln!("w {}",w);
            if let Some(n) = re_num.captures(w){
                // At a leaf, constant
                let z = n.get(1).unwrap().as_str().parse::<f64>().unwrap();
                //eprintln!("z: {} At a leaf, constant ", z);
                let n = Rc::new(RefCell::new(
                    Tree::Terminal(TerminalType::Constant(z))));
                match stack.last() {
                    Some(s) => {
                        eprintln!("Add '{}' -> '{}'",
                                  n.borrow().to_string(), s.borrow().to_string());
                        s.borrow_mut()._add_child(n.clone());
                    },
                    None => // Stack is empty.  The tree is just this constant
                        ret = n.clone(),
                }
            }else if let Some(n) = re_inp.captures(w) {
                // At a leaf, input
                let z = n.get(1).unwrap().as_str();
                //eprintln!("z: {} At a leaf, input ", z);
                let n = Rc::new(RefCell::new(
                    Tree::Terminal(TerminalType::Input(z.to_string()))
                ));
                match stack.last() {
                    Some(s) => {
                        eprintln!("Add '{}' -> '{}'",
                                  n.borrow().to_string(), s.borrow().to_string());
                        s.borrow_mut()._add_child(n.clone());
                    },
                    None => // Stack is empty.  The tree is just this input
                        ret = n.clone(),
                }
            }else if let Some(s) = re_op_start.captures(w) {
                // The start of a internal node
                let z = s.get(1).unwrap().as_str();
                let op = Operator::new(z);
                //eprintln!("z: {} op: {:?} The start of a internal node ", z, op);
                let ch:Vec<Rc<RefCell<Tree<f64>>>> = Vec::new();
                let n = Rc::new(RefCell::new(
                    Tree::Internal{
                        operator:op,
                        children:ch,
                    }
                ));
                if let Some(s) =  stack.last() {
                    eprintln!("Add '{}' -> '{}'",
                              n.borrow().to_string(), s.borrow().to_string());
                    s.borrow_mut()._add_child(n.clone());
                }
                stack.push(n.clone());
            }else if let Some(_) = re_op_end.captures(w) {
                // Close a operator
                //eprintln!("Close a operator");                
                if let Some(c) =  stack.pop() {
                    if stack.len() == 0 {
                        ret = c;
                    }
                }else{
                    panic!("Closed a node with {} and stack empty", w);
                }
            }
        }
        assert!(stack.len() == 0);
        ret
    }
    fn to_string(&self) -> String {

        match self {
            Tree::Terminal(t) => match t {
                TerminalType::Constant(c) => format!("{:.1}", c),
                // FIXME Look `s` up in inputs.
                TerminalType::Input(s) => String::from(s.as_str()),
            },
            Tree::Internal{operator, children} =>
                format!("{:?}({} ){:?}", operator,
                        children.iter().
                        fold("".to_string(), |acc,x| {
                            acc.to_string() +
                                " " +
                                x.borrow().to_string().as_str()
                        }), operator),
        }
        //"".to_string()
    }

    /// Internal function to replace a sub tree.  Sub trees are
    /// unmbered depth first left to right first child is 1.
    fn _replace(&mut self, t:Rc<RefCell<Tree<f64>>>,
                idx:usize) -> usize {

        if idx == 0 {
            // This can only happen if called with idx === 0.  Never a
            // recursive call.
            panic!("A tree cannot replace itself.")
        }

        // Replace the `idx`th child
        match self {
            Tree::Terminal(_) =>
            // No children to replace
                idx,
            Tree::Internal{operator:_, children} =>  {
                let mut idx = idx;                    
                for  c in children.iter_mut() {
                    idx = idx - 1;
                    if idx == 0 {
                        // Base case. Replace c
                        *c = t;
                        break;
                    }
                    idx = c.borrow_mut()._replace(t.clone(), idx);
                    if idx == 0 {
                            // Found and replaced sub-tree
                            break;
                    }
                }
                idx
            },
        }
    }

    fn _size(&self) -> usize {
        match self {
            Tree::Terminal(_) => 1,
            Tree::Internal{operator:_, children} =>
                1 + children.iter().fold(0, |acc, x| acc + x.borrow()._size()),
        }
    }
    
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::cell::{RefCell};
    use crate::inputs::Inputs;
    use crate::operator::Operator;
    use super ::Tree;
    use crate::tree::TerminalType;
    fn _sum() -> Rc::<RefCell<Tree<f64>>> {
        let c1 = Rc::new(RefCell::new(_const_tree(0.0)));
        let c2 = Rc::new(RefCell::new(_const_tree(2.0)));
        let c3 = Rc::new(RefCell::new(_const_tree(0.5)));
        let c4 = Rc::new(RefCell::new(_const_tree(-1.5)));
        Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Sum"),
            children:vec![c1.clone(), c2.clone(), c3.clone(), c4.clone()]
        }))
    }
    fn _product()  -> Rc::<RefCell<Tree<f64>>> {
        let c1 = Rc::new(RefCell::new(_const_tree(0.5)));        
        let c2 = Rc::new(RefCell::new(_const_tree(12.0)));        
        Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Prod"),
            children:vec![c1.clone(), c1.clone(), c2.clone()],
        }))
    }

    //use super::*;
    fn _const_tree(c:f64) -> Tree<f64> {
        Tree::Terminal(TerminalType::Constant(c))
    }
    fn _input() -> Inputs{
        let mut ret = Inputs::new();
        ret.insert("A", 0.0);
        ret
    }
    #[test]
    fn sum() {
        let sum = _sum();
        let v = sum.borrow_mut().evaluate(&_input());
        assert_eq!(v, Some(1.0));
    }
    #[test]
    fn invert() {
        let product = _product();
        let invert = Rc::new(RefCell::new(Tree::Internal {
            operator:Operator::new("Inv"),
            children:vec![product.clone()],
        }));
        let v = invert.borrow_mut().evaluate(&_input());
        assert_eq!(v, Some(1.0/3.0));
    }
    #[test]
    fn log() {
        let sum = _sum();
        let log = Rc::new(RefCell::new(Tree::Internal {
            operator:Operator::new("Log"),
            children:vec![sum.clone()],
        }));
        let v = log.borrow_mut().evaluate(&_input());
        assert_eq!(v, Some(0.0));
    }
    #[test]
    fn product() {
        let product = _product();
        let v = product.borrow_mut().evaluate(&_input());
        assert_eq!(v, Some(3.0));
    }
    #[test]
    fn size() {
        let sum = _sum();
        assert_eq!(sum.borrow()._size(), 5);
    }
    #[test]
    fn replace() {
        let p =  _product();
        let sum = _sum();

        /*

      __+_______
     /  |  \    \
   0.0 2.0 0.5 -1.5
 
         */
        assert_eq!(sum.borrow().to_string(),
                   "Sum( 0.0 2.0 0.5 -1.5 )Sum");
        let n = sum.borrow_mut()._replace(p.clone(), 2);

        /*

      __+_______
     /  |  \    \
    0.0 x  0.5 -1.5
       /|\
      / | \
   0.5 0.5 12.0
 
         */

        assert_eq!(n, 0);
        assert_eq!(sum.borrow().to_string(),
                   "Sum( 0.0 Prod( 0.5 0.5 12.0 )Prod 0.5 -1.5 )Sum");
        let t = Rc::new(RefCell::new(
            Tree::Terminal(TerminalType::Input("A".to_string()))));
        sum.borrow_mut()._replace(t.clone(), 3);
        /*

      __+_______
     /  |  \    \
    0.0 x  0.5 -1.5
       /|\
      / | \
     A 0.5 12.0
 
         */
        assert_eq!(sum.borrow().to_string(),
                   "Sum( 0.0 Prod( A 0.5 12.0 )Prod 0.5 -1.5 )Sum");
        sum.borrow_mut()._replace(t.clone(), 1);
        /*

      __+_______
     /  |  \    \
    A   x  0.5 -1.5
       /|\
      / | \
     A 0.5 12.0
 
         */
        assert_eq!(sum.borrow_mut().to_string(),
                   "Sum( A Prod( A 0.5 12.0 )Prod 0.5 -1.5 )Sum");

        // Danger!  A infinite loop.  Cannot evaluate!
        sum.borrow_mut()._replace(sum.clone(), 1);

    }
    #[test]
    fn from_str(){
        let t = Tree::from_str("Sum( A Prod( A 0.5 12.0 )Prod 0.5 -1.5 )Sum");
        let mut input = Inputs::new();
        input.insert("A", 3.0);
        let f = t.borrow().evaluate(&input).unwrap();
        assert_eq!(f, 20.0);
        let t = Tree::from_str(
            "Lt( Prod( A 0.5 0.5 12.0 )Prod Sum( 10.0 2.0 0.5 -1.5 )Sum )Lt");
        let f = t.borrow().evaluate(&input).unwrap();
        assert_eq!(f, 1.0);
        input.insert("A", 30.0);
        let f = t.borrow().evaluate(&input).unwrap();
        assert_eq!(f, -1.0);
        
    }
    #[test]
    fn to_string() {
        let  p = _product();
        assert_eq!(p.borrow().to_string(),
                   "Prod( 0.5 0.5 12.0 )Prod".to_string());
        let s = _sum();
        let t =  Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Lt"),
            children:vec![p.clone(), s.clone()],
        }));
        assert_eq!(t.borrow().to_string(),
                   format!("{}{}", "Lt( Prod( 0.5 0.5 12.0 )Prod ",
                           "Sum( 0.0 2.0 0.5 -1.5 )Sum )Lt"));
        
                                                    
    }
    /// Test building trees that take paramatised inputs
    #[test]
    fn inputs() {
        let mut inputs = Inputs::new();
        let  t = _product();
        assert_eq!(t.borrow_mut().evaluate(&inputs), Some(3.0));
        assert_eq!(t.borrow().to_string(), "Prod( 0.5 0.5 12.0 )Prod");
        let s = Rc::new(RefCell::new(
            Tree::Terminal(TerminalType::Input("A".to_string()))));
        t.borrow_mut()._replace(s.clone(), 2);
        inputs.insert("A", 2.0);
        assert_eq!(t.borrow_mut().evaluate(&inputs), Some(12.0));
        assert_eq!(t.borrow().to_string(), "Prod( 0.5 A 12.0 )Prod");
        inputs.insert("A", 4.0);
        assert_eq!(t.borrow_mut().evaluate(&inputs), Some(24.0));
    }
    #[test]
    fn copy() {
        // let b = Rc::new(RefCell::new(_const_tree(0.5)));        
        let a = Rc::new(RefCell::new(_const_tree(0.5)));        
        let negate = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Neg"),
            children:vec![a.clone(),],
        }));
        let prod = Rc::new(RefCell::new(Tree::Internal{
            operator:Operator::new("Prod"),
            children:vec![a.clone(), negate.clone()],
        }));

        
        let ps = prod.borrow().to_string();
        let p2 = prod.borrow().clone();
        let p2s = p2.borrow().to_string();
        assert_eq!(ps, p2s);
        let mut inputs = Inputs::new();
        // inputs.insert("A", -1.0);
        // inputs.insert("B", 1.0);

        let pe = prod.borrow().evaluate(&inputs);
        let p2e = p2.borrow().evaluate(&inputs);
        assert_eq!(Some(pe), Some(p2e));
        let t1 =
            Rc::new(RefCell::new(
                Tree::Terminal(TerminalType::Input("A".to_string()))));
        prod.borrow_mut()._add_child(t1.clone());
        inputs.insert("A", -1.0);
        let pe = prod.borrow().evaluate(&inputs);
        let p2e = p2.borrow().evaluate(&inputs);
        assert_ne!(Some(pe), Some(p2e));
    }
}
