//use regex::Regex;
mod inputs;
mod operator;
mod tree;
// use crate::operator::Operator;
// use crate::inputs::Inputs;
use crate::tree::Tree;
use crate::tree::TerminalType;


fn _const_tree(c:f64) -> Tree<f64> {
    Tree::Terminal(TerminalType::Constant(c))
}

#[cfg(test)]
mod tests{
}
