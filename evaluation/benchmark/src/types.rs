pub enum List
{
    Nil,
    Cons(i32, Box<List>)
}
pub enum Tree
{
    Leaf,
    Node(i32, Box<Tree>, Box<Tree>)
}

pub type Tuple = (List, Tree);
pub struct Record{pub l:List, pub t:Tree}

pub struct NListNode {
    pub value : i32,
    pub next : NList
}
pub enum NList
{
    None,
    Some(Box<NListNode>)
}
use NList::*;