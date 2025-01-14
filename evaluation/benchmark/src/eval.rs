use rrlib::tick;

use crate::types::{List, Tree, Tuple, Record, NListNode, NList};
use List::{Nil, Cons};
use Tree::{Leaf, Node};
use NList::{None, Some};

fn sum_rec(l:&List) -> i32
{
    match l
    {
    | Nil => { 
        tick(1); /* 1 = match Nil */
        0 
    },
    | Cons(hd, tl) => { 
        tick(3); /* 3 = match Cons + hd + tl */
        tick(3); *hd + sum_rec(&*tl) /* 3 = *hd + &tl + i32Add */
    }
    }
}
fn sum_loop(l:&List) -> i32
{
    let mut p : &List = l;
    let mut s = 0;
    while true
    {
    match p {
    | Nil => { 
        tick(1); /* 1 = match Nil */
        break; 
    },
    | Cons(hd, tl) => {
        tick(3); /* 3 = match Cons + hd + tl */
        tick(3); /* 3 = *hd + &tl + i32Add */
        p = &**tl;
        s = s + *hd; 
        // must derefence hd here
        // otherwise it will emit add trait for (i32, &i32)
        continue;
    }
    }
    }
    s
}
fn sum2(l:&List) -> i32
{
    sum_rec(l) + sum_loop(l)
}
fn rev_rec(l:&mut List, r: List) -> List
{
    match l 
    {
    | Nil => { 
        tick(1); /* 1 = match Nil */ 
        r
    },
    | Cons(hd, tl) => {
        tick(3); /* 3 = match Cons + hd + tl */
        tick(5); let r = Cons(*hd, Box::new(r)); /* 5 = *r + Box::new + *hd + Cons + *r */
        tick(1); rev_rec(&mut *tl, r) /* 1 = &mut tl */
    }
    }
}
fn rev_loop(l:&mut List)
{
    let mut l = l;
    let mut r = Nil;
     
    while true
    {
    match l 
    {
    | Nil => { 
        tick(1); /* 1 = match Nil */ 
        break; 
    }
    | Cons(hd, tl) => { 
        tick(3); /* 3 = match Cons + hd + tl */
        tick(5); r = Cons(*hd, Box::new(r)); /* 5 = r + Box::new + *hd + Cons + r */
        tick(1); l = &mut *tl; /* 1 = &mut tl */
    }
    }
    }
}

fn rev(l:&mut List)
{
    tick(3);
    *l = rev_rec(l, Nil);
}

fn rev2(l:&mut List)
{
    rev(&mut *l); rev(&mut *l);
}

fn end_m(l:&mut List) -> &mut List
{
    match l
    {
    | Nil => { 
        tick(1); /* 1 = match Nil */
        l 
    },
    | Cons(_, tl) => {
        tick(2); /* 2 = match Cons + tl */
        tick(1); end_m(&mut *tl) /* 1 = &mut tl */
    }
    }
}
fn end_c<'a>(l:&'a mut List, out:&mut &'a mut List)
{
    match l {
    | Nil => { 
        tick(1); /* 1 = match Nil */
        tick(1); *out=l; /* 1 = *out */
    },
    | Cons(_, tl) => {
        tick(2); /* 2 = match Cons + tl */
        tick(1); end_c(&mut *tl, out) /* 1 = &mut tl */
    },
    }
}
fn append(l:&mut List, x:i32)
{
    let end = end_m(l);
    tick(4); *end = Cons(x, Box::new(Nil)); /* 4 = Nil + Box::new + Cons + *end */
}
fn concat(l1:&mut List, l2:List)
{
    let mut x = Nil;
    let out = &mut &mut x;
    end_c(l1, out);
    tick(2); **out = l2; /* 2 = ** */
    tick(2); // keep consistent to the paper
}

fn dup(l:List) -> List
{
    match l 
    {
    | Nil => {
        tick(1); /* 1 = match Nil */
        Nil
    },
    | Cons(hd, tl) => {
        tick(3); /* 3 = match Cons + hd + tl */
        tick(1); /* 1 = &mut *tl */
        tick(7); Cons(hd, Box::new(Cons(hd, Box::new(dup(*tl))))) /* 7 = *hd + **tl + Box::new + Cons + **tl */
        
    }
    }
}

fn dup2(l:List) -> List
{
    dup(dup(l))
}

fn min(t:&Tree, d:i32) -> i32
{
    match t
    {
    | Leaf => {
        tick(1); /* 1 = match Leaf */
        d
    },
    | Node(n, l, _) => {
        tick(3); /* 3 = match Node + n + l */
        tick(2); min(&*l, *n) /* 2 = &l + *n */
    }
    }
}
fn max(t:&Tree, d:i32) -> i32
{
    match t
    {
    | Leaf => {
        tick(1); /* 1 = match Leaf */
        d
    },
    | Node(n, _, r) => {
        tick(3); /* 3 = match Node + n + r */
        tick(2); max(&*r, *n) /* 2 = &l + *n */
    }
    }
}

fn find(t:&Tree, x:i32) -> bool
{
    match t
    {
    | Leaf => {
        tick(1); /* 1 = match Leaf */
        false
    },
    | Node(n, l, r) => {
        tick(4); /* 4 = match Node + n + l + r */
        tick(1); let n = *n; /* 1 = *n */
        tick(1); if x < n /* 1 = i32Lt */
        { 
            tick(1); find(&*l, x) /* 1 = &l */
        }
        else 
        {
        tick(1); if x == n /* 1 = i32Eq */
        { 
            true 
        }
        else 
        { 
            tick(1); find(&*r, x) /* 1 = *r */
        }
        }
    }
    }
}

fn add(t:&mut Tree, x:i32)
{
    match t
    {
    | Leaf => { 
        tick(1); /* 1 = match Leaf */
    },
    | Node(n, l, r) => {
        tick(4); /* 4 = match Node + n + l + r */
        tick(1); add(&mut *l, x); /* 1 = &mut l */
        tick(1); add(&mut *r, x); /* 1 = &mut r */
        tick(3); *n = *n + x; /* 3 = *n + i32Add + *n */
    }
    }
}

fn tuple(x:&mut Tuple){
    rev2(&mut (*x).0);
    min(&mut (*x).1, 0);
}

fn record(x:&mut Record){
    rev2(&mut (*x).l);
    min(&mut (*x).t, 0);
}

fn reborrow_m(l:&mut List)
{
    let ll = &mut*l;
    rev2(ll);
    rev2(l);
}

fn reborrow_s(l:&List)
{
    let ll = &*l;
    sum2(ll);
    sum2(l);
}

fn nested_s_s(l:&&List)
{
    sum2(*l);
}
fn nested_m_s(l:&mut &List)
{
    sum2(*l);
}
fn nested_m_m(l:&mut &mut List)
{
    rev2(*l);
}

fn sum_rec_nlist(l:&NList) -> i32
{
    match l
    {
    | None =>{ 
        tick(1); /* 1 = match Nil */
        0 
    },
    | Some(node) => { 
        tick(2); /* 2 = match Some + node */
        // tick(1); let node = *node; 
        /* 3 = node.value + &node.next + i32Add */
        tick(3); node.value + sum_rec_nlist(&node.next) 
    }
    }
}

fn rev_rec_nlist(l:&mut NList, r:NList) -> NList
{
    match l 
    {
    | None => { 
        tick(1); /* 1 = match None */ 
        r
    },
    | Some(node) => {
        tick(2); /* 2 = match Some + node */
        // tick(1); let mut node = *node; 
        tick(4); /* 4 = *r + Box::new + node.value, *r */
        let r = Some(Box::new(NListNode{
            value : node.value, 
            next : r
        }));
        tick(1);
        rev_rec_nlist(&mut node.next, r)
    }
    }
}