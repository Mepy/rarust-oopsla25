// checked by Flux(https://github.com/flux-rs/flux/commit/1f98b23619a7fe1dd8791dbc14a03412aed6682d)
// in the online demo(http://goto.ucsd.edu:8091/)
#![allow(unused)]

type Res = u32;
#[flux_rs::sig(fn(r:&strg Res[@res], {Res[@q] | q<=res}) ensures r:Res[res-q] )]
fn tick(r:&mut Res, q:Res){
    *r = *r - q;
}

type Anno = u32;
#[flux_rs::refined_by(alpha:int)]
#[flux_rs::invariant(alpha>=0)]
pub enum List
{
    #[flux_rs::variant((Anno[@alpha]) -> List[alpha])]
    Nil(Anno), 
    #[flux_rs::variant((Res[@alpha], i32, Box<List[alpha]>) -> List[alpha])]
    Cons(Res, i32, Box<List>)
}

impl List 
{
    #[flux_rs::sig(fn(l:&List[@alpha]) -> Anno[alpha])] 
    fn anno(self:&List) -> Anno
    {
        match self { 
        | List::Nil(anno) => *anno, 
        | List::Cons(anno, _, _) => *anno 
        }
    }

    #[flux_rs::sig(fn(alpha:Anno) -> List[alpha])]
    fn nil(alpha:Anno) -> List { List::Nil(alpha) }

    #[flux_rs::sig(fn(r:&strg { Res[@res] | res >= alpha }, hd:i32, tl:List[@alpha]) -> List[alpha] ensures r:Res[res-alpha])] 
    fn cons(r:&mut Res, hd:i32, tl:List) -> List 
    {
        let alpha = tl.anno();
        tick(r, alpha);
        List::Cons(alpha, hd, Box::new(tl))
    }
}

#[flux_rs::refined_by(alpha:int)]
#[flux_rs::invariant(alpha>=0)]
pub enum Tree
{
    #[flux_rs::variant((Anno[@alpha]) -> Tree[alpha])]
    Leaf(Anno),
    
    #[flux_rs::variant((Res[@alpha], i32, Box<Tree[alpha]>, Box<Tree[alpha]>) -> Tree[alpha])]
    Node(Res, i32, Box<Tree>, Box<Tree>)
}


impl Tree 
{
    #[flux_rs::sig(fn(l:&Tree[@alpha]) -> Anno[alpha])] 
    fn anno(self:&Tree) -> Anno
    {
        match self { 
        | Tree::Leaf(anno) => *anno, 
        | Tree::Node(anno, _, _, _) => *anno 
        }
    }

    #[flux_rs::sig(fn(alpha:Anno) -> Tree[alpha])]
    fn leaf(alpha:Anno) -> Tree { Tree::Leaf(alpha) }

    #[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= alpha }, n:i32, l:Tree[@alpha], r:Tree[alpha]) -> Tree[alpha] ensures delta:Res[res-alpha])] 
    fn node(delta:&mut Res, n:i32, l:Tree, r:Tree) -> Tree
    {
        let alpha = l.anno();
        assert!(l.anno() == r.anno());
        tick(delta, alpha);
        Tree::Node(alpha, n, Box::new(l), Box::new(r))
    }


    #[flux_rs::sig(fn(self:&strg Tree[@alpha], { Anno[@beta] | alpha >= beta }) ensures self:Tree[beta])]
    fn lower(self:&mut Tree, beta:Anno)
    {
        match self { 
        | Tree::Leaf(anno) => { *anno = beta; } 
        | Tree::Node(anno, _, l, r) => { 
            *anno = beta; 
            l.lower(beta);
            r.lower(beta);
        }
        }
    }
}


type Tuple = (List, Tree);

#[flux_rs::refined_by(alpha:int, beta:int)]
#[flux_rs::invariant(alpha>=0 && beta>=0)]
pub struct Record
{  
    #[flux_rs::field(List[alpha])]
    pub l:List,
    #[flux_rs::field(Tree[beta])]
    pub t:Tree
}

#[flux_rs::refined_by(alpha:int)]
#[flux_rs::invariant(alpha>=0)]
pub struct NListNode {
    #[flux_rs::field(Res[alpha])]
    pub pot : Res,
    pub value : i32,
    #[flux_rs::field(NList[alpha])]
    pub next : NList
}
#[flux_rs::refined_by(alpha:int)]
#[flux_rs::invariant(alpha>=0)]
pub enum NList
{
    #[flux_rs::variant((Anno[@alpha]) -> NList[alpha])]
    None(Anno), 
    #[flux_rs::variant((Box<NListNode[@alpha]>) -> NList[alpha])]
    Some(Box<NListNode>)
}
impl NListNode
{
    #[flux_rs::sig(fn(l:&NListNode[@alpha]) -> Anno[alpha])] 
    fn anno(self:&NListNode) -> Anno
    {
        self.pot
    }

    #[flux_rs::sig(fn(r:&strg { Res[@res] | res >= alpha }, hd:i32, tl:NList[@alpha]) -> NListNode[alpha] ensures r:Res[res-alpha])] 
    fn new(r:&mut Res, hd:i32, tl:NList) -> NListNode 
    {
        let alpha = tl.anno();
        tick(r, alpha);
        NListNode { pot:alpha, value:hd, next:tl }
    }
}
impl NList 
{
    #[flux_rs::sig(fn(l:&NList[@alpha]) -> Anno[alpha])] 
    fn anno(self:&NList) -> Anno
    {
        match self { 
        | NList::None(anno) => *anno, 
        | NList::Some(node) => node.anno(), 
        }
    }

    #[flux_rs::sig(fn(alpha:Anno) -> NList[alpha])]
    fn none(alpha:Anno) -> NList { NList::None(alpha) }

    #[flux_rs::sig(fn(l:NListNode[@alpha]) -> NList[alpha])] 
    fn some(l:NListNode) -> NList
    {
        NList::Some(Box::new(l))
    }

    #[flux_rs::sig(fn(alpha:Anno) -> NList[alpha])]
    fn nil(alpha:Anno) -> NList { NList::none(alpha) }
    #[flux_rs::sig(fn(r:&strg { Res[@res] | res >= alpha }, hd:i32, tl:NList[@alpha]) -> NList[alpha] ensures r:Res[res-alpha])] 
    fn cons(r:&mut Res, hd:i32, tl:NList) -> NList 
    {
        NList::some(NListNode::new(r, hd, tl))
    }
}


#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 1 } , List[10]) ensures r:Res[res-1])]
fn iter(r:&mut Res, l:List)
{
    match l 
    {
        List::Nil(_anno) => { tick(r, 1); },
        List::Cons(pot, hd, tl) => {
            *r = *r + pot;
            tick(r, 10);
            iter(r, *tl);
        },
    }
}

fn test_new_and_iter()
{
    let mut res = 32;
    let l = List::nil(10);
    let l = List::cons(&mut res, 1, l);
    let l = List::cons(&mut res, 2, l);
    iter(&mut res, l);
}

#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 1 }, l:&strg { List[@alpha] | alpha >= 6 }) -> i32 ensures r:Res[res-1], l:List[alpha-6])]
fn sum_rec(r:&mut Res, l:&mut List) -> i32
{
    match l
    {
    | List::Nil(anno) => { 
        *anno = *anno - 6;
        tick(r, 1); /* 1 = match Nil */
        0 
    },
    | List::Cons(pot, hd, tl) => { 
        *pot = *pot - 6;
        *r = *r + 6;
        tick(r, 3); /* 3 = match Cons + hd + tl */
        tick(r, 3); *hd + sum_rec(r, &mut *tl) /* 3 = *hd + &tl + i32Add */
    }
    }
}

/*
#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 1 }, l:&strg { List[@alpha] | alpha >= 6 }) -> i32 ensures r:Res[res-1], l:List[alpha-6])]
fn sum_loop(r:&mut Res, l:&mut List) -> i32
{
    let mut p : &mut List = l;
    let mut s = 0;
    while true
    {
    match p {
    | List::Nil(anno) => { 
        *anno = *anno - 6;
        tick(r, 1); /* 1 = match Nil */
        break; 
    },
    | List::Cons(pot, hd, tl) => {
        *pot = *pot - 6;
        *r = *r + 6;
        tick(r, 3); /* 3 = match Cons + hd + tl */
        tick(r, 3); /* 3 = *hd + &tl + i32Add */
        p = &mut *tl;
        s = s + *hd; 
        // must derefence hd here
        // otherwise it will emit add trait for (i32, &i32)
        continue;
    }
    }
    }
    s
}
*/

#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 2 }, l:&strg { List[@alpha] | alpha >= 12 }) -> i32 ensures r:Res[res-2], l:List[alpha-12])]
fn sum2(r:&mut Res, l:&mut List) -> i32
{
    sum_rec(r, l) + sum_rec(r, l)
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, l:&strg { List[@alpha] | alpha >= 9 + beta }, List[@beta]) -> List[beta] ensures delta:Res[res-1], l:List[alpha-9-beta])]
fn rev_rec(delta:&mut Res, l:&mut List, r: List) -> List
{
    let beta = r.anno();
    match l 
    {
    | List::Nil(anno) => { 
        *anno = *anno - 9 - beta;
        tick(delta, 1); /* 1 = match Nil */ 
        r
    },
    | List::Cons(pot, hd, tl) => {
        *pot = *pot - 9 - beta;
        *delta = *delta + 9 + beta;
        tick(delta, 3); /* 3 = match Cons + hd + tl */
        tick(delta, 5); let r = List::cons(delta, *hd, r); /* 5 = *r + Box::new + *hd + Cons + *r */
        tick(delta, 1); rev_rec(delta, &mut *tl, r) /* 1 = &mut tl */
    }
    }
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 4 }, l:&strg { List[@alpha] | alpha >= 9 }) ensures delta:Res[res-4], l:List[alpha-9])]
fn rev(delta:&mut Res, l:&mut List)
{
    let alpha = l.anno();
    tick(delta, 3);
    *l = rev_rec(delta, l, List::nil(alpha-9));
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 8 }, l:&strg { List[@alpha] | alpha >= 18 }) ensures delta:Res[res-8], l:List[alpha-18])]
fn rev2(delta:&mut Res, l:&mut List)
{
    rev(delta, &mut *l); rev(delta, &mut *l);
}

/*
#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, l:&strg { List[@alpha] | alpha >= 3 }) -> &mut List[alpha-3]  ensures delta:Res[res-1], l:List[alpha-3])]
fn end_m<'a>(delta:&mut Res, l:&'a mut List) -> &'a mut List
{
    match l
    {
    | List::Nil(anno) => { 
        *anno = *anno - 3;
        tick(delta, 1); /* 1 = match Nil */
        l 
    },
    | List::Cons(pot, _, tl) => {
        *pot = *pot - 3;
        *delta = *delta + 3;
        tick(delta, 2); /* 2 = match Cons + tl */
        tick(delta, 1); end_m(delta, &mut *tl) /* 1 = &mut tl */
    }
    }
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 2 }, l:&strg { List[@alpha] | alpha >= 3 }, out:&strg (&mut List[@beta]))
    ensures delta:Res[res-2], l:List[alpha-3], out: List[alpha-3])]
fn end_c<'a>(delta:&mut Res, l:&'a mut List, out:&mut &'a mut List)
{
    match l {
    | List::Nil(anno) => { 
        *anno = *anno - 3;
        tick(delta, 1); /* 1 = match Nil */
        tick(delta, 1); *out=l; /* 1 = *out */
    },
    | List::Cons(pot, _, tl) => {
        *pot = *pot - 3;
        *delta = *delta + 3;
        tick(delta, 2); /* 2 = match Cons + tl */
        tick(delta, 1); end_c(delta, &mut *tl, out) /* 1 = &mut tl */
    },
    }
}

*/


#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= alpha + 2 }, l:&strg { List[@alpha] | alpha >= 3 }, x:i32) ensures r:Res[res-alpha-2], l:List[alpha-3])]
fn append(r:&mut Res, l:&mut List, x:i32)
{
    /*
    let end = end_m(l); /* 1 + 3n */
    tick(4); *end = Cons(x, Box::new(Nil)); /* 4 = Nil + Box::new + Cons + *end */
    */
    match l 
    {
    | List::Nil(anno) => {
        tick(r, 5); // 5 = 1 + 4 
        *l = List::cons(r, x, List::nil(*anno-3));
    }
    | List::Cons(pot, hd, tl) => {
        *pot = *pot - 3;
        *r = *r + 3;
        tick(r, 3);
        append(r, &mut *tl, x);
    }
    }
}


#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 5 }, l1:&strg { List[@alpha] | alpha >= 3 }, l2:List[alpha-3]) ensures r:Res[res-5], l1:List[alpha-3])]
fn concat(r:&mut Res, l1:&mut List, l2:List)
{
    match l1 
    {
    | List::Nil(anno) => {
        tick(r, 5);
        *l1 = l2;
    }
    | List::Cons(pot, hd, tl) => {
        *pot = *pot - 3;
        *r = *r + 3;
        tick(r, 3);
        concat(r, &mut *tl, l2);
    }
    }
}

#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 1 }, { List[@alpha] | alpha >= 11 }) -> List[(alpha-11)/2] ensures r:Res[res-1])]
fn dup(r:&mut Res, l:List) -> List
{
    match l 
    {
    | List::Nil(anno) => {
        tick(r, 1); /* 1 = match Nil */
        List::nil((anno-11)/2)
    },
    | List::Cons(pot, hd, tl) => {
        if ((pot-11)%2==1) { *r = *r + pot - 1; }
        else { *r = *r + pot; }
        tick(r, 3); /* 3 = match Cons + hd + tl */
        tick(r, 1); /* 1 = &mut *tl */
        tick(r, 7); /* 7 = *hd + **tl + Box::new + Cons + **tl */
        let tl = dup(r, *tl);
        let tl = List::cons(r, hd, tl);
        List::cons(r, hd, tl) 
    }
    }
}

#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 2 }, { List[@alpha] | alpha >= 33 }) -> List[(alpha-33)/4] ensures r:Res[res-2])]
fn dup2(r:&mut Res, l:List) -> List
{
    let l = dup(r, l);
    let l = dup(r, l);
    l
}


#[flux_rs::sig(fn(r:&strg { Res[@res] | res >= 1 }, t:&strg { Tree[@alpha] | alpha >= 5 }, d:i32) -> i32 ensures r:Res[res-1], t:Tree[alpha-5])]
fn min(delta:&mut Res, t:&mut Tree, d:i32) -> i32
{
    match t
    {
    | Tree::Leaf(anno) => {
        *anno = *anno - 5;
        tick(delta, 1); /* 1 = match Leaf */
        d
    },
    | Tree::Node(pot, n, l, r) => {
        *pot = *pot - 5;
        *delta = *delta + 5;
        tick(delta, 3); /* 3 = match Node + n + l */
        tick(delta, 2); /* 2 = &l + *n */
        r.lower(*pot);
        min(delta, &mut *l, *n)
    }
    }
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, t:&strg { Tree[@alpha] | alpha >= 5 }, d:i32) -> i32 ensures delta:Res[res-1], t:Tree[alpha-5])]
fn max(delta:&mut Res, t:&mut Tree, d:i32) -> i32
{
    match t
    {
    | Tree::Leaf(anno) => {
        *anno = *anno - 5;
        tick(delta, 1); /* 1 = match Leaf */
        d
    },
    | Tree::Node(pot, n, l, r) => {
        *pot = *pot - 5;
        *delta = *delta + 5;
        tick(delta, 3); /* 3 = match Node + n + l */
        tick(delta, 2); /* 2 = &l + *n */
        l.lower(*pot);
        max(delta, &mut *r, *n)
    }
    }
}


#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, t:&strg { Tree[@alpha] | alpha >= 8 }, x:i32) -> bool ensures delta:Res[res-1], t:Tree[alpha-8])]
fn find(delta:&mut Res, t:&mut Tree, x:i32) -> bool
{
    match t
    {
    | Tree::Leaf(anno) => {
        *anno = *anno - 8;
        tick(delta, 1);
        false
    },
    | Tree::Node(pot, n, l, r) => {
        *pot = *pot - 8;
        *delta = *delta + 8;
        tick(delta, 4); /* 4 = match Node + n + l + r */
        tick(delta, 1); let n = *n; /* 1 = *n */
        tick(delta, 1); if x < n /* 1 = i32Lt */
        { 
            Tree::lower(r, *pot);
            tick(delta, 2); find(delta, l, x) /* 1 = &l, 1 = aligning */
        }
        else 
        {
        tick(delta, 1); if x == n /* 1 = i32Eq */
        { 
            Tree::lower(l, *pot);
            Tree::lower(r, *pot);
            tick(delta, 2); true /* 2 = aligning */
        }
        else 
        { 
            Tree::lower(l, *pot);
            tick(delta, 1); find(delta, r, x) /* 1 = *r */
        }
        }
    }
    }
}



#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, t:&strg { Tree[@alpha] | alpha >= 10 }, d:i32) ensures delta:Res[res-1], t:Tree[alpha-10])]
fn add(delta:&mut Res, t:&mut Tree, x:i32)
{
    match t
    {
    | Tree::Leaf(anno) => {
        *anno = *anno - 10;
        tick(delta, 1); /* 1 = match Leaf */
    },
    | Tree::Node(pot, n, l, r) => {
        *pot = *pot - 10;
        *delta = *delta + 10;
        tick(delta, 4); /* 4 = match Node + n + l + r */
        tick(delta, 1); add(delta, &mut *l, x); /* 1 = &mut l */
        tick(delta, 1); add(delta, &mut *r, x); /* 1 = &mut r */
        tick(delta, 3); *n = *n + x; /* 3 = *n + i32Add + *n */
    }
    }
}

#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 9 }, x:&strg { (List[@alpha], Tree[@beta]) | alpha >= 18 && beta >= 5 }) ensures delta:Res[res-9], x:(List[alpha-18], Tree[beta-5]))]
fn tuple(r:&mut Res, x:&mut Tuple){
    rev2(r, &mut x.0);
    min(r, &mut x.1, 0);
}


#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 9 }, x:&strg { Record[@alpha, @beta] | alpha >= 18 && beta >= 5 }) ensures delta:Res[res-9], x:Record[alpha-18, beta-5])]
fn record(r:&mut Res, x:&mut Record){
    rev2(r, &mut x.l);
    min(r, &mut x.t, 0);
}


#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, l:&strg { NList[@alpha] | alpha >= 5 }) -> i32 ensures delta:Res[res-1], l:NList[alpha-5])]
fn sum_rec_nlist(delta:&mut Res, l:&mut NList) -> i32
{
    match l
    {
    | NList::None(anno) =>{
        *anno = *anno - 5; 
        tick(delta, 1); /* 1 = match Nil */
        0 
    },
    | NList::Some(node) => { 
        node.pot = node.pot - 5;
        *delta = *delta + 5;
        tick(delta, 2); /* 2 = match Some + node */
        // tick(1); let node = *node; 
        /* 3 = node.value + &node.next + i32Add */
        tick(delta, 3); node.value + sum_rec_nlist(delta, &mut node.next) 
    }
    }
}



#[flux_rs::sig(fn(delta:&strg { Res[@res] | res >= 1 }, l:&strg { NList[@alpha] | alpha >= 7 + beta }, NList[@beta]) -> NList[beta] ensures delta:Res[res-1], l:NList[alpha-7-beta])]
fn rev_rec_nlist(delta:&mut Res, l:&mut NList, r:NList) -> NList
{
    let beta = r.anno();
    match l 
    {
    | NList::None(anno) =>{
        *anno = *anno - 7 - beta;
        tick(delta, 1); /* 1 = match None */ 
        r
    },
    | NList::Some(node) => {
        node.pot = node.pot - 7 - beta;
        *delta = *delta + 7 + beta;
        tick(delta, 2); /* 2 = match Some + node */
        tick(delta, 4); /* 4 = *r + Box::new + node.value, *r */
        let r = NList::cons(delta, node.value, r);
        tick(delta, 1);
        rev_rec_nlist(delta, &mut node.next, r)
    }
    }
}