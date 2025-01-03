/*  rich with resource potential! 
    Only support ADT, Struct, Tuple, no function type!
*/


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RichType<P : Clone> {
    Undefined, /* undefined, uninitialized */
    Primitive, /* potential = 0 */
    Tuple(Vec<RichType<P>>, P), /* also for struct, unnamed */
    Variant(Vec<(Vec<RichType<P>>, P)>), /* each is for one constructor with P potential */
    
    SS(usize), // We use Box<Self> to represent sub-structure, SS(tindex) is the rtypes[tindex]
    MR(usize, Box<RichType<P>>), // Mutual Recursive types
    BoxOf(Box<RichType<P>>), // non-self, and no support for mutual recursive

    Shared(Box<RichType<P>>),
    Mutable(Box<RichType<P>>, Box<RichType<P>>), /* Mut(current, prophecy) */
}

/*

let list = RichType<P>::Variant(vec![(vec![], 0), (vec![Primitive], alpha)]) 

*/

pub fn extract<P: Clone>(rt:&RichType<P>, tindex:usize) -> Option<RichType<P>>
{
    use RichType::*;
    match rt
    {     
    | MR(id, rtype) => { 
        if *id == tindex {
            Some(*rtype.clone()) // extract
        }
        else {
            extract(& *rtype, tindex)
        }
    }
    | SS(_id) => None,
    | Undefined | Primitive => None,
    | Tuple(fields, _p) => {
        fields.iter().find_map(|rt|{ extract(rt, tindex) })
    }
    | Variant(variants) => {
        variants.iter().find_map(|(fields, _)|{
            fields.iter().find_map(|rt|{ extract(rt, tindex) })
        })
    }
    | BoxOf(rt) | Shared(rt) => {
        extract(rt, tindex)
    }
    | Mutable(rtc, rtp) => {
        extract(rtc, tindex).or(extract(rtp, tindex))
    }
    }
}

pub fn fold<P : Clone>(rt:&mut RichType<P>, tindex:usize)
{
    use RichType::*;
    match rt
    {
    | MR(id, rtype) => { 
        if *id == tindex {
            *rt = SS(tindex); // fold here
        }
        else {
            fold(&mut *rtype, tindex)
        }
    }
    | SS(_id) => (),
    | Undefined | Primitive => (),
    | Tuple(fields, _p) => {
        for rt in fields {
            fold(rt, tindex);
        }
    }
    | Variant(variants) => {
        for (fields, _) in variants {
        for rt in fields {
            fold(rt, tindex);
        }
        }
    }
    | BoxOf(rt) | Shared(rt) => {
        fold(rt, tindex);
    }
    | Mutable(rtc, rtp) => {
        fold(rtc, tindex);
        fold(rtp, tindex);
    }
    }
}


pub fn unfold<P : Clone>(rt:&mut RichType<P>, tindex:usize, subst:&RichType<P>)
{
    use RichType::*;
    match rt
    {
    | SS(id) => if *id == tindex {
        *rt = RichType::MR(tindex, Box::new(subst.clone()));
    }
    | Undefined | Primitive => (),
    | Tuple(fields, _p) => {
        for rt in fields {
            unfold(rt, tindex, subst);
        }
    }
    | Variant(variants) => {
        for (fields, _) in variants {
        for rt in fields {
            unfold(rt, tindex, subst);
        }
        }
    }

    | MR(id, rt) => if *id != tindex {
        unfold(rt, tindex, subst);
    }
    | BoxOf(rt) | Shared(rt) => {
        unfold(rt, tindex, subst);
    }
    | Mutable(rtc, rtp) => {
        unfold(rtc, tindex, subst);
        unfold(rtp, tindex, subst);
    }
    }
}
