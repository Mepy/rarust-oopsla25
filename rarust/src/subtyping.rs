/* resource awared subtyping */

use crate::{lp::{Lp, RType, Resource}, rich_type::RichType, typ_ctx::Gamma};

use RichType::*;
impl Lp
{
    pub fn wf(&mut self, rtype:&RichType<Resource>) // TODO : how to use it better?
    {
        use RichType::*;
        match rtype
        {
        | Undefined => (),
        | Primitive => (),
        | Tuple(rfields, _r) => {
            rfields.iter().for_each(|rtype|{ self.wf(rtype) });
        },
        | Variant(rvariants) => {
            rvariants.iter().for_each(|(rfields, _r)|{
                rfields.iter().for_each(|rtype|{ self.wf(rtype) });
            })
        },
        | SS(_tindex) => (),
        | MR(_tindex, rt) => self.wf(rt),
        | BoxOf(rt) => self.wf(rt),
        | Shared(rt) => self.wf(rt),
        | Mutable(rtc, rtp) => {
            self.wf(rtc);
            self.wf(rtp);
            self.prec(rtp, rtc);
        }
        }
    }
}
impl Lp
{
    #[allow(dead_code)]
    pub fn eq(&mut self, rt1:&RType, rt2:&RType)
    {
        match (rt1, rt2)
        {
        | (Undefined, _) => (),
        | (Primitive, Primitive) => (),
        | (Tuple(rfields1, r1), Tuple(rfields2, r2)) => {
            for (rt1, rt2) in std::iter::zip(rfields1, rfields2)
            {
                self.eq(rt1, rt2);
            }
            self.add(constraint!(r1.clone() == r2.clone()));
        },
        | (Variant(rvariants1), Variant(rvariants2)) => {
            for ((rfields1, r1), (rfields2, r2)) in std::iter::zip(rvariants1, rvariants2)
            {
                for (rt1, rt2) in std::iter::zip(rfields1, rfields2)
                {
                    self.eq(rt1, rt2);
                }
                self.add(constraint!(r1.clone() == r2.clone()));
            }
        },
        | (SS(id1), SS(id2)) if id1 == id2 => (),
        | (MR(id1, rt1), MR(id2, rt2)) if id1 == id2 
            => self.eq(&rt1, &rt2),
        | (BoxOf(rt1), BoxOf(rt2)) 
        | (Shared(rt1), Shared(rt2))
            => self.eq(&rt1, &rt2),
        | (Mutable(rtc1, rtp1), Mutable(rtc2, rtp2)) 
            => { self.eq(&rtc1, &rtc2); self.eq(&rtp2, &rtp1); }
        | (_, Undefined) => (), 
            // this is because we might not initialize some types in context, 
            // leaving them as undefined, but no problem now
            // todo: initialize them, but generate no extra constraints
        | (rt1, rt2) => unreachable!("undefined prec of {:?} <: {:?}", rt1, rt2),
        }
    }
    pub fn prec(&mut self, rt1:&RType, rt2:&RType)
    {
        match (rt1, rt2)
        {
        | (Undefined, _) => (),
        | (Primitive, Primitive) => (),
        | (Tuple(rfields1, r1), Tuple(rfields2, r2)) => {
            for (rt1, rt2) in std::iter::zip(rfields1, rfields2)
            {
                self.prec(rt1, rt2);
            }
            self.add(constraint!(r1.clone() <= r2.clone()));
        },
        | (Variant(rvariants1), Variant(rvariants2)) => {
            for ((rfields1, r1), (rfields2, r2)) in std::iter::zip(rvariants1, rvariants2)
            {
                for (rt1, rt2) in std::iter::zip(rfields1, rfields2)
                {
                    self.prec(rt1, rt2);
                }
                self.add(constraint!(r1.clone() <= r2.clone()));
            }
        },
        | (SS(id1), SS(id2)) if id1 == id2 => (),
        | (SS(id1), MR(id2, _)) if id1 == id2 => (),
        | (MR(id1, _), SS(id2)) if id1 == id2 => (),
        | (MR(id1, rt1), MR(id2, rt2)) if id1 == id2 
            => self.prec(&rt1, &rt2),
        | (BoxOf(rt1), BoxOf(rt2)) 
        | (Shared(rt1), Shared(rt2))
            => self.prec(&rt1, &rt2),
        | (Mutable(rtc1, rtp1), Mutable(rtc2, rtp2)) 
            => { self.prec(&rtc1, &rtc2); self.prec(&rtp2, &rtp1); }
        | (_, Undefined) => (), 
            // this is because we might not initialize some types in context, 
            // leaving them as undefined, but no problem now
            // todo: initialize them, but generate no extra constraints
        | (rt1, rt2) => unreachable!("undefined prec of {:?} <: {:?}", rt1, rt2),
        }
    
    }

    pub fn meet(&mut self, rt1:RType, rt2:RType) -> RType
    {
        if rt1 == rt2 { rt1 }
        else {
        match (rt1, rt2)
        {
        | (Undefined, rt) | (rt, Undefined) => {
            let rtype = self.fresh_rtype(&rt);
            self.prec(&rtype, &rt);
            rtype
        },
        | (Primitive, Primitive) => Primitive,
        | (Tuple(rfields1, r1), Tuple(rfields2, r2)) => {
            let rfields = std::iter::zip(rfields1, rfields2)
                .map(|(rt1, rt2)|{
                     self.meet(rt1, rt2) 
                }).collect();
            let r = self.min(r1, r2);
            Tuple(rfields, r)
        },
        | (Variant(rvariants1), Variant(rvariants2)) => { 
            let rvariants = std::iter::zip(rvariants1, rvariants2)
            .map(|((rfields1, r1), (rfields2, r2))|{
                let rfields = std::iter::zip(rfields1, rfields2)
                .map(|(rt1, rt2)|{
                     self.meet(rt1, rt2) 
                }).collect();
                let r = self.min(r1, r2);
                (rfields, r)
            })
            .collect();
            Variant(rvariants)
        },
        | (SS(id1), SS(id2)) if id1 == id2 => SS(id1),
        | (MR(id1, rt1), MR(id2, rt2)) if id1 == id2
            => MR(id1, Box::new(self.meet(*rt1, *rt2))),
        | (BoxOf(rt1), BoxOf(rt2)) 
            => BoxOf(Box::new(self.meet(*rt1, *rt2))),
        | (Shared(rt1), Shared(rt2))
            => Shared(Box::new(self.meet(*rt1, *rt2))),
        | (Mutable(rtc1, rtp1), Mutable(rtc2, rtp2)) 
            => {
            if rtp1 != rtp2 { // for more precise
                self.prec(&rtp1, &rtc1);
                self.prec(&rtp2, &rtc2);
            }
            Mutable(
                Box::new(self.meet(*rtc1, *rtc2)),
                Box::new(self.join(*rtp1, *rtp2)),
            )
        },
        | (rt1, rt2) => unreachable!("undefined meet of {:?} {:?}", rt1, rt2),
        }
        }
    }
    pub fn join(&mut self, rt1:RType, rt2:RType) -> RType
    {
        if rt1 == rt2 { rt1 }
        else {
        match (rt1, rt2)
        {
        | (Undefined, rt) | (rt, Undefined) => rt,
        | (Primitive, Primitive) => Primitive,
        | (Tuple(rfields1, r1), Tuple(rfields2, r2)) => {
            let rfields = std::iter::zip(rfields1, rfields2)
                .map(|(rt1, rt2)|{
                     self.join(rt1, rt2) 
                }).collect();
            let r = self.max(r1, r2);
            Tuple(rfields, r)
        },
        | (Variant(rvariants1), Variant(rvariants2)) => { 
            let rvariants = std::iter::zip(rvariants1, rvariants2)
            .map(|((rfields1, r1), (rfields2, r2))|{
                let rfields = std::iter::zip(rfields1, rfields2)
                .map(|(rt1, rt2)|{
                     self.join(rt1, rt2) 
                }).collect();
                let r = self.max(r1, r2);
                (rfields, r)
            })
            .collect();
            Variant(rvariants)
        },
        | (SS(id1), SS(id2)) if id1 == id2 => SS(id1),
        | (BoxOf(rt1), BoxOf(rt2)) 
            => BoxOf(Box::new(self.join(*rt1, *rt2))),
        | (Shared(rt1), Shared(rt2))
            => Shared(Box::new(self.join(*rt1, *rt2))),
        | (Mutable(rtc1, rtp1), Mutable(rtc2, rtp2)) 
            => {
            if rtp1 != rtp2 { // for more precise
                self.prec(&rtp1, &rtc1);
                self.prec(&rtp2, &rtc2);
            }
            Mutable(
                Box::new(self.meet(*rtc1, *rtc2)),
                Box::new(self.join(*rtp1, *rtp2)),
            )
        },
        | (rt1, rt2) => unreachable!("undefined join of {:?} {:?}", rt1, rt2),
        }
        }
    }
    pub fn wedge(&mut self, g1:Gamma, g2:Gamma) -> Gamma
    {
        let rtypes = std::iter::zip(g1.rtypes, g2.rtypes)
        .map(|(rt1, rt2)|{
            self.meet(rt1, rt2)
        }).collect::<im::Vector<RType>>();
        Gamma { rtypes }
    }
    /* // `vee` is never used
    pub fn vee(&mut self, g1:Gamma, g2:Gamma) -> Gamma
    {
        let rtypes = std::iter::zip(g1.rtypes, g2.rtypes)
        .map(|(rt1, rt2)|{
            self.join(rt1, rt2)
        }).collect::<im::Vector<RType>>();
        Gamma { rtypes }
    }
    */
}