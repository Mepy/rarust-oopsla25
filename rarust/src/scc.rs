// strong connective components and topological sorting on directed cyclic graph

use std::collections::HashSet;


#[derive(Debug, Clone)]
pub struct Node
{
    pub nexts : Vec<usize>,
}

#[derive(Debug)]
pub struct Graph
{
    pub nodes : Vec<Node>,
}

/* // `new` is never used
impl Graph
{
    pub fn new(nodes_size:usize) -> Graph
    {
        Graph{ nodes:vec![Node{ nexts:Vec::new() }; nodes_size] }
    }
}
*/

#[derive(Debug)]
pub struct SCC
{
    pub components : Vec<Vec<usize>>,
}
impl SCC
{
    fn strong_connect
    (&mut self, graph:&Graph, stack:&mut Vec<usize>, on_stack:&mut Vec<bool>,
     indexs: &mut Vec<i32>, lowlinks:&mut Vec<i32>, index:&mut i32, v:usize)
    {
        let i = *index;
        indexs[v] = i;
        lowlinks[v] = i;
        *index = i + 1;
        stack.push(v);
        on_stack[v] = true;
    
        for w in graph.nodes[v].nexts.iter()
        {
            let w = *w;
            if indexs[w] == -1
            {
                self.strong_connect(graph, stack, on_stack, indexs, lowlinks, index, w);
                lowlinks[v] = std::cmp::min(lowlinks[v], lowlinks[w]);
            }
            else if on_stack[w]
            {
                lowlinks[v] = std::cmp::min(lowlinks[v], indexs[w]);
            }
        }
    
        if lowlinks[v] == indexs[v] && indexs[v] != -1
        {
            let mut component = Vec::new();
            loop
            {
                let Some(w) = stack.pop() else { unreachable!("stack pop") };
                on_stack[w] = false;
                component.push(w);
                if w == v { break }
            }
            if component.len() >= 1 { self.components.push(component); }
        }
    }
    
    pub fn new(graph:&Graph) -> SCC
    {
        let nodes_size = graph.nodes.len();
        let mut on_stack = vec![false; nodes_size];
        let mut indexs = vec![-1; nodes_size];
        let mut lowlinks = vec![-1; nodes_size];
        let mut index = 0;
        let mut stack : Vec<usize> = Vec::with_capacity(nodes_size);

        let mut scc = SCC{ components:Vec::new() };

        for v in 0..nodes_size
        {
            if indexs[v] != -1 { continue; } // has been visited
            scc.strong_connect(graph, &mut stack, &mut on_stack, &mut indexs, &mut lowlinks, &mut index, v)
        }
        scc
    }
}

#[derive(Debug)]
pub struct Sort
{
    pub topology : Vec<usize>,
}

impl Sort
{
    pub fn new(graph:&Graph) -> Sort
    {
        let nodes_size = graph.nodes.len();
        let mut topology = Vec::with_capacity(nodes_size);
        
        let mut indegrees = vec![0; nodes_size];

        for node in graph.nodes.iter()
        {
            for next in node.nexts.iter()
            {
                indegrees[*next] += 1;
            }
        }

        let mut worklist = Vec::with_capacity(nodes_size);
        loop {
            for (nindex, indegree) in indegrees.iter_mut().enumerate()
            {
                if *indegree == 0 
                { 
                    worklist.push(nindex);
                    *indegree = -1; // -1 != 0, it won't be visited more.
                }
            }
            let Some(nindex) = worklist.pop() else { break; };
            topology.push(nindex);
            for next in graph.nodes[nindex].nexts.iter()
            {
                indegrees[*next] -= 1;
            }
        }
        Sort{ topology }
    }   
}

pub fn make_supergraph(graph:&Graph, scc:&SCC) -> Graph
{
    let mut node_super_map : Vec<usize> = vec![0; graph.nodes.len()];
    scc.components.iter().enumerate()
    .for_each(|(super_index, component)|{
        component.iter().for_each(|index|{
            node_super_map[*index] = super_index;
        });
    });
    let node_super_map = node_super_map; // no more mutate

    let nodes = scc.components.iter().map(|component|{
        let mut nexts = HashSet::new();
        for index in component
        {
            for next in graph.nodes[*index].nexts.iter()
            {
                let next = node_super_map[*next];
                if next != node_super_map[*index] // delete loop : i -> i
                { nexts.insert(next); }
            }
        }
        let nexts = nexts.into_iter().collect::<Vec<usize>>();
        Node { nexts }
    }).collect::<Vec<Node>>();
    Graph {nodes}
}

pub fn make_top_sort(graph:&Graph) -> Vec<Vec<usize>>
{
    let scc = SCC::new(graph);
    // to shrink component as supernode
    let supergraph = make_supergraph(graph, &scc); 
    let sort = Sort::new(&supergraph);

    sort.topology.into_iter().map(|super_index|{
        scc.components[super_index].clone()
    }).collect()
}