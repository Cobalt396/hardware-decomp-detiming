use egglog::{ast::Literal, *};
use egraph_serialize::{ClassId, EGraph, NodeId};
use indexmap::{IndexMap, IndexSet};
use super::*;
use rustc_hash::FxHashMap;

struct CostSet {
    costs: FxHashMap<ClassId, Cost>,
    total: Cost,
    choice: NodeId,
}

pub struct GreedyDagExtractor;
impl Extractor for GreedyDagExtractor {
    fn extract(&self, egraph: &EGraph, _roots: &[ClassId]) -> ExtractionResult {
        let mut costs = FxHashMap::<ClassId, CostSet>::with_capacity_and_hasher(
            egraph.classes().len(),
            Default::default(),
        );

        let mut keep_going = true;

        let mut i = 0;
        while keep_going {
            i += 1;
            println!("iteration {}", i);
            keep_going = false;

            'node_loop: for (node_id, node) in &egraph.nodes {
                let cid = egraph.nid_to_cid(node_id);
                let mut cost_set = CostSet {
                    costs: Default::default(),
                    total: Cost::default(),
                    choice: node_id.clone(),
                };

                // compute the cost set from the children
                for child in &node.children {
                    let child_cid = egraph.nid_to_cid(child);
                    if let Some(child_cost_set) = costs.get(child_cid) {
                        // prevent a cycle
                        if child_cost_set.costs.contains_key(cid) {
                            continue 'node_loop;
                        }
                        cost_set.costs.extend(child_cost_set.costs.clone());
                    } else {
                        continue 'node_loop;
                    }
                }

                // add this node
                cost_set.costs.insert(cid.clone(), node.cost);

                cost_set.total = cost_set.costs.values().sum();

                // if the cost set is better than the current one, update it
                if let Some(old_cost_set) = costs.get(cid) {
                    if cost_set.total < old_cost_set.total {
                        costs.insert(cid.clone(), cost_set);
                        keep_going = true;
                    }
                } else {
                    costs.insert(cid.clone(), cost_set);
                    keep_going = true;
                }
            }
        }

        let mut result = ExtractionResult::default();
        for (cid, cost_set) in costs {
            result.choose(cid, cost_set.choice);
        }
        result
    }
}

pub fn get_unextractables(egraph: &egglog::EGraph) -> IndexSet<String> {
    let unextractables = egraph
        .functions
        .iter()
        .filter_map(|(name, func)| {
            if func.is_extractable() {
                None
            } else {
                Some(name.to_string())
            }
        })
        .collect();
    unextractables
}

pub fn serialized_egraph(
    egglog_egraph: egglog::EGraph,
) -> (egraph_serialize::EGraph, IndexSet<String>) {
    let config = SerializeConfig::default();
    let egraph = egglog_egraph.serialize(config);

    (egraph, get_unextractables(&egglog_egraph))
}

fn main() {
    let mut egraph = egglog::EGraph::default();

    egraph.parse_and_run_program(None, 
        r#"(datatype Net
          (Var String)
          (Not Net)
          (Gate)
		  (Reg i64)
		  (Wire String)
          (Overlay Net Net)
          (Connect Net Net))

            (ruleset rewrite-rules)
        ;; --- Overlay ---
        ;; Commutativity:
        ;;   G1 + G2 ~~> G2 + G1
        (birewrite (Overlay G1 G2) (Overlay G2 G1)
                :ruleset rewrite-rules)
        ;; Associativity:
        ;;   (G1 + G2) + G3 ~~> G1 + (G2 + G3)
        (birewrite (Overlay (Overlay G1 G2) G3)
                    (Overlay G1 (Overlay G2 G3))
                :ruleset rewrite-rules)

        ;; --- Connect ---
        ;; Associativity: 
        ;;   (G1 -> G2) -> G3 ~~> G1 -> (G2 -> G3)
        (birewrite (Connect (Connect G1 G2) G3)
                (Connect G1 (Connect G2 G3))
                :ruleset rewrite-rules)

        ;; Left and right distributivity:
        ;;   G1 -> (G2 + G3) ~~> (G1 -> G2) + (G1 -> G3)
        (birewrite (Connect G1 (Overlay G2 G3))
                (Overlay (Connect G1 G2) (Connect G1 G3))
                :ruleset rewrite-rules)
        ;;   (G1 + G2) -> G3 ~~> (G1 -> G3) + (G2 -> G3)
        (birewrite (Connect (Overlay G1 G2) G3)
                (Overlay (Connect G1 G3) (Connect G2 G3))
                :ruleset rewrite-rules)

        ;; --- Pushing Registers ---
        ;;Rewrite for pushing two registers through a gate (one output)
        (rewrite 
                (Connect (Connect (Overlay A B) (Gate)) (Reg N))
            (Connect (Overlay (Connect A (Reg N)) (Connect B (Reg N))) (Gate))
        :ruleset rewrite-rules) 

        ;;Rewrite for pushing one register through a gate (one output)
        ;;Note that for multiple in-line registers, the rewrites expect Connects to be done left to right in order to properly apply these rules 
        ;;(Associativity rewrites don't seem to be applying)
        (rewrite
                    (Connect(Connect A (Gate)) (Reg N))
            (Connect(Connect A (Reg N)) (Gate))
        :ruleset rewrite-rules)"#).unwrap();

        
        egraph.parse_and_run_program(None, 
            r#"(let c1 
        		(Connect(Connect (Connect (Var "a") (Gate)) (Reg 0)) (Gate))
                )
            "#).unwrap();

        
        // // Gus's code to make an svg?
        // let serialized = egraph.serialize_for_graphviz(true, usize::MAX, usize::MAX);
        // let svg_path = Path::new("tmp").with_extension("svg");
        // serialized.to_svg_file(svg_path).unwrap();
        let serialized = serialized_egraph(egraph);
        let output = extract(serialized);
}
