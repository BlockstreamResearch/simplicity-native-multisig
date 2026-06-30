use std::collections::{HashMap, hash_map::Entry};

use simplicityhl::simplicity::Cmr;
use simplicityhl::simplicity::dag::{Dag, DagLike, SharingTracker};
use simplicityhl::simplicity::jet::Elements;
use simplicityhl::simplicity::node::{Disconnectable, Inner};
use simplicityhl::simplicity::types::arrow::FinalArrow;
use simplicityhl::simplicity::{CommitNode, Ihr};

#[derive(Copy, Clone)]
enum EncodedCommitNode<'node> {
    Node(&'node CommitNode<Elements>),
    Hidden(Cmr),
}

impl DagLike for EncodedCommitNode<'_> {
    type Node = Self;

    fn data(&self) -> &Self {
        self
    }

    fn as_dag_node(&self) -> Dag<Self> {
        let node = match *self {
            EncodedCommitNode::Node(node) => node,
            EncodedCommitNode::Hidden(_) => return Dag::Nullary,
        };

        match node.inner() {
            Inner::Unit | Inner::Iden | Inner::Fail(_) | Inner::Jet(_) | Inner::Word(_) => {
                Dag::Nullary
            }
            Inner::InjL(child) | Inner::InjR(child) | Inner::Take(child) | Inner::Drop(child) => {
                Dag::Unary(EncodedCommitNode::Node(child.as_ref()))
            }
            Inner::Comp(left, right) | Inner::Case(left, right) | Inner::Pair(left, right) => {
                Dag::Binary(
                    EncodedCommitNode::Node(left.as_ref()),
                    EncodedCommitNode::Node(right.as_ref()),
                )
            }
            Inner::Disconnect(left, right) => right
                .disconnect_dag_ref(left.as_ref())
                .map(EncodedCommitNode::Node),
            Inner::AssertL(left, right_cmr) => Dag::Binary(
                EncodedCommitNode::Node(left.as_ref()),
                EncodedCommitNode::Hidden(*right_cmr),
            ),
            Inner::AssertR(left_cmr, right) => Dag::Binary(
                EncodedCommitNode::Hidden(*left_cmr),
                EncodedCommitNode::Node(right.as_ref()),
            ),
            Inner::Witness(_) => Dag::Nullary,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum EncodedCommitId {
    Node(Ihr),
    Hidden(Cmr),
}

#[derive(Clone, Default)]
struct EncodedCommitSharing {
    map: HashMap<EncodedCommitId, usize>,
}

impl SharingTracker<EncodedCommitNode<'_>> for EncodedCommitSharing {
    fn record(&mut self, node: &EncodedCommitNode<'_>, index: usize) -> Option<usize> {
        let id = match node {
            EncodedCommitNode::Node(node) => EncodedCommitId::Node(node.sharing_id()?),
            EncodedCommitNode::Hidden(cmr) => EncodedCommitId::Hidden(*cmr),
        };

        match self.map.entry(id) {
            Entry::Occupied(entry) => Some(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(index);
                None
            }
        }
    }

    fn seen_before(&self, node: &EncodedCommitNode<'_>) -> Option<usize> {
        let id = match node {
            EncodedCommitNode::Node(node) => EncodedCommitId::Node(node.sharing_id()?),
            EncodedCommitNode::Hidden(cmr) => EncodedCommitId::Hidden(*cmr),
        };

        self.map.get(&id).copied()
    }
}

pub(super) fn encoded_type_table(program: &CommitNode<Elements>) -> Vec<Option<FinalArrow>> {
    EncodedCommitNode::Node(program)
        .post_order_iter::<EncodedCommitSharing>()
        .map(|item| match item.node {
            EncodedCommitNode::Node(node) => Some(node.arrow().shallow_clone()),
            EncodedCommitNode::Hidden(_) => None,
        })
        .collect()
}
