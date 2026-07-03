use std::{collections::HashMap, sync::Arc};

use super::CompiledMultisigCertificate;
use simplicityhl::simplicity::types::arrow::FinalArrow;
use simplicityhl::simplicity::types::{CompleteBound, Final};

#[derive(Default)]
struct CoqTypeRegistry {
    type_indices: HashMap<Arc<Final>, usize>,
    type_definitions: Vec<CoqBridgeTypeDefinition>,
    arrow_indices: HashMap<FinalArrow, usize>,
    arrow_definitions: Vec<(usize, usize)>,
}

enum CoqBridgeTypeDefinition {
    Unit,
    Sum { left: usize, right: usize },
    Product { left: usize, right: usize },
}

pub(super) struct CoqTypeArtifact {
    pub type_definitions: Vec<String>,
    pub arrow_definitions: Vec<String>,
    pub type_table_entries: Vec<String>,
    pub root_arrow: usize,
}

impl CoqTypeRegistry {
    fn intern_type(&mut self, ty: &Arc<Final>) -> usize {
        if let Some(index) = self.type_indices.get(ty) {
            return *index;
        }

        let definition = match ty.bound() {
            CompleteBound::Unit => CoqBridgeTypeDefinition::Unit,
            CompleteBound::Sum(left, right) => {
                let left = self.intern_type(left);
                let right = self.intern_type(right);
                CoqBridgeTypeDefinition::Sum { left, right }
            }
            CompleteBound::Product(left, right) => {
                let left = self.intern_type(left);
                let right = self.intern_type(right);
                CoqBridgeTypeDefinition::Product { left, right }
            }
        };

        let index = self.type_definitions.len();
        self.type_indices.insert(Arc::clone(ty), index);
        self.type_definitions.push(definition);
        index
    }

    fn intern_arrow(&mut self, arrow: &FinalArrow) -> usize {
        if let Some(index) = self.arrow_indices.get(arrow) {
            return *index;
        }

        let source = self.intern_type(&arrow.source);
        let target = self.intern_type(&arrow.target);
        let index = self.arrow_definitions.len();

        self.arrow_indices.insert(arrow.shallow_clone(), index);
        self.arrow_definitions.push((source, target));
        index
    }
}

pub(super) fn coq_type_artifact(certificate: &CompiledMultisigCertificate) -> CoqTypeArtifact {
    let mut registry = CoqTypeRegistry::default();
    let type_table = certificate
        .type_table
        .iter()
        .map(|entry| entry.as_ref().map(|arrow| registry.intern_arrow(arrow)))
        .collect::<Vec<_>>();
    let root_arrow = registry.intern_arrow(&certificate.root_arrow);

    CoqTypeArtifact {
        type_definitions: registry
            .type_definitions
            .iter()
            .map(|definition| match definition {
                CoqBridgeTypeDefinition::Unit => String::from("CBTDUnit"),
                CoqBridgeTypeDefinition::Sum { left, right } => {
                    format!("CBTDSum {left} {right}")
                }
                CoqBridgeTypeDefinition::Product { left, right } => {
                    format!("CBTDProd {left} {right}")
                }
            })
            .collect(),
        arrow_definitions: registry
            .arrow_definitions
            .iter()
            .map(|(source, target)| format!("({source}, {target})"))
            .collect(),
        type_table_entries: type_table
            .iter()
            .map(|entry| {
                entry
                    .as_ref()
                    .map_or_else(|| String::from("None"), |arrow| format!("Some {arrow}"))
            })
            .collect(),
        root_arrow,
    }
}
