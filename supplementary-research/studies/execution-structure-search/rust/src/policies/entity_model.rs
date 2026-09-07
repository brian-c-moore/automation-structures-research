//! Entity / addressing model policy (docs/execution-modalities.md).
//!
//! Where work attaches and how it is addressed.
//!  - AnonymousOperator: positional slots in a declared graph
//!  - NamedGraphNode:    named nodes, queryable topology
//!  - AddressableEntity: PIDs/ActorRefs/grains, runtime-emergent topology
//!  - ChannelEndpoint:   first-class channels (CSP, Go, π-calculus names)

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntityModel {
    AnonymousOperator,
    NamedGraphNode,
    AddressableEntity,
    ChannelEndpoint,
}

impl EntityModel {
    pub fn parse(s: &str) -> Result<Self, String> {
        match s {
            "AnonymousOperator" | "anonymous" => Ok(EntityModel::AnonymousOperator),
            "NamedGraphNode" | "named" => Ok(EntityModel::NamedGraphNode),
            "AddressableEntity" | "addressable" => Ok(EntityModel::AddressableEntity),
            "ChannelEndpoint" | "channel" => Ok(EntityModel::ChannelEndpoint),
            other => Err(format!("unknown entity model: {}", other)),
        }
    }
}
