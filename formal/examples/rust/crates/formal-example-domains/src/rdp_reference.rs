use crate::rdp::{AccountantConfig, CertifiedQuery, ProjectionCandidate};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceEvaluation {
    pub cumulative_curve: Vec<u64>,
    pub candidates: Vec<ProjectionCandidate>,
    pub reported_epsilon: u64,
    pub winner_alpha: Option<u64>,
}

/// Structure-free fixed-grid RDP accountant.
///
/// This evaluator reads accepted query declarations. It does not inspect a
/// Budget, registry, trace, winner selected by the construction, or committed
/// account state.
pub fn evaluate_prefix(
    config: &AccountantConfig,
    queries: &[CertifiedQuery],
) -> Result<ReferenceEvaluation, String> {
    let mut cumulative_curve = vec![0u64; config.orders.len()];
    for query in queries {
        if query.rdp_costs.len() != config.orders.len() {
            return Err(format!(
                "query {} has {} costs for {} registered orders",
                query.id,
                query.rdp_costs.len(),
                config.orders.len()
            ));
        }
        for (total, cost) in cumulative_curve.iter_mut().zip(&query.rdp_costs) {
            *total = total
                .checked_add(*cost)
                .ok_or_else(|| "reference RDP sum overflow".to_string())?;
        }
    }

    let mut candidates = Vec::with_capacity(config.orders.len());
    for (alpha, rdp_epsilon) in config.orders.iter().zip(&cumulative_curve) {
        let denominator = alpha
            .checked_sub(1)
            .ok_or_else(|| "reference order is not greater than one".to_string())?;
        if !config.log_reciprocal_delta.is_multiple_of(denominator) {
            return Err(format!(
                "conversion penalty is not integral for order {alpha}"
            ));
        }
        let penalty = config.log_reciprocal_delta / denominator;
        let epsilon = rdp_epsilon
            .checked_add(penalty)
            .ok_or_else(|| "reference conversion overflow".to_string())?;
        candidates.push(ProjectionCandidate {
            alpha: *alpha,
            epsilon,
        });
    }

    if queries.is_empty() {
        return Ok(ReferenceEvaluation {
            cumulative_curve,
            candidates,
            reported_epsilon: 0,
            winner_alpha: None,
        });
    }

    let winner = candidates
        .iter()
        .min_by_key(|candidate| (candidate.epsilon, candidate.alpha))
        .cloned()
        .ok_or_else(|| "reference order grid is empty".to_string())?;
    Ok(ReferenceEvaluation {
        cumulative_curve,
        candidates,
        reported_epsilon: winner.epsilon,
        winner_alpha: Some(winner.alpha),
    })
}
