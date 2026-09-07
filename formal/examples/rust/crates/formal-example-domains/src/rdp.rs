use crate::rdp_reference as references;

use formal_example_structures::{
    ActuationPass, Budget, CompetitiveSelection, RecipeEdge, ResourceRegistry, Sequential,
    Structure, StructureError, TraceLog, Unit,
};
use std::collections::BTreeSet;

pub use references::{evaluate_prefix, ReferenceEvaluation};

pub const MICRO_EPSILON_SCALE: u64 = 1_000_000;
pub const LOG_RECIPROCAL_DELTA: u64 = 24 * MICRO_EPSILON_SCALE;
pub const FIXED_ORDERS: [u64; 6] = [2, 3, 5, 9, 17, 33];
pub const DEFAULT_EPSILON_CEILING: u64 = 5 * MICRO_EPSILON_SCALE;
pub const ORDER_LEDGER_CAPACITY: u64 = 1_000 * MICRO_EPSILON_SCALE;

const RUN_SUBJECT: &str = "FEX-DOM-PRIV-01::run";

const ACCEPT_STRUCTURES: &[Structure] = &[
    Structure::Sequential,
    Structure::CompetitiveSelection,
    Structure::Budget,
    Structure::ResourceRegistry,
    Structure::ActuationPass,
];

const ACCEPT_EDGES: &[RecipeEdge] = &[
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::CompetitiveSelection,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::CompetitiveSelection,
        before_action: "Commit",
        after: Structure::Budget,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::Budget,
        before_action: "Commit",
        after: Structure::ResourceRegistry,
        after_action: "Store",
    },
    RecipeEdge {
        before: Structure::ResourceRegistry,
        before_action: "Store",
        after: Structure::ActuationPass,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::ActuationPass,
        before_action: "Commit",
        after: Structure::Sequential,
        after_action: "Complete",
    },
];

const REJECT_STRUCTURES: &[Structure] = &[
    Structure::Sequential,
    Structure::CompetitiveSelection,
    Structure::Budget,
];

const REJECT_EDGES: &[RecipeEdge] = &[
    RecipeEdge {
        before: Structure::Sequential,
        before_action: "Begin",
        after: Structure::CompetitiveSelection,
        after_action: "Commit",
    },
    RecipeEdge {
        before: Structure::CompetitiveSelection,
        before_action: "Commit",
        after: Structure::Budget,
        after_action: "Reject",
    },
    RecipeEdge {
        before: Structure::Budget,
        before_action: "Reject",
        after: Structure::Sequential,
        after_action: "Complete",
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RdpMicroEpsilon;

impl Unit for RdpMicroEpsilon {
    const NAME: &'static str = "RdpMicroEpsilon";
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReportedMicroEpsilon;

impl Unit for ReportedMicroEpsilon {
    const NAME: &'static str = "ReportedMicroEpsilon";
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccountantConfig {
    pub(crate) orders: Vec<u64>,
    pub(crate) scale: u64,
    pub(crate) log_reciprocal_delta: u64,
    pub(crate) epsilon_ceiling: u64,
    pub(crate) order_ledger_capacity: u64,
    pub adjacency_relation: String,
}

impl AccountantConfig {
    pub fn fixed(epsilon_ceiling: u64) -> Result<Self, StructureError> {
        let config = Self {
            orders: FIXED_ORDERS.to_vec(),
            scale: MICRO_EPSILON_SCALE,
            log_reciprocal_delta: LOG_RECIPROCAL_DELTA,
            epsilon_ceiling,
            order_ledger_capacity: ORDER_LEDGER_CAPACITY,
            adjacency_relation: "replace-one-record".to_string(),
        };
        config.validate()?;
        Ok(config)
    }

    pub fn orders(&self) -> &[u64] {
        &self.orders
    }

    pub fn scale(&self) -> u64 {
        self.scale
    }

    pub fn epsilon_ceiling(&self) -> u64 {
        self.epsilon_ceiling
    }

    pub fn delta_description(&self) -> &'static str {
        "exp(-24)"
    }

    fn validate(&self) -> Result<(), StructureError> {
        if self.orders.is_empty() || self.scale == 0 || self.epsilon_ceiling == 0 {
            return Err(StructureError::new(
                "RDP configuration requires orders, scale, and a positive epsilon ceiling",
            ));
        }
        let mut unique = BTreeSet::new();
        for alpha in &self.orders {
            if *alpha <= 1 || !unique.insert(*alpha) {
                return Err(StructureError::new(
                    "RDP orders must be unique integers greater than one",
                ));
            }
            if !self.log_reciprocal_delta.is_multiple_of(alpha - 1) {
                return Err(StructureError::new(format!(
                    "RDP conversion penalty is not integral for order {alpha}"
                )));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedQuery {
    pub id: String,
    pub rdp_costs: Vec<u64>,
}

impl CertifiedQuery {
    pub fn linear(
        id: impl Into<String>,
        base_cost: u64,
        config: &AccountantConfig,
    ) -> Result<Self, StructureError> {
        let rdp_costs = config
            .orders
            .iter()
            .map(|alpha| {
                alpha
                    .checked_mul(base_cost)
                    .ok_or_else(|| StructureError::new("linear RDP curve overflow"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            id: id.into(),
            rdp_costs,
        })
    }

    fn validate(&self, config: &AccountantConfig) -> Result<(), StructureError> {
        if self.id.is_empty() {
            return Err(StructureError::new("query identity cannot be empty"));
        }
        if self.rdp_costs.len() != config.orders.len() {
            return Err(StructureError::new(format!(
                "query {} has {} costs for {} registered orders",
                self.id,
                self.rdp_costs.len(),
                config.orders.len()
            )));
        }
        if self.rdp_costs.windows(2).any(|pair| pair[0] > pair[1]) {
            return Err(StructureError::new(format!(
                "query {} RDP curve is not monotone across the registered orders",
                self.id
            )));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryRequest {
    pub account: String,
    pub query: CertifiedQuery,
}

impl QueryRequest {
    pub fn new(account: impl Into<String>, query: CertifiedQuery) -> Self {
        Self {
            account: account.into(),
            query,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ProjectionCandidate {
    pub alpha: u64,
    pub epsilon: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct QueryRecord {
    query: CertifiedQuery,
    reported_epsilon_after: u64,
    winner_alpha_after: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AccountState {
    account_id: String,
    query_registry: ResourceRegistry<QueryRecord>,
    order_budgets: Vec<Budget<RdpMicroEpsilon>>,
    reported_budget: Budget<ReportedMicroEpsilon>,
    reported_epsilon: u64,
    winner_alpha: Option<u64>,
    accepted_queries: Vec<CertifiedQuery>,
    released_queries: u64,
}

impl AccountState {
    fn new(account_id: &str, config: &AccountantConfig, trace: &mut TraceLog) -> Self {
        let query_registry = ResourceRegistry::empty(
            trace,
            &format!("FEX-DOM-PRIV-01::account::{account_id}::queries"),
        );
        let order_budgets = config
            .orders
            .iter()
            .map(|alpha| {
                Budget::new(
                    config.order_ledger_capacity,
                    trace,
                    &format!("FEX-DOM-PRIV-01::account::{account_id}::order-{alpha}"),
                )
            })
            .collect();
        let reported_budget = Budget::new(
            config.epsilon_ceiling,
            trace,
            &format!("FEX-DOM-PRIV-01::account::{account_id}::reported"),
        );
        Self {
            account_id: account_id.to_string(),
            query_registry,
            order_budgets,
            reported_budget,
            reported_epsilon: 0,
            winner_alpha: None,
            accepted_queries: Vec::new(),
            released_queries: 0,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AccountantControl {
    Honest,
    ReuseQueryIdentity,
    OmitOrderCharge,
    DoubleOrderCharge,
    DropDeltaPenalty,
    OmitBestOrderCandidate,
    SumPerQueryConvertedBounds,
    BypassReportedBudget,
    MisdirectAccount,
    MutateRejectedState,
    MisorderLaterCommit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequestWitness {
    subject: String,
    requested_account: String,
    actual_account: String,
    query: CertifiedQuery,
    before_accounts: Vec<AccountState>,
    after_accounts: Vec<AccountState>,
    candidate_curve: Vec<u64>,
    supplied_candidates: Vec<ProjectionCandidate>,
    proposed_epsilon: u64,
    winner_alpha: u64,
    accepted: bool,
    order_subjects: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AccountSummary {
    pub account_id: String,
    pub accepted_queries: usize,
    pub reported_epsilon: u64,
    pub winner_alpha: Option<u64>,
    pub cumulative_curve: Vec<u64>,
}

pub struct AccountantRun {
    account_registry: ResourceRegistry<usize>,
    account_ids: Vec<String>,
    accounts: Vec<AccountState>,
    config: AccountantConfig,
    requests: Vec<QueryRequest>,
    witnesses: Vec<RequestWitness>,
    pub trace: TraceLog,
}

impl AccountantRun {
    pub fn account(&self, account_id: &str) -> Option<AccountSummary> {
        let index = self.account_registry.get(account_id).copied()?;
        let account = self.accounts.get(index)?;
        Some(AccountSummary {
            account_id: account.account_id.clone(),
            accepted_queries: account.accepted_queries.len(),
            reported_epsilon: account.reported_epsilon,
            winner_alpha: account.winner_alpha,
            cumulative_curve: account.order_budgets.iter().map(Budget::spent).collect(),
        })
    }

    pub fn request_count(&self) -> usize {
        self.requests.len()
    }

    pub fn accepted_count(&self) -> usize {
        self.witnesses
            .iter()
            .filter(|witness| witness.accepted)
            .count()
    }

    pub fn rejected_count(&self) -> usize {
        self.witnesses.len() - self.accepted_count()
    }
}

pub fn run_workload(
    account_ids: &[&str],
    config: &AccountantConfig,
    requests: &[QueryRequest],
    control: AccountantControl,
) -> Result<AccountantRun, StructureError> {
    config.validate()?;
    if account_ids.len() < 2 {
        return Err(StructureError::new(
            "FEX-DOM-PRIV-01 requires at least two accounts for target discrimination",
        ));
    }
    if requests.is_empty() {
        return Err(StructureError::new(
            "FEX-DOM-PRIV-01 requires a nonempty request stream",
        ));
    }

    let mut trace = TraceLog::default();
    let account_ids = account_ids
        .iter()
        .map(|account| (*account).to_string())
        .collect::<Vec<_>>();
    let account_registry = ResourceRegistry::build(
        account_ids
            .iter()
            .enumerate()
            .map(|(index, account)| (account.clone(), index)),
        &mut trace,
        RUN_SUBJECT,
    )?;
    let mut accounts = account_ids
        .iter()
        .map(|account| AccountState::new(account, config, &mut trace))
        .collect::<Vec<_>>();
    let mut carrier = Sequential::new(
        requests.len() as u64,
        "initialized".to_string(),
        &mut trace,
        RUN_SUBJECT,
    )?;
    let mut witnesses = Vec::new();
    let mut accepted_ordinal = 0usize;

    for (index, request) in requests.iter().enumerate() {
        let subject = format!("FEX-DOM-PRIV-01::request-{index}");
        let step = carrier.begin_step(&mut trace, &subject)?;
        let witness = process_request(
            &account_registry,
            &account_ids,
            &mut accounts,
            config,
            request,
            control,
            accepted_ordinal,
            &mut trace,
            &subject,
        )?;
        if witness.accepted {
            accepted_ordinal += 1;
        }
        let outcome = if witness.accepted {
            format!("accepted:{}", request.query.id)
        } else {
            format!("rejected:{}", request.query.id)
        };
        carrier.complete_step(step, outcome, &mut trace, &subject)?;
        witnesses.push(witness);
    }
    carrier.done_stuttering(&mut trace, RUN_SUBJECT)?;

    Ok(AccountantRun {
        account_registry,
        account_ids,
        accounts,
        config: config.clone(),
        requests: requests.to_vec(),
        witnesses,
        trace,
    })
}

#[allow(clippy::too_many_arguments)]
fn process_request(
    account_registry: &ResourceRegistry<usize>,
    account_ids: &[String],
    accounts: &mut [AccountState],
    config: &AccountantConfig,
    request: &QueryRequest,
    control: AccountantControl,
    accepted_ordinal: usize,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<RequestWitness, StructureError> {
    let requested_index = account_registry
        .get(&request.account)
        .copied()
        .ok_or_else(|| {
            StructureError::new(format!("unknown privacy account {}", request.account))
        })?;
    request.query.validate(config)?;
    let before_accounts = accounts.to_vec();
    let before = &before_accounts[requested_index];

    let mut effective_query = request.query.clone();
    if control == AccountantControl::ReuseQueryIdentity {
        if let Some(first) = before.accepted_queries.first() {
            effective_query.id = first.id.clone();
        }
    }

    let candidate_curve = compose_candidate_curve(before, &effective_query, control)?;
    let mut supplied_candidates = project_candidates(config, &candidate_curve, control)?;
    if control == AccountantControl::OmitBestOrderCandidate {
        let best = domain_min_index(&supplied_candidates)?;
        supplied_candidates.remove(best);
    }

    let defer_selection = control == AccountantControl::MisorderLaterCommit && accepted_ordinal > 0;
    let winner_index = if defer_selection {
        domain_min_index(&supplied_candidates)?
    } else {
        CompetitiveSelection::select_min_index(
            &supplied_candidates,
            |candidate| (candidate.epsilon, candidate.alpha),
            trace,
            subject,
        )?
    };
    let selected = supplied_candidates
        .get(winner_index)
        .cloned()
        .ok_or_else(|| StructureError::new("selected RDP order is out of range"))?;

    let proposed_epsilon = if control == AccountantControl::SumPerQueryConvertedBounds {
        let standalone = project_candidates(
            config,
            &effective_query.rdp_costs,
            AccountantControl::Honest,
        )?;
        let standalone_index = domain_min_index(&standalone)?;
        before
            .reported_epsilon
            .checked_add(standalone[standalone_index].epsilon)
            .ok_or_else(|| StructureError::new("scalar converted-bound sum overflow"))?
    } else {
        selected.epsilon
    };
    let increment = proposed_epsilon
        .checked_sub(before.reported_epsilon)
        .ok_or_else(|| StructureError::new("reported privacy bound decreased"))?;
    let within_ceiling = increment <= before.reported_budget.remaining();
    let bypass_ceiling = control == AccountantControl::BypassReportedBudget && !within_ceiling;
    let mutate_rejection = control == AccountantControl::MutateRejectedState && !within_ceiling;
    let order_subjects = config
        .orders
        .iter()
        .map(|alpha| format!("{subject}::order-{alpha}"))
        .collect::<Vec<_>>();
    let actual_index = if control == AccountantControl::MisdirectAccount {
        (requested_index + 1) % accounts.len()
    } else {
        requested_index
    };
    let actual_account = account_ids[actual_index].clone();

    let accepted = if within_ceiling || bypass_ceiling {
        let mut candidate = before.clone();
        for (index, budget) in candidate.order_budgets.iter_mut().enumerate() {
            let amount = candidate_curve[index]
                .checked_sub(before.order_budgets[index].spent())
                .ok_or_else(|| StructureError::new("candidate RDP coordinate decreased"))?;
            budget.try_reserve(amount, trace, &order_subjects[index])?;
        }
        if !bypass_ceiling {
            candidate
                .reported_budget
                .try_reserve(increment, trace, subject)?;
        }
        candidate.query_registry.insert(
            effective_query.id.clone(),
            QueryRecord {
                query: effective_query.clone(),
                reported_epsilon_after: proposed_epsilon,
                winner_alpha_after: selected.alpha,
            },
            trace,
            subject,
        )?;
        candidate.reported_epsilon = proposed_epsilon;
        candidate.winner_alpha = Some(selected.alpha);
        candidate.accepted_queries.push(effective_query.clone());
        candidate.released_queries = candidate
            .released_queries
            .checked_add(1)
            .ok_or_else(|| StructureError::new("release counter overflow"))?;

        commit_account_candidate(accounts, actual_index, candidate, trace, subject)?;
        if defer_selection {
            let observed = CompetitiveSelection::select_min_index(
                &supplied_candidates,
                |item| (item.epsilon, item.alpha),
                trace,
                subject,
            )?;
            if observed != winner_index {
                return Err(StructureError::new(
                    "deferred selection differs from the computed winner",
                ));
            }
        }
        true
    } else {
        let mut admission_probe = before.reported_budget.clone();
        if admission_probe
            .try_reserve(increment, trace, subject)
            .is_ok()
        {
            return Err(StructureError::new(
                "reported Budget accepted an over-ceiling candidate",
            ));
        }
        if mutate_rejection {
            let mut candidate = before.clone();
            let amount = effective_query.rdp_costs[0];
            candidate.order_budgets[0].try_reserve(amount, trace, &order_subjects[0])?;
            commit_account_candidate(accounts, actual_index, candidate, trace, subject)?;
        }
        false
    };

    Ok(RequestWitness {
        subject: subject.to_string(),
        requested_account: request.account.clone(),
        actual_account,
        query: effective_query,
        before_accounts,
        after_accounts: accounts.to_vec(),
        candidate_curve,
        supplied_candidates,
        proposed_epsilon,
        winner_alpha: selected.alpha,
        accepted,
        order_subjects,
    })
}

fn compose_candidate_curve(
    before: &AccountState,
    query: &CertifiedQuery,
    control: AccountantControl,
) -> Result<Vec<u64>, StructureError> {
    before
        .order_budgets
        .iter()
        .zip(&query.rdp_costs)
        .enumerate()
        .map(|(index, (budget, cost))| {
            let amount = match control {
                AccountantControl::OmitOrderCharge if index == 0 => 0,
                AccountantControl::DoubleOrderCharge if index == 0 => cost
                    .checked_mul(2)
                    .ok_or_else(|| StructureError::new("double-charge overflow"))?,
                _ => *cost,
            };
            budget
                .spent()
                .checked_add(amount)
                .ok_or_else(|| StructureError::new("candidate RDP curve overflow"))
        })
        .collect()
}

fn project_candidates(
    config: &AccountantConfig,
    curve: &[u64],
    control: AccountantControl,
) -> Result<Vec<ProjectionCandidate>, StructureError> {
    if curve.len() != config.orders.len() {
        return Err(StructureError::new(
            "candidate curve differs from the registered order count",
        ));
    }
    config
        .orders
        .iter()
        .zip(curve)
        .map(|(alpha, rdp_epsilon)| {
            let penalty = if control == AccountantControl::DropDeltaPenalty {
                0
            } else {
                config.log_reciprocal_delta / (alpha - 1)
            };
            let epsilon = rdp_epsilon
                .checked_add(penalty)
                .ok_or_else(|| StructureError::new("RDP conversion overflow"))?;
            Ok(ProjectionCandidate {
                alpha: *alpha,
                epsilon,
            })
        })
        .collect()
}

fn domain_min_index(candidates: &[ProjectionCandidate]) -> Result<usize, StructureError> {
    candidates
        .iter()
        .enumerate()
        .min_by_key(|(_, candidate)| (candidate.epsilon, candidate.alpha))
        .map(|(index, _)| index)
        .ok_or_else(|| StructureError::new("RDP projection has no candidates"))
}

fn commit_account_candidate(
    accounts: &mut [AccountState],
    target_index: usize,
    candidate: AccountState,
    trace: &mut TraceLog,
    subject: &str,
) -> Result<(), StructureError> {
    let mut pass = ActuationPass::new(vec![Some(target_index)], trace, subject);
    pass.actuate_with(
        0,
        accounts,
        |account, _, _| {
            *account = candidate;
            Ok(())
        },
        trace,
        subject,
    )?;
    pass.finish(trace, subject)?;
    Ok(())
}

pub fn verify_run(run: &AccountantRun) -> Result<(), StructureError> {
    if run.account_registry.len() != run.account_ids.len()
        || run.accounts.len() != run.account_ids.len()
    {
        return Err(StructureError::new(
            "account registry differs from the executed account set",
        ));
    }
    for (index, account_id) in run.account_ids.iter().enumerate() {
        if run.account_registry.get(account_id) != Some(&index) {
            return Err(StructureError::new(format!(
                "account registry mapping differs for {account_id}"
            )));
        }
    }
    if run.requests.len() != run.witnesses.len() {
        return Err(StructureError::new(
            "request stream and witness stream differ",
        ));
    }

    let mut prior_after: Option<&[AccountState]> = None;
    for (request, witness) in run.requests.iter().zip(&run.witnesses) {
        if witness.requested_account != request.account {
            return Err(StructureError::new(format!(
                "witness {} changed the requested account identity",
                witness.subject
            )));
        }
        if witness.query != request.query {
            return Err(StructureError::new(format!(
                "witness {} changed the submitted query certificate",
                witness.subject
            )));
        }
        if let Some(previous) = prior_after {
            if witness.before_accounts != previous {
                return Err(StructureError::new(format!(
                    "witness {} does not begin at the prior completed state",
                    witness.subject
                )));
            }
        }
        let requested_index = run
            .account_registry
            .get(&witness.requested_account)
            .copied()
            .ok_or_else(|| StructureError::new("witness names an unknown account"))?;
        let before = &witness.before_accounts[requested_index];
        verify_account(before, &run.config, &witness.requested_account)?;

        let mut expected_queries = before.accepted_queries.clone();
        expected_queries.push(witness.query.clone());
        let expected = references::evaluate_prefix(&run.config, &expected_queries)
            .map_err(StructureError::new)?;
        if witness.candidate_curve != expected.cumulative_curve {
            return Err(StructureError::new(format!(
                "witness {} candidate curve differs from the independent prefix sum",
                witness.subject
            )));
        }
        if witness.supplied_candidates != expected.candidates {
            return Err(StructureError::new(format!(
                "witness {} selection candidates differ from the complete converted order set",
                witness.subject
            )));
        }
        if witness.proposed_epsilon != expected.reported_epsilon
            || Some(witness.winner_alpha) != expected.winner_alpha
        {
            return Err(StructureError::new(format!(
                "witness {} reported bound or winner differs from the independent evaluator",
                witness.subject
            )));
        }
        if witness.proposed_epsilon < before.reported_epsilon {
            return Err(StructureError::new(format!(
                "witness {} decreased the reported privacy bound",
                witness.subject
            )));
        }
        let should_accept = witness.proposed_epsilon <= run.config.epsilon_ceiling;
        if witness.accepted != should_accept {
            return Err(StructureError::new(format!(
                "witness {} decision differs from the hard epsilon ceiling",
                witness.subject
            )));
        }
        if witness.actual_account != witness.requested_account {
            return Err(StructureError::new(format!(
                "witness {} committed to {} instead of {}",
                witness.subject, witness.actual_account, witness.requested_account
            )));
        }

        if witness.accepted {
            for (index, (before_account, after_account)) in witness
                .before_accounts
                .iter()
                .zip(&witness.after_accounts)
                .enumerate()
            {
                if index != requested_index && before_account != after_account {
                    return Err(StructureError::new(format!(
                        "witness {} changed an untargeted account",
                        witness.subject
                    )));
                }
            }
            let after = &witness.after_accounts[requested_index];
            verify_account(after, &run.config, &witness.requested_account)?;
            if after.accepted_queries != expected_queries {
                return Err(StructureError::new(format!(
                    "witness {} committed a different accepted-query prefix",
                    witness.subject
                )));
            }
            run.trace.verify_recipe_instance_for(
                &witness.subject,
                ACCEPT_STRUCTURES,
                ACCEPT_EDGES,
            )?;
            for (index, order_subject) in witness.order_subjects.iter().enumerate() {
                let check = run.trace.require_single_event_for(
                    Structure::Budget,
                    "Check",
                    order_subject,
                )?;
                let expected_detail = format!("amount={} ", witness.query.rdp_costs[index]);
                if !check.detail.starts_with(&expected_detail) {
                    return Err(StructureError::new(format!(
                        "witness {} order charge differs at alpha {}",
                        witness.subject, run.config.orders[index]
                    )));
                }
                run.trace
                    .require_single_event_for(Structure::Budget, "Commit", order_subject)?;
            }
        } else {
            if witness.after_accounts != witness.before_accounts {
                return Err(StructureError::new(format!(
                    "witness {} changed state after rejection",
                    witness.subject
                )));
            }
            run.trace.verify_recipe_instance_for(
                &witness.subject,
                REJECT_STRUCTURES,
                REJECT_EDGES,
            )?;
        }
        prior_after = Some(&witness.after_accounts);
    }

    if run
        .witnesses
        .last()
        .is_none_or(|last| last.after_accounts != run.accounts)
    {
        return Err(StructureError::new(
            "final account state differs from the final request witness",
        ));
    }
    for (account, account_id) in run.accounts.iter().zip(&run.account_ids) {
        verify_account(account, &run.config, account_id)?;
    }
    run.trace
        .require_single_event_for(Structure::Sequential, "Done", RUN_SUBJECT)?;
    Ok(())
}

fn verify_account(
    account: &AccountState,
    config: &AccountantConfig,
    expected_account_id: &str,
) -> Result<(), StructureError> {
    let expected = references::evaluate_prefix(config, &account.accepted_queries)
        .map_err(StructureError::new)?;
    if account.account_id != expected_account_id {
        return Err(StructureError::new(format!(
            "account state identity {} differs from expected {expected_account_id}",
            account.account_id
        )));
    }
    if account.order_budgets.len() != config.orders.len() {
        return Err(StructureError::new(format!(
            "account {} has the wrong number of order ledgers",
            account.account_id
        )));
    }
    let observed_curve = account
        .order_budgets
        .iter()
        .map(Budget::spent)
        .collect::<Vec<_>>();
    if observed_curve != expected.cumulative_curve {
        return Err(StructureError::new(format!(
            "account {} order ledgers differ from accepted query declarations",
            account.account_id
        )));
    }
    if account.reported_epsilon != expected.reported_epsilon
        || account.winner_alpha != expected.winner_alpha
        || account.reported_budget.spent() != expected.reported_epsilon
        || account.reported_budget.capacity() != config.epsilon_ceiling
    {
        return Err(StructureError::new(format!(
            "account {} reported-bound ledger differs from the independent evaluator",
            account.account_id
        )));
    }
    if account.released_queries != account.accepted_queries.len() as u64
        || account.query_registry.len() != account.accepted_queries.len()
    {
        return Err(StructureError::new(format!(
            "account {} query registry and release count differ",
            account.account_id
        )));
    }
    for (index, query) in account.accepted_queries.iter().enumerate() {
        let prefix = references::evaluate_prefix(config, &account.accepted_queries[..=index])
            .map_err(StructureError::new)?;
        let expected_record = QueryRecord {
            query: query.clone(),
            reported_epsilon_after: prefix.reported_epsilon,
            winner_alpha_after: prefix
                .winner_alpha
                .ok_or_else(|| StructureError::new("nonempty prefix has no winning order"))?,
        };
        if account.query_registry.get(&query.id) != Some(&expected_record) {
            return Err(StructureError::new(format!(
                "account {} query record differs for {}",
                account.account_id, query.id
            )));
        }
    }
    Ok(())
}

pub fn demonstration_requests(
    config: &AccountantConfig,
) -> Result<Vec<QueryRequest>, StructureError> {
    let mut requests = Vec::new();
    for index in 1..=5 {
        requests.push(QueryRequest::new(
            "scope-a",
            CertifiedQuery::linear(format!("a-{index}"), 50_000, config)?,
        ));
    }
    for index in 1..=2 {
        requests.push(QueryRequest::new(
            "scope-b",
            CertifiedQuery::linear(format!("b-{index}"), 25_000, config)?,
        ));
    }
    Ok(requests)
}

pub fn expected_control_rejection(control: AccountantControl) -> Option<&'static str> {
    match control {
        AccountantControl::Honest => None,
        AccountantControl::ReuseQueryIdentity => Some("cannot replace existing ID"),
        AccountantControl::OmitOrderCharge | AccountantControl::DoubleOrderCharge => {
            Some("candidate curve differs from the independent prefix sum")
        }
        AccountantControl::DropDeltaPenalty | AccountantControl::OmitBestOrderCandidate => {
            Some("selection candidates differ from the complete converted order set")
        }
        AccountantControl::SumPerQueryConvertedBounds => {
            Some("reported bound or winner differs from the independent evaluator")
        }
        AccountantControl::BypassReportedBudget => {
            Some("decision differs from the hard epsilon ceiling")
        }
        AccountantControl::MisdirectAccount => Some("committed to scope-b instead of scope-a"),
        AccountantControl::MutateRejectedState => Some("changed state after rejection"),
        AccountantControl::MisorderLaterCommit => {
            Some("recipe edge CompetitiveSelection.Commit -> Budget.Commit is not ordered")
        }
    }
}

pub fn control_is_detected(control: AccountantControl) -> bool {
    let Some(expected) = expected_control_rejection(control) else {
        return false;
    };
    let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
    let requests = demonstration_requests(&config).unwrap();
    let observed = match run_workload(&["scope-a", "scope-b"], &config, &requests, control) {
        Err(error) => error.to_string(),
        Ok(run) => match verify_run(&run) {
            Err(error) => error.to_string(),
            Ok(()) => return false,
        },
    };
    observed.contains(expected)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_positive(config: &AccountantConfig, requests: &[QueryRequest]) -> AccountantRun {
        let run = run_workload(
            &["scope-a", "scope-b"],
            config,
            requests,
            AccountantControl::Honest,
        )
        .unwrap();
        verify_run(&run).unwrap();
        run
    }

    #[test]
    fn repeated_curve_changes_the_winning_order_and_rejects_the_fifth_query() {
        let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
        let requests = demonstration_requests(&config).unwrap();
        let run = run_positive(&config, &requests);
        let scope_a = run.account("scope-a").unwrap();
        assert_eq!(scope_a.accepted_queries, 4);
        assert_eq!(scope_a.reported_epsilon, 4_800_000);
        assert_eq!(scope_a.winner_alpha, Some(9));
        assert_eq!(run.accepted_count(), 6);
        assert_eq!(run.rejected_count(), 1);

        let winners = run
            .witnesses
            .iter()
            .filter(|witness| witness.requested_account == "scope-a" && witness.accepted)
            .map(|witness| witness.winner_alpha)
            .collect::<Vec<_>>();
        assert_eq!(winners, [17, 17, 17, 9]);
    }

    #[test]
    fn rejection_preserves_both_account_states() {
        let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
        let requests = demonstration_requests(&config).unwrap();
        let run = run_positive(&config, &requests);
        let rejected = run
            .witnesses
            .iter()
            .find(|witness| !witness.accepted)
            .unwrap();
        assert_eq!(rejected.before_accounts, rejected.after_accounts);
        assert_eq!(rejected.query.id, "a-5");
    }

    #[test]
    fn generated_curves_prefix_lengths_and_ceilings_match_the_reference(
    ) -> Result<(), StructureError> {
        let mut comparisons = 0usize;
        let mut decisions = 0usize;
        for ceiling in [3_000_000, 5_000_000, 8_000_000] {
            let config = AccountantConfig::fixed(ceiling).unwrap();
            for base_cost in [10_000, 25_000, 50_000, 75_000, 100_000] {
                for length in 1..=6 {
                    let requests = (1..=length)
                        .map(|index| {
                            CertifiedQuery::linear(
                                format!("q-{base_cost}-{index}"),
                                base_cost,
                                &config,
                            )
                            .map(|query| QueryRequest::new("scope-a", query))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let run = run_positive(&config, &requests);
                    assert!(run.account("scope-a").unwrap().reported_epsilon <= ceiling);
                    comparisons += 1;
                    decisions += length;
                }
            }
        }
        assert_eq!(comparisons, 90);
        assert_eq!(decisions, 315);
        Ok::<(), StructureError>(())
    }

    #[test]
    fn certificate_shape_and_account_local_identity_are_bound() {
        let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
        let malformed = [QueryRequest::new(
            "scope-a",
            CertifiedQuery {
                id: "wrong-width".to_string(),
                rdp_costs: vec![1],
            },
        )];
        assert!(run_workload(
            &["scope-a", "scope-b"],
            &config,
            &malformed,
            AccountantControl::Honest,
        )
        .is_err());

        let same_identity_in_distinct_accounts = [
            QueryRequest::new(
                "scope-a",
                CertifiedQuery::linear("shared-id", 25_000, &config).unwrap(),
            ),
            QueryRequest::new(
                "scope-b",
                CertifiedQuery::linear("shared-id", 25_000, &config).unwrap(),
            ),
        ];
        let run = run_positive(&config, &same_identity_in_distinct_accounts);
        assert_eq!(run.account("scope-a").unwrap().accepted_queries, 1);
        assert_eq!(run.account("scope-b").unwrap().accepted_queries, 1);
    }

    #[test]
    fn every_registered_control_is_discriminating() {
        let controls = [
            AccountantControl::ReuseQueryIdentity,
            AccountantControl::OmitOrderCharge,
            AccountantControl::DoubleOrderCharge,
            AccountantControl::DropDeltaPenalty,
            AccountantControl::OmitBestOrderCandidate,
            AccountantControl::SumPerQueryConvertedBounds,
            AccountantControl::BypassReportedBudget,
            AccountantControl::MisdirectAccount,
            AccountantControl::MutateRejectedState,
            AccountantControl::MisorderLaterCommit,
        ];
        for control in controls {
            assert!(control_is_detected(control), "control escaped: {control:?}");
        }
    }

    #[test]
    fn a_green_capacity_ledger_does_not_hide_a_wrong_conversion_premise() {
        let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
        let requests = demonstration_requests(&config).unwrap();
        let run = run_workload(
            &["scope-a", "scope-b"],
            &config,
            &requests,
            AccountantControl::DropDeltaPenalty,
        )
        .unwrap();
        assert!(run
            .accounts
            .iter()
            .all(|account| account.reported_budget.spent() <= config.epsilon_ceiling));
        assert!(verify_run(&run).is_err());
    }

    #[test]
    fn scalar_sum_of_standalone_bounds_is_conservative_but_not_claim_equivalent() {
        let config = AccountantConfig::fixed(DEFAULT_EPSILON_CEILING).unwrap();
        let requests = demonstration_requests(&config).unwrap();
        let honest = run_positive(&config, &requests);
        let scalar = run_workload(
            &["scope-a", "scope-b"],
            &config,
            &requests,
            AccountantControl::SumPerQueryConvertedBounds,
        )
        .unwrap();
        assert_eq!(honest.account("scope-a").unwrap().accepted_queries, 4);
        assert_eq!(scalar.account("scope-a").unwrap().accepted_queries, 2);
        assert!(scalar
            .accounts
            .iter()
            .all(|account| account.reported_budget.spent() <= config.epsilon_ceiling));
        assert!(verify_run(&scalar).is_err());
    }
}
