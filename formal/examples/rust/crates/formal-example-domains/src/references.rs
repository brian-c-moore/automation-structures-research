//! Separate result paths for the LOD and route-selection examples.
//!
//! This module imports domain data types but does not import the shared structure library. The LOD
//! reference uses direct recursive enumeration. The route reference uses Bellman-Ford relaxation.

use crate::edf::TaskSpec;
use crate::lod::{LodChoice, LodInput, LodOutput};
use crate::ospf::{OspfInput, OspfOutput, RouteEntry, VertexKind};
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet, HashSet};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct EdfReferenceResult {
    pub admission: bool,
    pub exhaustive_prefix_feasible: bool,
}

pub fn edf_admission_reference(tasks: &[TaskSpec]) -> Result<bool, String> {
    if tasks.is_empty() {
        return Err("EDF reference requires at least one task".to_string());
    }
    let mut ids = BTreeSet::new();
    let mut common_period = 1u64;
    for task in tasks {
        if task.id.is_empty()
            || !ids.insert(task.id.as_str())
            || task.wcet == 0
            || task.relative_deadline == 0
            || task.period == 0
        {
            return Err("EDF reference input is outside the task model".to_string());
        }
        let mut left = common_period;
        let mut right = task.period;
        while right != 0 {
            let remainder = left % right;
            left = right;
            right = remainder;
        }
        common_period = common_period
            .checked_div(left)
            .and_then(|value| value.checked_mul(task.period))
            .ok_or_else(|| "EDF reference period product overflow".to_string())?;
    }
    let mut repeating_demand = 0u64;
    for task in tasks {
        let charge = (common_period / task.period)
            .checked_mul(task.wcet)
            .ok_or_else(|| "EDF reference repeating charge overflow".to_string())?;
        repeating_demand = repeating_demand
            .checked_add(charge)
            .ok_or_else(|| "EDF reference repeating total overflow".to_string())?;
    }
    if repeating_demand > common_period {
        return Ok(false);
    }
    let max_deadline = tasks
        .iter()
        .map(|task| task.relative_deadline)
        .max()
        .ok_or_else(|| "EDF reference has no deadline".to_string())?;
    let bound = common_period
        .checked_add(max_deadline)
        .ok_or_else(|| "EDF reference feasibility bound overflow".to_string())?;
    for interval in 1..=bound {
        let mut demand = 0u64;
        for task in tasks {
            let charge = if interval < task.relative_deadline {
                0
            } else {
                let jobs = ((interval - task.relative_deadline) / task.period)
                    .checked_add(1)
                    .ok_or_else(|| "EDF reference job count overflow".to_string())?;
                jobs.checked_mul(task.wcet)
                    .ok_or_else(|| "EDF reference demand charge overflow".to_string())?
            };
            demand = demand
                .checked_add(charge)
                .ok_or_else(|| "EDF reference interval total overflow".to_string())?;
        }
        if demand > interval {
            return Ok(false);
        }
    }
    Ok(true)
}

#[derive(Clone, Debug)]
struct EdfReferenceJob {
    release: u64,
    deadline: u64,
    demand: u64,
}

fn edf_reference_jobs(tasks: &[TaskSpec], horizon: u64) -> Result<Vec<EdfReferenceJob>, String> {
    let mut jobs = Vec::new();
    for task in tasks {
        let mut release = 0u64;
        while release < horizon {
            let deadline = release
                .checked_add(task.relative_deadline)
                .ok_or_else(|| "EDF reference deadline overflow".to_string())?;
            if deadline <= horizon {
                jobs.push(EdfReferenceJob {
                    release,
                    deadline,
                    demand: task.wcet,
                });
            }
            release = release
                .checked_add(task.period)
                .ok_or_else(|| "EDF reference release overflow".to_string())?;
        }
    }
    Ok(jobs)
}

fn edf_exhaustive_search(
    jobs: &[EdfReferenceJob],
    time: u64,
    horizon: u64,
    remaining: Vec<u64>,
    seen: &mut HashSet<(u64, Vec<u64>)>,
) -> bool {
    if remaining
        .iter()
        .enumerate()
        .any(|(index, demand)| *demand > 0 && jobs[index].deadline <= time)
    {
        return false;
    }
    if time == horizon {
        return remaining.iter().all(|demand| *demand == 0);
    }
    if !seen.insert((time, remaining.clone())) {
        return false;
    }
    let ready: Vec<usize> = jobs
        .iter()
        .enumerate()
        .filter(|(index, job)| job.release <= time && remaining[*index] > 0)
        .map(|(index, _)| index)
        .collect();
    if ready.is_empty() {
        return edf_exhaustive_search(jobs, time + 1, horizon, remaining, seen);
    }
    for index in ready {
        let mut next = remaining.clone();
        next[index] -= 1;
        if edf_exhaustive_search(jobs, time + 1, horizon, next, seen) {
            return true;
        }
    }
    false
}

pub fn edf_exhaustive_reference(tasks: &[TaskSpec], horizon: u64) -> Result<bool, String> {
    edf_admission_reference(tasks)?;
    let jobs = edf_reference_jobs(tasks, horizon)?;
    let remaining = jobs.iter().map(|job| job.demand).collect();
    Ok(edf_exhaustive_search(
        &jobs,
        0,
        horizon,
        remaining,
        &mut HashSet::new(),
    ))
}

pub fn edf_reference_bundle(
    tasks: &[TaskSpec],
    horizon: u64,
) -> Result<EdfReferenceResult, String> {
    Ok(EdfReferenceResult {
        admission: edf_admission_reference(tasks)?,
        exhaustive_prefix_feasible: edf_exhaustive_reference(tasks, horizon)?,
    })
}

fn reference_lod_output(mut selected: Vec<LodChoice>) -> Result<LodOutput, String> {
    selected.sort();
    let total_bytes = selected.iter().try_fold(0u64, |sum, choice| {
        sum.checked_add(choice.bytes)
            .ok_or_else(|| "reference LOD byte overflow".to_string())
    })?;
    let total_utility = selected.iter().try_fold(0u64, |sum, choice| {
        sum.checked_add(choice.weighted_utility)
            .ok_or_else(|| "reference LOD utility overflow".to_string())
    })?;
    Ok(LodOutput {
        selected,
        total_bytes,
        total_utility,
    })
}

fn reference_lod_better(candidate: &LodOutput, incumbent: &LodOutput) -> bool {
    candidate.total_utility > incumbent.total_utility
        || (candidate.total_utility == incumbent.total_utility
            && (candidate.total_bytes < incumbent.total_bytes
                || (candidate.total_bytes == incumbent.total_bytes
                    && candidate.selected < incumbent.selected)))
}

fn enumerate_lod(
    input: &LodInput,
    index: usize,
    used: u64,
    selected: &mut Vec<LodChoice>,
    best: &mut Option<LodOutput>,
) -> Result<(), String> {
    if index == input.objects.len() {
        let candidate = reference_lod_output(selected.clone())?;
        if best
            .as_ref()
            .map(|incumbent| reference_lod_better(&candidate, incumbent))
            .unwrap_or(true)
        {
            *best = Some(candidate);
        }
        return Ok(());
    }
    enumerate_lod(input, index + 1, used, selected, best)?;
    let object = &input.objects[index];
    for level in &object.levels {
        let Some(next_used) = used.checked_add(level.bytes) else {
            continue;
        };
        if next_used > input.byte_budget {
            continue;
        }
        let weighted_utility = level
            .utility
            .checked_mul(object.view_weight)
            .ok_or_else(|| "reference LOD utility overflow".to_string())?;
        selected.push(LodChoice {
            object_id: object.id.clone(),
            level_id: level.id.clone(),
            bytes: level.bytes,
            weighted_utility,
        });
        enumerate_lod(input, index + 1, next_used, selected, best)?;
        selected.pop();
    }
    Ok(())
}

pub fn lod_reference(input: &LodInput) -> Result<LodOutput, String> {
    let mut best = None;
    enumerate_lod(input, 0, 0, &mut Vec::new(), &mut best)?;
    Ok(best.unwrap_or(LodOutput {
        selected: Vec::new(),
        total_bytes: 0,
        total_utility: 0,
    }))
}

pub fn lod_assembly_reference(
    scenarios: &[(&str, LodInput)],
) -> Result<Vec<(String, LodOutput)>, String> {
    let mut observed = BTreeSet::new();
    let mut outputs = Vec::new();
    for (name, input) in scenarios {
        if name.is_empty() || !observed.insert(*name) {
            return Err(
                "reference LOD assembly scenario names must be nonempty and unique".to_string(),
            );
        }
        outputs.push(((*name).to_string(), lod_reference(input)?));
    }
    outputs.sort_by(|left, right| left.0.cmp(&right.0));
    Ok(outputs)
}

fn predecessor_first_hops(
    vertex: &str,
    root: &str,
    predecessors: &BTreeMap<String, BTreeSet<String>>,
    kinds: &BTreeMap<String, VertexKind>,
    visiting: &mut BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    if !visiting.insert(vertex.to_string()) {
        return Ok(BTreeSet::new());
    }
    let mut hops = BTreeSet::new();
    for predecessor in predecessors.get(vertex).into_iter().flatten() {
        if predecessor == root {
            let kind = kinds
                .get(vertex)
                .ok_or_else(|| "reference predecessor vertex is missing".to_string())?;
            hops.insert(if *kind == VertexKind::Router {
                vertex.to_string()
            } else {
                "*".to_string()
            });
        } else {
            hops.extend(predecessor_first_hops(
                predecessor,
                root,
                predecessors,
                kinds,
                visiting,
            )?);
        }
    }
    visiting.remove(vertex);
    Ok(hops)
}

pub fn ospf_reference(input: &OspfInput) -> Result<OspfOutput, String> {
    if input.topology_version != input.expected_version {
        return Err("reference rejected stale topology".to_string());
    }
    let kinds: BTreeMap<String, VertexKind> = input
        .vertices
        .iter()
        .map(|vertex| (vertex.id.clone(), vertex.kind))
        .collect();
    if kinds.len() != input.vertices.len() || !kinds.contains_key(&input.root) {
        return Err("reference topology has invalid vertex identities".to_string());
    }
    let mut distances = BTreeMap::new();
    distances.insert(input.root.clone(), 0u64);
    for _ in 0..input.vertices.len().saturating_sub(1) {
        let mut changed = false;
        for link in &input.links {
            if !kinds.contains_key(&link.from) || !kinds.contains_key(&link.to) {
                return Err("reference link has an unknown endpoint".to_string());
            }
            let Some(from) = distances.get(&link.from).copied() else {
                continue;
            };
            let candidate = from
                .checked_add(link.cost)
                .ok_or_else(|| "reference path cost overflow".to_string())?;
            if distances
                .get(&link.to)
                .map(|current| candidate < *current)
                .unwrap_or(true)
            {
                distances.insert(link.to.clone(), candidate);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut predecessors: BTreeMap<String, BTreeSet<String>> = input
        .vertices
        .iter()
        .map(|vertex| (vertex.id.clone(), BTreeSet::new()))
        .collect();
    for link in &input.links {
        if link.to == input.root {
            continue;
        }
        let Some(from_distance) = distances.get(&link.from) else {
            continue;
        };
        let Some(to_distance) = distances.get(&link.to) else {
            continue;
        };
        if from_distance.checked_add(link.cost) == Some(*to_distance) {
            predecessors
                .get_mut(&link.to)
                .ok_or_else(|| "reference predecessor target is missing".to_string())?
                .insert(link.from.clone());
        }
    }

    let mut routes = Vec::new();
    for destination in &input.destinations {
        let Some(cost) = distances.get(destination) else {
            continue;
        };
        routes.push(RouteEntry {
            destination: destination.clone(),
            cost: *cost,
            next_hops: predecessor_first_hops(
                destination,
                &input.root,
                &predecessors,
                &kinds,
                &mut BTreeSet::new(),
            )?
            .into_iter()
            .collect(),
        });
    }
    routes.sort();
    Ok(OspfOutput { routes })
}
