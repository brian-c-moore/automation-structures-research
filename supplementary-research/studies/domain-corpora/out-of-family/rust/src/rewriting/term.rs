//! First-order terms over a signature of function symbols and variables.
//!
//! A term is either a variable or a function symbol applied to a list of
//! argument terms; constants are the zero-argument case. Positions are
//! sequences of argument indices, the standard notation `t|_p` for the
//! subterm at `p` and `t[s]_p` for replacement.

use std::collections::BTreeMap;
use std::fmt;

/// A substitution: a finite map from variable names to terms.
pub type Subst = BTreeMap<String, Term>;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Term {
    Var(String),
    App(String, Vec<Term>),
}

impl Term {
    pub fn var(name: &str) -> Term {
        Term::Var(name.to_string())
    }

    /// A constant: a function symbol of arity zero.
    pub fn cst(name: &str) -> Term {
        Term::App(name.to_string(), Vec::new())
    }

    pub fn app(name: &str, args: Vec<Term>) -> Term {
        Term::App(name.to_string(), args)
    }

    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    /// Number of symbol occurrences (variables count as one).
    pub fn size(&self) -> usize {
        match self {
            Term::Var(_) => 1,
            Term::App(_, args) => 1 + args.iter().map(Term::size).sum::<usize>(),
        }
    }

    /// Variables in order of first (left-to-right) appearance.
    pub fn vars(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.vars_into(&mut out);
        out
    }

    pub fn vars_into(&self, out: &mut Vec<String>) {
        match self {
            Term::Var(v) => {
                if !out.iter().any(|u| u == v) {
                    out.push(v.clone());
                }
            }
            Term::App(_, args) => {
                for a in args {
                    a.vars_into(out);
                }
            }
        }
    }

    pub fn has_var(&self, x: &str) -> bool {
        match self {
            Term::Var(v) => v == x,
            Term::App(_, args) => args.iter().any(|a| a.has_var(x)),
        }
    }

    /// `self|_pos`, or `None` when the position does not exist.
    pub fn at(&self, pos: &[usize]) -> Option<&Term> {
        match pos.split_first() {
            None => Some(self),
            Some((i, rest)) => match self {
                Term::App(_, args) => args.get(*i).and_then(|a| a.at(rest)),
                Term::Var(_) => None,
            },
        }
    }

    /// `self[new]_pos`.
    pub fn replace_at(&self, pos: &[usize], new: &Term) -> Term {
        match pos.split_first() {
            None => new.clone(),
            Some((i, rest)) => match self {
                Term::App(f, args) => {
                    let mut args = args.clone();
                    args[*i] = args[*i].replace_at(rest, new);
                    Term::App(f.clone(), args)
                }
                Term::Var(_) => self.clone(),
            },
        }
    }

    /// Every position whose subterm is not a variable, outermost first.
    pub fn nonvar_positions(&self) -> Vec<Vec<usize>> {
        let mut out = Vec::new();
        let mut cur = Vec::new();
        self.collect_nonvar(&mut cur, &mut out);
        out
    }

    fn collect_nonvar(&self, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
        if let Term::App(_, args) = self {
            out.push(cur.clone());
            for (i, a) in args.iter().enumerate() {
                cur.push(i);
                a.collect_nonvar(cur, out);
                cur.pop();
            }
        }
    }

    /// Apply a substitution.
    pub fn apply(&self, s: &Subst) -> Term {
        if s.is_empty() {
            return self.clone();
        }
        match self {
            Term::Var(v) => s.get(v).cloned().unwrap_or_else(|| self.clone()),
            Term::App(f, args) => Term::App(f.clone(), args.iter().map(|a| a.apply(s)).collect()),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "{v}"),
            Term::App(g, args) if args.is_empty() => write!(f, "{g}"),
            Term::App(g, args) => {
                write!(f, "{g}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Term {
        // f(g(x), y)
        Term::app(
            "f",
            vec![Term::app("g", vec![Term::var("x")]), Term::var("y")],
        )
    }

    #[test]
    fn positions_and_replacement() {
        let t = sample();
        assert_eq!(t.at(&[0]).unwrap().to_string(), "g(x)");
        assert_eq!(t.at(&[0, 0]).unwrap().to_string(), "x");
        assert!(t.at(&[2]).is_none());
        assert_eq!(t.replace_at(&[0], &Term::cst("e")).to_string(), "f(e,y)");
        // Non-variable positions of f(g(x),y): root and 0.
        assert_eq!(t.nonvar_positions(), vec![vec![], vec![0]]);
    }

    #[test]
    fn substitution_and_vars() {
        let t = sample();
        assert_eq!(t.vars(), vec!["x".to_string(), "y".to_string()]);
        let mut s = Subst::new();
        s.insert("x".to_string(), Term::cst("e"));
        assert_eq!(t.apply(&s).to_string(), "f(g(e),y)");
        assert_eq!(t.size(), 4);
    }
}
