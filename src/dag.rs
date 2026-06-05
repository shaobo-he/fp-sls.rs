//! A hash-consed DAG representation of the scored formula.
//!
//! z3's `simplify` can emit a heavily-shared formula via `let` (e.g. `sin2.c.125`
//! is ~1.2M Sexp nodes). The Sexp preprocessing pipeline deep-clones such a tree
//! several times — hundreds of MB per clone — which OOMs. This module builds the
//! formula *once* into a compact node array, resolving `let`s into shared node
//! ids (never expanding the tree) and folding constants during construction.
//!
//! Scoring caches a [`Value`] per term node and a [`Rational`] per boolean node,
//! evaluating each node once (bottom-up: nodes are stored children-before-parents).
//! The result is identical to the recursive [`crate::score::score`] — verified by
//! the test at the bottom.

use crate::data::bitvec::BitVec;
use crate::data::fp::{rounding_mode, FloatingPoint};
use crate::data::value::{Assignment, Value};
use crate::parsing::parse::Type;
use crate::score::{score_atom, score_bool_value};
use crate::sexp::Sexp;
use rug::float::Round;
use rug::{Integer, Rational};
use std::collections::HashMap;

type Id = u32;

/// Term-level operation (mirrors the cases of `eval::eval_list`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Op {
    BvNeg,
    BvAdd,
    BvSub,
    BvMul,
    BvUdiv,
    BvUrem,
    BvNot,
    BvAnd,
    BvOr,
    FpNeg,
    FpAdd(RM),
    FpSub(RM),
    FpMul(RM),
    FpDiv(RM),
    FpSqrt(RM),
    FpIsNormal,
    FpIsSubnormal,
    FpIsZero,
    FpIsPositive,
    FpIsNaN,
    FpIsInfinite,
    ToFp(RM, u32, u32),
}

/// A `Hash`-able stand-in for `rug::float::Round`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct RM(u8);
impl RM {
    fn of(r: Round) -> RM {
        RM(match r {
            Round::Nearest => 0,
            Round::Zero => 1,
            Round::Up => 2,
            Round::Down => 3,
            _ => 4, // AwayZero
        })
    }
    fn round(self) -> Round {
        match self.0 {
            0 => Round::Nearest,
            1 => Round::Zero,
            2 => Round::Up,
            3 => Round::Down,
            _ => Round::AwayZero,
        }
    }
}

/// Binary atom kind (mirrors the scorable predicates of `score::score`).
#[derive(Clone, Copy)]
enum Atom {
    Eq,
    BvUlt,
    FpLt,
    FpLeq,
    FpGt,
    FpGeq,
    FpEq,
}
impl Atom {
    fn from_head(h: &str) -> Option<Atom> {
        Some(match h {
            "=" => Atom::Eq,
            "bvult" => Atom::BvUlt,
            "fp.lt" => Atom::FpLt,
            "fp.leq" => Atom::FpLeq,
            "fp.gt" => Atom::FpGt,
            "fp.geq" => Atom::FpGeq,
            "fp.eq" => Atom::FpEq,
            _ => return None,
        })
    }
    fn head(self) -> &'static str {
        match self {
            Atom::Eq => "=",
            Atom::BvUlt => "bvult",
            Atom::FpLt => "fp.lt",
            Atom::FpLeq => "fp.leq",
            Atom::FpGt => "fp.gt",
            Atom::FpGeq => "fp.geq",
            Atom::FpEq => "fp.eq",
        }
    }
}

enum Node {
    // ----- term nodes (produce a Value) -----
    Const(Value),
    Var(u32), // index into `vars`
    Term(Op, Vec<Id>),
    // ----- boolean nodes (produce a score) -----
    True,
    False,
    And(Vec<Id>),
    Or(Vec<Id>),
    AtomNode(Atom, bool, Id, Id), // kind, negated, term children
    BoolTerm(bool, Id),           // bare boolean term (width-1 BV), negated or not
}

pub struct Dag {
    nodes: Vec<Node>,
    roots: Vec<Id>,            // top-level asserts
    vars: Vec<String>,         // var index -> name
    assert_vars: Vec<Vec<u32>>, // per assert: the var indices it depends on (sorted)
}

/// Reusable evaluation buffers (one [`Value`] / [`Rational`] cache slot per node),
/// so the move-scoring hot loop allocates nothing per neighbor.
pub struct Scorer {
    val: Vec<Option<Value>>,
    scr: Vec<Option<Rational>>,
}

/// `let` scope: term bindings map to a shared node id; boolean bindings are kept
/// as their (already-built- id) — but because boolean lets need NNF polarity,
/// they are stored as the original Sexp and re-built at each use.
#[derive(Clone, Default)]
struct Scope {
    term: HashMap<String, Id>,
    boolean: HashMap<String, Sexp>,
}

// hash-cons key for term Op / Var nodes
#[derive(PartialEq, Eq, Hash)]
enum Key {
    Var(u32),
    Op(Op, Vec<Id>),
}

struct Builder {
    nodes: Vec<Node>,
    intern: HashMap<Key, Id>,
    vars: Vec<String>,
    var_idx: HashMap<String, u32>,
}

impl Builder {
    fn push(&mut self, n: Node) -> Id {
        let id = self.nodes.len() as Id;
        self.nodes.push(n);
        id
    }

    fn intern(&mut self, key: Key, make: Node) -> Id {
        if let Some(&id) = self.intern.get(&key) {
            return id;
        }
        let id = self.push(make);
        self.intern.insert(key, id);
        id
    }

    fn var(&mut self, name: &str) -> Id {
        let idx = match self.var_idx.get(name) {
            Some(&i) => i,
            None => {
                let i = self.vars.len() as u32;
                self.vars.push(name.to_string());
                self.var_idx.insert(name.to_string(), i);
                i
            }
        };
        self.intern(Key::Var(idx), Node::Var(idx))
    }

    fn op(&mut self, op: Op, children: Vec<Id>) -> Id {
        self.intern(Key::Op(op, children.clone()), Node::Term(op, children))
    }

    // ---------- term construction ----------

    fn build_term(&mut self, s: &Sexp, scope: &Scope) -> Id {
        match s {
            Sexp::BV(b) => self.push(Node::Const(Value::BV(b.clone()))),
            Sexp::FP(f) => self.push(Node::Const(Value::FP(f.clone()))),
            Sexp::Sym(name) => {
                if let Some(&id) = scope.term.get(name) {
                    id
                } else {
                    self.var(name)
                }
            }
            Sexp::Int(_) => panic!("bare numeral in term position: {s}"),
            Sexp::List(items) => self.build_term_list(items, scope),
        }
    }

    fn build_term_list(&mut self, items: &[Sexp], scope: &Scope) -> Id {
        // let (term-level)
        if items[0].is_sym("let") {
            let (inner, _) = self.with_lets(items, scope);
            return self.build_term(&items[2], &inner);
        }
        // constant folds (replicating transform::remove_const_bv2fp / remove_fpconst)
        if let Some(v) = fold_const(items) {
            return self.push(Node::Const(v));
        }
        // ((_ to_fp e s) rm op)
        if let Sexp::List(h) = &items[0] {
            if h.len() == 4 && h[0].is_sym("_") && h[1].is_sym("to_fp") && items.len() == 3 {
                let e = h[2].as_u32().expect("to_fp exp");
                let s = h[3].as_u32().expect("to_fp sig");
                let r = RM::of(rm(&items[1]));
                let c = self.build_term(&items[2], scope);
                return self.op(Op::ToFp(r, e, s), vec![c]);
            }
            panic!("unsupported term head: {}", items[0]);
        }
        let head = items[0].as_sym().expect("term operator");
        let child = |b: &mut Self, i: usize| b.build_term(&items[i], scope);
        let (op, kids): (Op, Vec<Id>) = match head {
            "bvneg" => (Op::BvNeg, vec![child(self, 1)]),
            "bvadd" => (Op::BvAdd, vec![child(self, 1), child(self, 2)]),
            "bvsub" => (Op::BvSub, vec![child(self, 1), child(self, 2)]),
            "bvmul" => (Op::BvMul, vec![child(self, 1), child(self, 2)]),
            "bvudiv" => (Op::BvUdiv, vec![child(self, 1), child(self, 2)]),
            "bvurem" => (Op::BvUrem, vec![child(self, 1), child(self, 2)]),
            "bvnot" => (Op::BvNot, vec![child(self, 1)]),
            "bvand" => (Op::BvAnd, vec![child(self, 1), child(self, 2)]),
            "bvor" => (Op::BvOr, vec![child(self, 1), child(self, 2)]),
            "fp.neg" => (Op::FpNeg, vec![child(self, 1)]),
            "fp.add" => (Op::FpAdd(RM::of(rm(&items[1]))), vec![child(self, 2), child(self, 3)]),
            "fp.sub" => (Op::FpSub(RM::of(rm(&items[1]))), vec![child(self, 2), child(self, 3)]),
            "fp.mul" => (Op::FpMul(RM::of(rm(&items[1]))), vec![child(self, 2), child(self, 3)]),
            "fp.div" => (Op::FpDiv(RM::of(rm(&items[1]))), vec![child(self, 2), child(self, 3)]),
            "fp.sqrt" => (Op::FpSqrt(RM::of(rm(&items[1]))), vec![child(self, 2)]),
            "fp.isNormal" => (Op::FpIsNormal, vec![child(self, 1)]),
            "fp.isSubnormal" => (Op::FpIsSubnormal, vec![child(self, 1)]),
            "fp.isZero" => (Op::FpIsZero, vec![child(self, 1)]),
            "fp.isPositive" => (Op::FpIsPositive, vec![child(self, 1)]),
            "fp.isNaN" => (Op::FpIsNaN, vec![child(self, 1)]),
            "fp.isInfinite" => (Op::FpIsInfinite, vec![child(self, 1)]),
            _ => panic!("unsupported term operation: {head}"),
        };
        self.op(op, kids)
    }

    /// Process a `(let (bindings) body)` head, returning the extended scope.
    fn with_lets(&mut self, items: &[Sexp], scope: &Scope) -> (Scope, ()) {
        let bindings = items[1].as_list().expect("let bindings");
        let mut inner = scope.clone();
        for b in bindings {
            let pair = b.as_list().expect("binding pair");
            let name = pair[0].as_sym().expect("binding name").to_string();
            if is_boolean(&pair[1], &inner) {
                inner.boolean.insert(name, pair[1].clone());
            } else {
                let id = self.build_term(&pair[1], &inner);
                inner.term.insert(name, id);
            }
        }
        (inner, ())
    }

    // ---------- boolean construction (NNF: `neg` pushed to atoms) ----------

    fn build_bool(&mut self, s: &Sexp, neg: bool, scope: &Scope) -> Id {
        match s {
            Sexp::Sym(x) if x == "⊤" => self.push(if neg { Node::False } else { Node::True }),
            Sexp::Sym(x) if x == "⊥" => self.push(if neg { Node::True } else { Node::False }),
            Sexp::Sym(name) => {
                if let Some(e) = scope.boolean.get(name).cloned() {
                    self.build_bool(&e, neg, scope)
                } else {
                    // bare boolean variable / term
                    let t = self.build_term(s, scope);
                    self.push(Node::BoolTerm(neg, t))
                }
            }
            Sexp::List(items) => self.build_bool_list(items, neg, scope),
            _ => panic!("non-boolean in formula position: {s}"),
        }
    }

    fn build_bool_list(&mut self, items: &[Sexp], neg: bool, scope: &Scope) -> Id {
        match items[0].as_sym() {
            Some("let") => {
                let (inner, _) = self.with_lets(items, scope);
                self.build_bool(&items[2], neg, &inner)
            }
            Some("¬") => self.build_bool(&items[1], !neg, scope),
            Some("∧") => {
                // effective connective: ∧ when not negated, ∨ when negated (De Morgan)
                let kids = self.build_junction(&items[1..], neg, scope);
                self.junction(!neg, kids)
            }
            Some("∨") => {
                let kids = self.build_junction(&items[1..], neg, scope);
                self.junction(neg, kids)
            }
            Some(h) if Atom::from_head(h).is_some() => {
                let kind = Atom::from_head(h).unwrap();
                let a = self.build_term(&items[1], scope);
                let b = self.build_term(&items[2], scope);
                self.push(Node::AtomNode(kind, neg, a, b))
            }
            _ => {
                // a boolean-valued term (e.g. (fp.isNormal x))
                let t = self.build_term(&Sexp::List(items.to_vec()), scope);
                self.push(Node::BoolTerm(neg, t))
            }
        }
    }

    fn build_junction(&mut self, args: &[Sexp], neg: bool, scope: &Scope) -> Vec<Id> {
        args.iter().map(|a| self.build_bool(a, neg, scope)).collect()
    }

    /// Build an `∧` (and_kind=true) or `∨` (and_kind=false) node, flattening and
    /// applying ⊤/⊥ simplification — `and_kind` is the *effective* connective
    /// after negation has been pushed in.
    fn junction(&mut self, and_kind: bool, children: Vec<Id>) -> Id {
        let mut flat: Vec<Id> = Vec::new();
        for c in children {
            match &self.nodes[c as usize] {
                Node::True if and_kind => continue,      // identity
                Node::False if !and_kind => continue,    // identity
                Node::True if !and_kind => return self.push(Node::True), // annihilator of ∨
                Node::False if and_kind => return self.push(Node::False), // annihilator of ∧
                Node::And(gs) if and_kind => flat.extend(gs.clone()),     // unnest
                Node::Or(gs) if !and_kind => flat.extend(gs.clone()),     // unnest
                _ => flat.push(c),
            }
        }
        if flat.len() == 1 {
            return flat[0];
        }
        if and_kind {
            self.push(Node::And(flat))
        } else {
            self.push(Node::Or(flat))
        }
    }
}

/// Constant folds for term lists (z3 emits these literal forms).
fn fold_const(items: &[Sexp]) -> Option<Value> {
    // (_ bvN w)
    if items.len() == 3 && items[0].is_sym("_") {
        if let Some(name) = items[1].as_sym() {
            if let Some(w) = items[2].as_u32() {
                if let Some(rest) = name.strip_prefix("bv") {
                    let n = Integer::from_str_radix(rest, 10).expect("bv numeral");
                    return Some(Value::BV(BitVec::new(w, n)));
                }
            }
        }
    }
    // (fp (_ s 1) (_ e ew) (_ sig sw))
    if items.len() == 4 && items[0].is_sym("fp") {
        if let (Sexp::List(sgn), Sexp::List(exp), Sexp::List(sig)) =
            (&items[1], &items[2], &items[3])
        {
            if is_bvconst(sgn) && is_bvconst(exp) && is_bvconst(sig) {
                let ew = exp[2].as_u32().unwrap();
                let sw = sig[2].as_u32().unwrap();
                let sv = bvval(&sgn[1]);
                let ev = bvval(&exp[1]);
                let gv = bvval(&sig[1]);
                let value = (sv << (ew + sw)) + (ev << sw) + gv;
                return Some(Value::FP(FloatingPoint::from_bitvec(
                    &BitVec::new(sw + 1 + ew, value),
                    ew,
                    sw + 1,
                )));
            }
        }
    }
    // (_ +zero ew sw) and friends
    if items.len() == 4 && items[0].is_sym("_") {
        if let (Some(tag), Some(ew), Some(sw)) =
            (items[1].as_sym(), items[2].as_u32(), items[3].as_u32())
        {
            let f = |v: f64| Some(Value::FP(FloatingPoint::real_from_f64(v, ew, sw)));
            return match tag {
                "+zero" => f(0.0),
                "-zero" => f(-0.0),
                "+oo" => f(f64::INFINITY),
                "-oo" => f(f64::NEG_INFINITY),
                "NaN" => f(f64::NAN),
                _ => None,
            };
        }
    }
    // ((_ to_fp e s) (_ bvN w))
    if items.len() == 2 {
        if let (Sexp::List(h), Sexp::List(g)) = (&items[0], &items[1]) {
            if h.len() == 4
                && h[0].is_sym("_")
                && h[1].is_sym("to_fp")
                && g.len() == 3
                && g[0].is_sym("_")
                && g[1].as_sym().is_some_and(|s| s.starts_with("bv"))
            {
                let e = h[2].as_u32().unwrap();
                let s = h[3].as_u32().unwrap();
                let w = g[2].as_u32().unwrap();
                let v = bvval(&g[1]);
                return Some(Value::FP(FloatingPoint::from_bitvec(&BitVec::new(w, v), e, s)));
            }
        }
    }
    None
}

fn is_bvconst(items: &[Sexp]) -> bool {
    items.len() == 3
        && items[0].is_sym("_")
        && items[1].as_sym().is_some_and(|s| s.starts_with("bv"))
}
fn bvval(s: &Sexp) -> Integer {
    Integer::from_str_radix(&s.as_sym().unwrap()[2..], 10).expect("bv numeral")
}

/// Does `s` denote a boolean expression (for `let` classification)? Mirrors
/// `transform::boolean_expr`, but also resolves boolean let-vars in scope.
fn is_boolean(s: &Sexp, scope: &Scope) -> bool {
    match s {
        Sexp::Sym(x) => x == "⊤" || x == "⊥" || scope.boolean.contains_key(x),
        Sexp::List(items) => match items[0].as_sym() {
            Some(op) => {
                matches!(op, "¬" | "∧" | "∨" | "let") && (op != "let")
                    || Atom::from_head(op).is_some()
                    || (op == "let" && {
                        // a let whose body is boolean
                        items.len() == 3 && is_boolean(&items[2], scope)
                    })
            }
            None => false,
        },
        _ => false,
    }
}

fn rm(s: &Sexp) -> Round {
    s.as_sym()
        .and_then(rounding_mode)
        .unwrap_or_else(|| panic!("non-constant rounding mode: {s}"))
}

impl Dag {
    /// Build the DAG from the prepared boolean formula (a conjunction of asserts,
    /// in the core connective vocabulary `∧/∨/¬` with surface ops already mapped
    /// by `transform_expr`) and the variable declarations.
    pub fn build(formula: &Sexp, var_info: &HashMap<String, Type>) -> Dag {
        let mut b = Builder {
            nodes: Vec::new(),
            intern: HashMap::new(),
            vars: Vec::new(),
            var_idx: HashMap::new(),
        };
        // Pre-register declared variables in a deterministic order so var indices
        // are stable regardless of where each first appears in the formula.
        let mut names: Vec<&String> = var_info.keys().collect();
        names.sort();
        for name in names {
            b.var(name);
        }
        let scope = Scope::default();
        // Build the whole formula, then expose the flattened top-level conjuncts
        // as the asserts — matching `get_assertions` on the unnested formula
        // (the SLS scores and selects per-assert, so the granularity must agree).
        let root = b.build_bool(formula, false, &scope);
        let roots: Vec<Id> = match &b.nodes[root as usize] {
            Node::And(ch) => ch.clone(),
            _ => vec![root],
        };
        let mut dag = Dag {
            nodes: b.nodes,
            roots,
            vars: b.vars,
            assert_vars: Vec::new(),
        };
        dag.assert_vars = dag.compute_assert_vars();
        dag
    }

    /// For each assert (root), the sorted var indices in its cone.
    fn compute_assert_vars(&self) -> Vec<Vec<u32>> {
        let mut seen = vec![false; self.nodes.len()];
        let mut visited: Vec<Id> = Vec::new();
        self.roots
            .iter()
            .map(|&r| {
                let mut vars = Vec::new();
                let mut stack = vec![r];
                visited.clear();
                while let Some(id) = stack.pop() {
                    if seen[id as usize] {
                        continue;
                    }
                    seen[id as usize] = true;
                    visited.push(id);
                    match &self.nodes[id as usize] {
                        Node::Var(idx) => vars.push(*idx),
                        Node::Const(_) | Node::True | Node::False => {}
                        Node::Term(_, ch) | Node::And(ch) | Node::Or(ch) => stack.extend(ch),
                        Node::AtomNode(_, _, a, b) => {
                            stack.push(*a);
                            stack.push(*b);
                        }
                        Node::BoolTerm(_, t) => stack.push(*t),
                    }
                }
                // reset `seen` for the nodes this assert visited, so the next
                // assert re-traverses shared subterms (otherwise it misses vars).
                for &v in &visited {
                    seen[v as usize] = false;
                }
                vars.sort_unstable();
                vars.dedup();
                vars
            })
            .collect()
    }

    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }
    pub fn vars(&self) -> &[String] {
        &self.vars
    }
    pub fn num_asserts(&self) -> usize {
        self.roots.len()
    }

    /// A fresh evaluation buffer for this DAG (reused across move scorings).
    pub fn scorer(&self) -> Scorer {
        Scorer {
            val: vec![None; self.nodes.len()],
            scr: vec![None; self.nodes.len()],
        }
    }

    /// Per-assert scores under `asn`, into the reusable `s` (allocation-free in
    /// the hot loop). Full bottom-up evaluation: each node computed once.
    pub fn eval_into(&self, c: &Rational, asn: &Assignment, s: &mut Scorer) -> Vec<Rational> {
        for id in 0..self.nodes.len() {
            self.eval_node(id, asn, c, &mut s.val, &mut s.scr);
        }
        self.roots
            .iter()
            .map(|&r| s.scr[r as usize].clone().expect("root scored"))
            .collect()
    }

    /// Per-assert scores under `asn` (convenience; allocates a throwaway buffer).
    pub fn assert_scores(&self, c: &Rational, asn: &Assignment) -> Vec<Rational> {
        let mut s = self.scorer();
        self.eval_into(c, asn, &mut s)
    }

    /// The variable names that assert `i` depends on.
    pub fn assert_var_names(&self, i: usize) -> Vec<&str> {
        self.assert_vars[i]
            .iter()
            .map(|&v| self.vars[v as usize].as_str())
            .collect()
    }

    /// `(assert (= const var))` for every variable reachable in the formula,
    /// matching `sls::get_models`.
    pub fn models(&self, asn: &Assignment) -> Vec<Sexp> {
        let mut idxs: Vec<u32> = self.assert_vars.iter().flatten().copied().collect();
        idxs.sort_unstable();
        idxs.dedup();
        let mut names: Vec<&String> = idxs.iter().map(|&i| &self.vars[i as usize]).collect();
        names.sort();
        names
            .into_iter()
            .map(|name| {
                let cst = match asn.get(name).expect("model var") {
                    Value::BV(b) => b.to_bv_const(),
                    Value::FP(f) => f.to_fp_const(),
                };
                Sexp::List(vec![
                    Sexp::sym("assert"),
                    Sexp::List(vec![Sexp::sym("="), cst, Sexp::sym(name.clone())]),
                ])
            })
            .collect()
    }

    /// Evaluate node `id`, assuming all children (lower ids) are already done.
    fn eval_node(
        &self,
        id: usize,
        asn: &Assignment,
        c: &Rational,
        val: &mut [Option<Value>],
        scr: &mut [Option<Rational>],
    ) {
        let v = |val: &[Option<Value>], i: Id| val[i as usize].clone().expect("child value");
        match &self.nodes[id] {
            Node::Const(x) => val[id] = Some(x.clone()),
            Node::Var(idx) => {
                let name = &self.vars[*idx as usize];
                val[id] = Some(asn.get(name).expect("var in assignment").clone());
            }
            Node::Term(op, ch) => {
                let r = self.apply_op(*op, ch, val);
                val[id] = Some(r);
            }
            Node::True => scr[id] = Some(Rational::from(1)),
            Node::False => scr[id] = Some(Rational::from(0)),
            Node::And(ch) => {
                if ch.is_empty() {
                    scr[id] = Some(Rational::from(1));
                } else {
                    let mut sum = Rational::from(0);
                    for &k in ch {
                        sum += scr[k as usize].as_ref().expect("and child");
                    }
                    scr[id] = Some(sum / Rational::from(ch.len() as u32));
                }
            }
            Node::Or(ch) => {
                let mut m = Rational::from(0);
                for &k in ch {
                    let s = scr[k as usize].as_ref().expect("or child");
                    if *s > m {
                        m = s.clone();
                    }
                }
                scr[id] = Some(m);
            }
            Node::AtomNode(kind, neg, a, b) => {
                scr[id] = Some(score_atom(c, kind.head(), *neg, &v(val, *a), &v(val, *b)));
            }
            Node::BoolTerm(neg, t) => {
                scr[id] = Some(score_bool_value(*neg, &v(val, *t)));
            }
        }
    }

    fn apply_op(&self, op: Op, ch: &[Id], val: &[Option<Value>]) -> Value {
        let bv = |i: usize| val[ch[i] as usize].as_ref().unwrap().as_bv();
        let fp = |i: usize| val[ch[i] as usize].as_ref().unwrap().as_fp();
        match op {
            Op::BvNeg => Value::BV(bv(0).bvneg()),
            Op::BvAdd => Value::BV(bv(0).bvadd(bv(1))),
            Op::BvSub => Value::BV(bv(0).bvsub(bv(1))),
            Op::BvMul => Value::BV(bv(0).bvmul(bv(1))),
            Op::BvUdiv => Value::BV(bv(0).bvudiv(bv(1))),
            Op::BvUrem => Value::BV(bv(0).bvurem(bv(1))),
            Op::BvNot => Value::BV(bv(0).bvnot()),
            Op::BvAnd => Value::BV(bv(0).bvand(bv(1))),
            Op::BvOr => Value::BV(bv(0).bvor(bv(1))),
            Op::FpNeg => Value::FP(fp(0).fpneg()),
            Op::FpAdd(r) => Value::FP(fp(0).fpadd(fp(1), r.round())),
            Op::FpSub(r) => Value::FP(fp(0).fpsub(fp(1), r.round())),
            Op::FpMul(r) => Value::FP(fp(0).fpmul(fp(1), r.round())),
            Op::FpDiv(r) => Value::FP(fp(0).fpdiv(fp(1), r.round())),
            Op::FpSqrt(r) => Value::FP(fp(0).fpsqrt(r.round())),
            Op::FpIsNormal => Value::BV(BitVec::from_bool(fp(0).is_normal())),
            Op::FpIsSubnormal => Value::BV(BitVec::from_bool(fp(0).is_subnormal())),
            Op::FpIsZero => Value::BV(BitVec::from_bool(fp(0).is_zero())),
            Op::FpIsPositive => Value::BV(BitVec::from_bool(fp(0).is_positive())),
            Op::FpIsNaN => Value::BV(BitVec::from_bool(fp(0).is_nan())),
            Op::FpIsInfinite => Value::BV(BitVec::from_bool(fp(0).is_infinity())),
            Op::ToFp(r, e, s) => Value::FP(fp(0).fpconv(e, s, r.round())),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parsing::parse::{get_assertions, get_formula, get_var_info, prepare_formula};
    use crate::parsing::reader::read_all;
    use crate::rng::Rng;
    use crate::score::score;
    use crate::sls::randomize_assignment;

    // Reference scores: the recursive `score()` on the fully-prepared formula —
    // exactly what the SLS uses today.
    fn check_against(dag_source: &Sexp, smt: &str, seed: u64) {
        let cmds = read_all(smt);
        let var_info = get_var_info(&cmds);
        let dag = Dag::build(dag_source, &var_info);
        let asserts = get_assertions(&prepare_formula(&cmds));
        let c = Rational::from((1, 2));
        let mut rng = Rng::from_seed(seed);
        for _ in 0..6 {
            let asn = randomize_assignment(&var_info, &mut rng);
            let dag_scores = dag.assert_scores(&c, &asn);
            let ref_scores: Vec<Rational> =
                asserts.iter().map(|a| score(&c, &asn, &[], a)).collect();
            assert_eq!(dag_scores, ref_scores, "DAG vs score() mismatch");
        }
    }

    // Build the DAG from the fully-prepared formula.
    fn check(smt: &str) {
        check_against(&prepare_formula(&read_all(smt)), smt, 7);
    }

    // Build the DAG from the *un-normalized* `get_formula` output (lets kept, not
    // NNF'd) — the integration path that lets us skip the OOM-prone passes.
    fn check_raw(smt: &str) {
        check_against(&get_formula(&read_all(smt)), smt, 11);
    }

    #[test]
    fn dag_from_raw_with_negation() {
        check_raw(
            "(declare-fun x () Float32)\n\
             (declare-fun y () Float32)\n\
             (assert (not (and (fp.lt x y) (fp.gt x y))))\n\
             (assert (or (fp.eq x y) (not (fp.leq x y))))\n\
             (assert (=> (fp.lt x y) (fp.leq x y)))\n\
             (check-sat)",
        );
    }

    #[test]
    fn dag_from_raw_with_let() {
        check_raw(
            "(declare-fun x () Float32)\n\
             (declare-fun y () Float32)\n\
             (assert (let ((s (fp.add roundNearestTiesToEven x y)))\n\
                       (let ((d (fp.sub roundTowardZero s x)))\n\
                         (fp.lt (fp.mul roundNearestTiesToEven s d) y))))\n\
             (check-sat)",
        );
    }

    #[test]
    fn dag_matches_score_fp() {
        check(
            "(declare-fun x () Float32)\n\
             (declare-fun y () Float32)\n\
             (assert (fp.lt (fp.add roundNearestTiesToEven x y) x))\n\
             (assert (fp.eq (fp.mul roundTowardZero x x) y))\n\
             (check-sat)",
        );
    }

    #[test]
    fn dag_matches_score_bv() {
        check(
            "(declare-fun a () (_ BitVec 8))\n\
             (declare-fun b () (_ BitVec 8))\n\
             (assert (bvult (bvadd a b) a))\n\
             (assert (= (bvand a b) b))\n\
             (check-sat)",
        );
    }
}
