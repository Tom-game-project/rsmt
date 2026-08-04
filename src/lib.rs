use std::{collections::VecDeque, option::Iter, vec};

#[derive(Clone, Copy, Debug)]
struct PredId(usize);

#[derive(Clone, Debug)]
enum Expr {
    Pred(PredId),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
}

impl Expr {
    fn to_string(&self, pred_list: &[String]) -> String {
        match self {
            Expr::Pred(predid) => {
                format!("{}", pred_list[predid.0])
            }
            Expr::Not(expr) => {
                format!("¬ ({})", (*expr).to_string(pred_list))
            }
            Expr::Or(l, r) => {
                format!("({} ∨ {})", (*l).to_string(pred_list), (*r).to_string(pred_list))
            }
            Expr::And(l, r) => {
                format!("({} ∧ {})", (*l).to_string(pred_list), (*r).to_string(pred_list))
            }
        }
    }
}

struct ExprState {
    pre: Vec<Expr>,
    res: Expr
}

fn not(expr: Expr) -> Expr {
    Expr::Not(Box::new(expr))
}

fn implies(l: Expr, r: Expr) -> Expr {
    Expr::Or(Box::new(Expr::Not(Box::new(l))), Box::new(r))
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct ExprId(usize);

#[derive(Clone, Debug)]
enum Branch {
    Fork{expr_id: ExprId, cont: bool, l: Box<Branch>, r: Box<Branch>},
    Child{expr_id: ExprId, cont: bool, c: Option<Box<Branch>>}
}

impl Branch {

    /// ```
    /// br.add_branch(expr_id, branch, false);
    /// ```
    fn add_branch(&mut self, expr_id: ExprId, branch: Branch, under_expr: bool) {
        match self {
            Branch::Fork { expr_id: child_expr_id , cont, l, r} => {
                l.add_branch(expr_id, branch.clone(), *child_expr_id == expr_id || under_expr);
                r.add_branch(expr_id, branch, *child_expr_id == expr_id || under_expr);
            }
            Branch::Child { expr_id: child_expr_id, cont, c } => {
                if let Some(parent_branch) = c {
                    parent_branch.add_branch(expr_id, branch, *child_expr_id == expr_id || under_expr);
                } else {
                    if (*child_expr_id == expr_id || under_expr) && !*cont {
                        let mut new_branch = branch;
                        new_branch.set_expr_id(*child_expr_id);
                        *self = new_branch;
                    }
                } 
            }
        }
    }

    fn set_expr_id(&mut self, new_expr_id: ExprId) {
        match self {
            Branch::Fork { expr_id, .. } => {
                *expr_id = new_expr_id;
            }
            Branch::Child { expr_id, .. } => {
                *expr_id = new_expr_id;
            }
        }
    }

    fn get_expr_id(&self) -> ExprId {
        match self {
            Branch::Fork { expr_id, .. } => {
                *expr_id
            }
            Branch::Child { expr_id, .. } => {
                *expr_id
            }
        }
    }

    fn find_closd_branch<'a>(
        &'a self,
        expr_id_list: &mut Vec<ExprId>,
        expr_list: &[Expr]
    ) {
        match self {
            Branch::Fork { expr_id, cont, l, r } => {
                expr_id_list.push(*expr_id);
                l.find_closd_branch(expr_id_list, expr_list);
                r.find_closd_branch(expr_id_list, expr_list);
                expr_id_list.pop();
            }
            Branch::Child { expr_id, cont, c } => {
                if let Some(branch) = c {
                    expr_id_list.push(*expr_id);
                    branch.find_closd_branch(expr_id_list, expr_list);
                    expr_id_list.pop();
                } else {
                    expr_id_list.push(*expr_id);
                    for i in expr_id_list.into_iter() {
                        print!("{:?}", i);
                    }
                    expr_id_list.pop();
                    println!("");
                }
            }
        }
    }

    fn get_dep_dot(&self) -> Vec<String> {
        let mut rlist = Vec::new();
        match self {
            Branch::Fork { expr_id, cont, l, r } => {
                rlist.push(format!("{} -> {} [ ]", expr_id.0, l.get_expr_id().0));
                rlist.push(format!("{} -> {} [ ]", expr_id.0, r.get_expr_id().0));
                rlist.append(&mut l.get_dep_dot());
                rlist.append(&mut r.get_dep_dot());
            }
            Branch::Child { expr_id, cont, c } => {
                if let Some(branch) = c {
                    rlist.push(format!("{} -> {} [ ]", expr_id.0, branch.get_expr_id().0));
                    rlist.append(&mut branch.get_dep_dot());
                }
            }
        }
        rlist
    }

    pub fn dot(&self, expr_list: &[Expr], pred_list: &[String]) -> String {
        let nodes = expr_list.iter().enumerate().map(|(i, a)| format!("{} [label =\"{}\"]", i, a.to_string(pred_list))).collect::<Vec<String>>().join("\n");
        format!("
digraph {{
{}
{}
}}
        ", nodes, self.get_dep_dot().join("\n"))
    }
}

pub struct tableau {
    pub expr_list: Vec<Expr>,
}

fn gen_branch_from_vec(expr_id: ExprId, expr_list: &[Expr]) -> Option<Box<Branch>> {
    if expr_id.0 < expr_list.len() {
        let succ_id = ExprId(expr_id.0 + 1);
        Some(
            Box::new(Branch::Child { expr_id, cont: false, c: gen_branch_from_vec(succ_id, expr_list) })
        )
    } else {
        None
    }
}

impl tableau {

    pub fn new (pre: Vec<Expr>, res: Expr) -> Self {
        let mut expr_list = pre;
        expr_list.push(res);
        Self {
            expr_list,
        }
    }

    fn push(&mut self, expr: Expr) -> ExprId {
        let l = self.expr_list.len();
        self.expr_list.push(expr);
        ExprId(l)
    }

    pub fn resolve(&mut self) -> Option<Box<Branch>> {
        if let Some(mut init_branch) = gen_branch_from_vec(ExprId(0), &self.expr_list) {
            let mut stack: VecDeque<ExprId> = self.expr_list.iter().enumerate().map(|(i, _j)| ExprId(i)).collect();

            println!("{:#?}", init_branch);
            while let Some(expr_id) = stack.pop_front() {
                if let Some((branch, new_expr_id_list)) = self.gen_branch(expr_id) {
                    init_branch.add_branch(expr_id, branch, false);
                    for i in new_expr_id_list {
                        println!("expr id: {:?}", i);
                        stack.push_back(i);
                    }
                    println!("{:#?}", init_branch);
                }
            }
            Some(init_branch)
        } else {
            // Error
            println!("error occured");
            None
        }
    }

    pub fn gen_branch(&mut self, expr_id: ExprId) -> Option<(Branch, Vec<ExprId>)> {
        let expr = self.expr_list[expr_id.0].clone();

        match expr {
            Expr::Not(x) => {
                match *x {

                    Expr::Not(x) => { 
                        let child_expr_id = self.push(*x);
                        Some((Branch::Child { expr_id: child_expr_id, cont: false, c: None }, vec![child_expr_id]))
                    }

                    Expr::Pred(_pred) => {
                        None
                    }

                    Expr::Or(l, r) => {
                        let l_expr_id = self.push(not(*l));
                        let r_expr_id = self.push(not(*r));
                        Some((Branch::Child {expr_id, cont: false , c: Some(Box::new( Branch::Child { expr_id: l_expr_id, cont: false, c: Some(Box::new(Branch::Child { expr_id: r_expr_id, cont: false , c: None })) }))}, vec![l_expr_id, r_expr_id]))
                    }

                    Expr::And(l, r) => {
                        let l_expr_id = self.push(not(*l));
                        let r_expr_id = self.push(not(*r));
                        Some((
                            Branch::Fork { 
                                expr_id, 
                                cont: false,
                                l: Box::new(Branch::Child { expr_id: l_expr_id, cont: false , c: None }), 
                                r: Box::new(Branch::Child { expr_id: r_expr_id, cont: false , c: None }),
                            },
                            vec![l_expr_id, r_expr_id]
                        ))
                    }
                }
            }

            Expr::Or(l, r) => {
                let l_expr_id = self.push(*l);
                let r_expr_id = self.push(*r);
                Some((
                    Branch::Fork { 
                        expr_id, 
                        cont: false,
                        l: Box::new(Branch::Child { expr_id: l_expr_id, cont: false, c: None }), 
                        r: Box::new(Branch::Child { expr_id: r_expr_id, cont: false, c: None }),
                    },
                    vec![l_expr_id, r_expr_id]
                ))
            }

            Expr::And(l, r) => {
                let l_expr_id = self.push(*l);
                let r_expr_id = self.push(*r);
                Some((Branch::Child {expr_id, cont: false , c: Some(Box::new( Branch::Child { expr_id: l_expr_id, cont:false , c: Some(Box::new(Branch::Child { expr_id: r_expr_id, cont:false , c: None })) }))}, vec![l_expr_id, r_expr_id]))
            }

            Expr::Pred(_pred) => {
                None
            }
        }
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    fn f<'a>(iter: impl Iterator<Item = &'a ExprId> + Clone) {
        let next_iter = iter.clone().chain(std::iter::once(&ExprId(4)));

        g(next_iter);

        println!("----------------");
        for i in iter {
            println!("{:?}", i);
        }
    }

    fn g<'a>(iter: impl Iterator<Item = &'a ExprId> + Clone) {
        for i in iter {
            println!("{:?}", i);
        }
    }

    #[test]
    fn it_works00() {
        f(vec![ExprId(0), ExprId(1), ExprId(2), ExprId(3)].iter());
    }

    #[test]
    fn it_works01() {
        let pred_a = Box::new(Expr::Pred(PredId(0)));
        let pred_b = Box::new(Expr::Pred(PredId(1)));
        let mut t = tableau::new(
            Vec::new(),
            not(
                implies(*pred_a.clone(), Expr::And(pred_a.clone(), Box::new(Expr::Or(pred_a, pred_b))))
            )
        );

        if let Some(b) = t.gen_branch(ExprId(0)) {
            println!("branch {:#?}", b);
        } else {
            println!("Nothing");
        }
        println!("{:#?}", t.expr_list);
    }

    #[test]
    fn it_works02() {
        let pred_a = Box::new(Expr::Pred(PredId(0)));
        let pred_b = Box::new(Expr::Pred(PredId(1)));
        let pred_c = Box::new(Expr::Pred(PredId(2)));

        let expr_pre = implies(Expr::And(pred_a.clone(), pred_b.clone()), *pred_c.clone());
        let expr_res = implies(*pred_a, Expr::Or(Box::new(not(*pred_b)), pred_c));

        let mut t = tableau::new(vec![expr_pre], not(expr_res));

        if let Some(b) = t.gen_branch(ExprId(0)) {
            println!("branch {:#?}", b);
        } else {
            println!("Nothing");
        }
        if let Some(b) = t.gen_branch(ExprId(1)) {
            println!("branch {:#?}", b);
        } else {
            println!("Nothing");
        }

        let pred_list = vec![
            "A".to_string(),
            "B".to_string(),
            "C".to_string(),
        ];

        for (i, expr) in t.expr_list.iter().enumerate() {
            println!("{}: {}", i, expr.to_string(&pred_list));
        }
    }

    #[test]
    fn it_works03() {
        let pred_a = Box::new(Expr::Pred(PredId(0)));
        let pred_b = Box::new(Expr::Pred(PredId(1)));
        let mut t = tableau::new(
            vec![],
            not(
                implies(*pred_a.clone(), Expr::And(pred_a.clone(), Box::new(Expr::Or(pred_a, pred_b))))
            )
        );

        let pred_list = vec![
            "A".to_string(),
            "B".to_string(),
        ];

        if let Some(branch) = t.resolve() {
            println!("{:#?}", branch);
            println!("start");
            branch.find_closd_branch(&mut vec![], &t.expr_list);
            println!("{}", branch.dot(&t.expr_list, &pred_list));
            println!("end");
        } else {
            println!("expression not set");
        }

        for (i, expr) in t.expr_list.iter().enumerate() {
            println!("{}: {}", i, expr.to_string(&pred_list));
        }

        
    }
}
