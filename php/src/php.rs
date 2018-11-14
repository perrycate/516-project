extern crate z3;

use z3::*;

fn add_pigeon_in_hole<'ctx>(
    c: &'ctx Context,
    ast: &'ctx Ast,
    vars: &'ctx [Ast],
    n: u64,
) -> Ast<'ctx> {
    let ub = vars.iter()
        .map(|var| var.le(&Ast::from_u64(c, n)))
        .collect::<Vec<_>>();
    let lb = vars.iter()
        .map(|var| var.ge(&Ast::from_u64(c, 1)))
        .collect::<Vec<_>>();
    ast.and(&ub.iter().collect::<Vec<_>>())
        .and(&lb.iter().collect::<Vec<_>>())
}

fn add_one_pigeon_only<'ctx>(
    c: &'ctx Context,
    ast: Ast<'ctx>,
    vars: &'ctx [Ast],
    n: u64,
) -> Ast<'ctx> {
    (1..=n).fold(ast, |ast, h| {
        let imps = vars.iter()
            .map(|var| {
                let imp = vars.iter()
                    .filter(|v2| var.as_u64() == v2.as_u64())
                    .map(|v2| v2._eq(&Ast::from_u64(c, h)).not())
                    .collect::<Vec<_>>();

                var._eq(&Ast::from_u64(c, h))
                    .implies(&Ast::from_bool(c, true).and(&imp.iter().collect::<Vec<_>>()))
            })
            .collect::<Vec<_>>();
        ast.and(&imps.iter().collect::<Vec<_>>())
    })
}

pub fn solve_php(n: u64) -> Option<Vec<u64>> {
    let ctx = Context::new(&Config::new());

    let vars = (0..=(n as u32))
        .map(|i| ctx.numbered_int_const(i))
        .collect::<Vec<_>>();

    let ast = Ast::from_bool(&ctx, true);
    let ast = add_pigeon_in_hole(&ctx, &ast, &vars, n);
    let ast = add_one_pigeon_only(&ctx, ast, &vars, n);

    let solver = Solver::new(&ctx);
    solver.assert(&ast);
    if solver.check() {
        let model = solver.get_model();
        Some(
            vars.iter()
                .map(|var| model.eval(var).unwrap().as_u64().unwrap())
                .collect::<Vec<_>>(),
        )
    } else {
        None
    }
}
