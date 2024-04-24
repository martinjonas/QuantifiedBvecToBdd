#include <string>
#include <sstream>
#include <numeric>
#include <iostream>

#include "ExprSimplifier.h"
#include "EGraphs.h"
#include "Model.h"
#include "UnconstrainedVariableSimplifier.h"
#include "simplificationPasses/EqualityPropagator.h"
#include "simplificationPasses/PureLiteralEliminator.h"


#define DEBUG false

using namespace z3;

expr ExprSimplifier::Simplify(expr expression)
{
    if (DEBUG)
    {
	std::cout << std::endl << std::endl << "input:" << std::endl;
	std::cout << expression << std::endl;
    }

    expression = expression.simplify();
    expression = CanonizeBoundVariables(expression);
    expression = StripToplevelExistentials(expression);

    std::set<unsigned> seen;
    while (seen.find(expression.hash()) == seen.end())
    {
        seen.insert(expression.hash());
	if (expression.is_const())
	{
	    return expression;
	}

	clearCaches();

	expression = PushQuantifierIrrelevantSubformulas(expression);

	auto eqPropagator = std::make_unique<EqualityPropagator>(*context);
	expression = eqPropagator->Apply(expression);
	usedPasses.push_back(std::move(eqPropagator));

	expression = expression.simplify();

	auto plEliminator = std::make_unique<PureLiteralEliminator>(*context);
	expression = plEliminator->Apply(expression);
	usedPasses.push_back(std::move(plEliminator));

	for (int i = 0; i < 4; i++)
	{
	    expression = negate(expression);
	    expression = applyDer(expression);
	}

	clearCaches();

	expression = RefinedPushQuantifierIrrelevantSubformulas(expression);
	expression = applyDer(expression);

	for (int i = 0; i < 2; i++)
	{
	    expression = negate(expression);
	    expression = applyDer(expression);
	}

        expression = ReduceDivRem(expression);

	if (propagateUnconstrained && !produceModels)
	{
	    expression = expression.simplify();

	    auto unconstrainedSimplifier = std::make_unique<UnconstrainedVariableSimplifier>(*context, expression);

	    unconstrainedSimplifier->SetCountVariablesLocally(true);
	    unconstrainedSimplifier->SetDagCounting(false);
            unconstrainedSimplifier->SetGoalUnconstrained(goalUnconstrained);
	    // TODO: Refactor (martin)
	    unconstrainedSimplifier->SimplifyIte();
	    expression = unconstrainedSimplifier->GetExpr();

	    usedPasses.push_back(std::move(unconstrainedSimplifier));
	}
    }

    pushNegationsCache.clear();
    expression = expression.simplify();
    expression = PushNegations(expression);

    if (DEBUG)
    {
	std::cout << std::endl << std::endl << "nnf:" << std::endl;
	std::cout << expression << std::endl;
    }

    context->check_error();
    clearCaches();

    if (false)
    {
        z3::context ctx1;
        z3::solver s(ctx1);
        s.from_string(EGraphs::EGraph.Simplify(expression));
        expression = mk_and(s.assertions());
    }

    return expression;
}

expr ExprSimplifier::PushQuantifierIrrelevantSubformulas(const expr &e)
{
    auto item = pushIrrelevantCache.find((Z3_ast)e);
    if (item != pushIrrelevantCache.end())
    {
        return item->second;
    }

    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(PushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        expr result = dec(arguments);
        pushIrrelevantCache.insert({(Z3_ast)e, result});
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        if (e.body().is_app())
        {
            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();
                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);

                    if (!isRelevant(arg, numBound, 0))
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, numBound, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

		expr bodyExpr = innerDecl(bodyVector);
                replacementVector.push_back(modifyQuantifierBody(e, PushQuantifierIrrelevantSubformulas(bodyExpr)));

		expr result = innerDecl(replacementVector);
                pushIrrelevantCache.insert({(Z3_ast)e, result});
                return result;
            }
        }

	expr result = modifyQuantifierBody(e, PushQuantifierIrrelevantSubformulas(e.body()));
        pushIrrelevantCache.insert({(Z3_ast)e, result});

        return result;
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::RefinedPushQuantifierIrrelevantSubformulas(const expr &e)
{
    auto item = refinedPushIrrelevantCache.find((Z3_ast)e);
    if (item != refinedPushIrrelevantCache.end())
    {
        return item->second;
    }

    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(RefinedPushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        expr result = dec(arguments);
        refinedPushIrrelevantCache.insert({e, result});
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

	if (e.body().is_app())
        {
	    Z3_sort sorts [numBound];
	    Z3_symbol decl_names [numBound];
	    for (int i = 0; i < numBound; i++)
	    {
		sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
		decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
	    }

            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();

                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);

                    if (!isRelevant(arg, 1, 0))
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, 1, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

                Z3_sort outerSorts [numBound-1];
                Z3_symbol outerDecl_names [numBound-1];
                for (int i = 0; i < numBound-1; i++)
                {
                    outerSorts[i] = sorts[i];
                    outerDecl_names[i] = decl_names[i];
                }

                Z3_sort innerSorts [1];
                Z3_symbol innerDecl_names [1];
                innerSorts[0] = sorts[numBound-1];
                innerDecl_names[0] = decl_names[numBound-1];

                expr bodyExpr = innerDecl(bodyVector);
                Z3_ast innerQuantAst = Z3_mk_quantifier(
		    *context,
		    Z3_is_quantifier_forall(*context, ast),
		    Z3_get_quantifier_weight(*context, ast),
		    0,
		    {},
		    1,
		    innerSorts,
		    innerDecl_names,
		    (Z3_ast)RefinedPushQuantifierIrrelevantSubformulas(bodyExpr));

                replacementVector.push_back(to_expr(*context, innerQuantAst));
                expr outerBody = innerDecl(replacementVector);

                if (numBound == 1)
                {
                    expr result = outerBody;
                    refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else
                {
                    Z3_ast outerQuantAst = Z3_mk_quantifier(
			*context,
			Z3_is_quantifier_forall(*context, ast),
			Z3_get_quantifier_weight(*context, ast),
			0,
			{},
			numBound-1,
			outerSorts,
			outerDecl_names,
			(Z3_ast)outerBody);

                    expr result = to_expr(*context, outerQuantAst);
		    refinedPushIrrelevantCache.clear();
                    refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
                    return result;
                }
            }
        }

	expr result = modifyQuantifierBody(e, RefinedPushQuantifierIrrelevantSubformulas(e.body()));
	refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
        return result;
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::decreaseDeBruijnIndices(const expr &e, int decreaseBy, int leastIndexToDecrease)
{
    auto item = decreaseDeBruijnCache.find(std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease));
    if (item != decreaseDeBruijnCache.end())
    {
        return item->second;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        if (deBruijnIndex > leastIndexToDecrease)
        {
            return to_expr(*context, Z3_mk_bound(*context, deBruijnIndex - decreaseBy, (Z3_sort)e.get_sort()));
        }
        else
        {
            return e;
        }
    }
    else if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(decreaseDeBruijnIndices(e.arg(i), decreaseBy, leastIndexToDecrease));
        }

        expr result = dec(arguments);
        decreaseDeBruijnCache.insert({std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease), result});
        return result;

    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
        int numBound = Z3_get_quantifier_num_bound(*context, ast);

	expr result = modifyQuantifierBody(e, decreaseDeBruijnIndices(e.body(), decreaseBy, leastIndexToDecrease + numBound));
        decreaseDeBruijnCache.insert({std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease), result});
        return result;
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::negate(const expr &e)
{
    assert(e.get_sort().is_bool());

    if (e.is_quantifier())
    {
	return flipQuantifierAndModifyBody(e, negate(e.body()));
    }

    return !e;
}

expr ExprSimplifier::PushNegations(const expr &e)
{
    auto item = pushNegationsCache.find((Z3_ast)e);
    if (false && item != pushNegationsCache.end())
    {
        return item->second;
    }

    if (e.is_app())
    {
        if (e.decl().decl_kind() == Z3_OP_EQ && e.arg(0).get_sort().is_bool())
        {
            return (PushNegations(e.arg(0)) && PushNegations(e.arg(1))) ||
                (PushNegations(!e.arg(0)) && PushNegations(!e.arg(1)));
        }
        else if (e.decl().decl_kind() != Z3_OP_NOT)
        {
            func_decl dec = e.decl();
            int numArgs = e.num_args();

            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                if (e.arg(i).is_bool())
                {
                    arguments.push_back(PushNegations(e.arg(i)));
                }
                else
                {
                    arguments.push_back(e.arg(i));
                }
            }

            auto result = dec(arguments);
            pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
        else
        {
            expr notBody = e.arg(0);
            if (notBody.is_app())
            {
                func_decl innerDecl = notBody.decl();
                int numArgs = notBody.num_args();

                if (innerDecl.decl_kind() == Z3_OP_NOT)
                {
                    auto result = PushNegations(notBody.arg(0));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_AND)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_or(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_OR)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_and(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_ITE)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(!notBody.arg(2)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_IFF)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(notBody.arg(1)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_EQ && notBody.arg(0).get_sort().is_bool())
                {
                    return (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) ||
                        (PushNegations(!notBody.arg(0)) && PushNegations(notBody.arg(1)));
                }
		else if (innerDecl.decl_kind() == Z3_OP_SLEQ)
		{
		    return notBody.arg(1) < notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_SLT)
		{
		    return notBody.arg(1) <= notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULEQ)
		{
		    return to_expr(*context, Z3_mk_bvult(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULT)
		{
		    return to_expr(*context, Z3_mk_bvule(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
            }
            else if (notBody.is_quantifier())
            {

                auto result = flipQuantifierAndModifyBody(notBody, PushNegations(!notBody.body()));
                //pushNegationsCache.insert({(Z3_ast)e, result});
                return result;
            }

            auto result = e;
            //pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
    }
    if (e.is_quantifier())
    {
	expr result = modifyQuantifierBody(e, PushNegations(e.body()));
        pushNegationsCache.insert({(Z3_ast)e, result});
        return result;
    }

    auto result = e;
    pushNegationsCache.insert({(Z3_ast)e, result});
    return result;
}

expr ExprSimplifier::CanonizeBoundVariables(const expr &e)
{
    if (e.is_app() && e.get_sort().is_bool())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(CanonizeBoundVariables(e.arg(i)));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
        {
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	    decl_names[i] = Z3_mk_string_symbol(*context, std::to_string(lastBound).c_str());

	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);
	    canonizeVariableRenaming.insert({std::to_string(lastBound), current_symbol.str()});

	    lastBound++;
        }

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)CanonizeBoundVariables(e.body() && context->bool_val(true)));

	auto result = to_expr(*context, quantAst);
	return result;
    }
    else
    {
	return e;
    }
}

expr ExprSimplifier::DeCanonizeBoundVariables(const expr &e)
{
    if (e.is_app() && e.get_sort().is_bool())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(DeCanonizeBoundVariables(e.arg(i)));
        }

	expr result = dec(arguments);
	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
        {
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);

	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    decl_names[i] = Z3_mk_string_symbol(*context, (canonizeVariableRenaming[current_symbol.str()]).c_str());
        }

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)DeCanonizeBoundVariables(e.body() && context->bool_val(true)));

	auto result = to_expr(*context, quantAst);
	return result;
    }
    else
    {
	return e;
    }
}

bool ExprSimplifier::isRelevant(const expr &e, int boundVariables, int currentDepth)
{
    auto item = isRelevantCache.find(std::make_tuple((Z3_ast)e, boundVariables, currentDepth));
    if (item != isRelevantCache.end())
    {
        return item->second;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        bool result = (deBruijnIndex - currentDepth) < boundVariables;
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), result});
        return result;
    }
    else if (e.is_app())
    {
        int numArgs = e.num_args();

        for (int i = 0; i < numArgs; i++)
        {
            bool relevant = isRelevant(e.arg(i), boundVariables, currentDepth);
            if (relevant)
            {
                isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), true});
                return true;
            }
        }

        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), false});
        return false;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        bool result = isRelevant(e.body(), boundVariables, currentDepth + numBound);
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), result});
        return result;
    }
    else
    {
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), false});
        return false;
    }
}

expr ExprSimplifier::mk_or(const expr_vector &args) const
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_or(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::mk_and(const expr_vector &args) const
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_and(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::modifyQuantifierBody(const expr& quantifierExpr, const expr& newBody) const
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

expr ExprSimplifier::flipQuantifierAndModifyBody(const expr& quantifierExpr, const expr& newBody) const
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	!Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

z3::expr ExprSimplifier::applyDer(const z3::expr &expression) const
{
    z3::goal g(*context);
    g.add(expression);

    z3::tactic derTactic =
	z3::tactic(*context, "simplify") &
	z3::tactic(*context, "elim-and") &
	z3::tactic(*context, "der") &
	z3::tactic(*context, "simplify") &
	z3::tactic(*context, "distribute-forall") &
	z3::tactic(*context, "simplify");

    z3::apply_result result = derTactic(g);

    assert(result.size() == 1);
    z3::goal simplified = result[0];
    return simplified.as_expr();
}

void ExprSimplifier::clearCaches()
{
    pushIrrelevantCache.clear();
    refinedPushIrrelevantCache.clear();
    decreaseDeBruijnCache.clear();
    isRelevantCache.clear();
    reduceDivRemCache.clear();
}

z3::expr ExprSimplifier::StripToplevelExistentials(const z3::expr& e)
{
    if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
	if (!Z3_is_quantifier_forall(*context, ast))
	{
	    int numBound = Z3_get_quantifier_num_bound(*context, ast);

	    z3::expr_vector currentBound(*context);
	    for (int i = numBound - 1; i >= 0; i--)
	    {
		z3::sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
		Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
		z3::symbol current_symbol(*context, z3_symbol);

		auto name = current_symbol.str();
		if (s.is_bool())
		{
		    currentBound.push_back(context->bool_const(name.c_str()));
		}
		else if (s.is_bv())
		{
		    currentBound.push_back(context->bv_const(name.c_str(), s.bv_size()));
		}
		else
		{
		    std::cout << "Unsupported quantifier sort" << std::endl;
		    std::cout << "unknown" << std::endl;
		    abort();
		}
	    }

	    auto body = e.body();
	    return StripToplevelExistentials(body.substitute(currentBound));
	}
    } else if (e.is_app() && e.decl().decl_kind() == Z3_OP_AND) {
	const auto decl = e.decl();
        const int numArgs = e.num_args();

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
            const auto arg = e.arg(i);
	    arguments.push_back(StripToplevelExistentials(arg));
        }

	return decl(arguments);
    }

    return e;
}

bool ExprSimplifier::isSentence(const z3::expr &e)
{
    auto item = isSentenceCache.find((Z3_ast)e);
    if (item != isSentenceCache.end())
    {
	return item->second;
    }

    if (e.is_var())
    {
	return true;
    }
    else if (e.is_const() && !e.is_numeral())
    {
	std::stringstream ss;
	ss << e;
	if (ss.str() == "true" || ss.str() == "false")
	{
	    return true;
	}

	return false;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	for (unsigned int i = 0; i < num; i++)
	{
	    if (!isSentence(e.arg(i)))
	    {
		isSentenceCache.insert({(Z3_ast)e, false});
		return false;
	    }
	}

	isSentenceCache.insert({(Z3_ast)e, true});
	return true;
    }
    else if(e.is_quantifier())
    {
	return isSentence(e.body());
    }

    return true;
}

expr ExprSimplifier::ReduceDivRem(const expr &e)
{
    auto item = reduceDivRemCache.find((Z3_ast)e);
    if (item != reduceDivRemCache.end())
    {
	return item->second;
    }

    if (e.is_app())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

        int numeral = -1;
        if (e.get_sort().is_bv() && dec.decl_kind() == Z3_OP_ITE && // (ite ? ? ?)
            e.arg(0).is_app() && e.arg(0).decl().decl_kind() == Z3_OP_EQ && // (ite (= ? ?) ? ?)
            e.arg(2).is_app() && e.arg(2).num_args() == 2 && // (ite (= ? ?) ? (f ? ?))
            e.arg(0).arg(1).is_numeral_i(numeral) && numeral == 0 && // (ite (= ? 0) ? (f ? ?))
            (Z3_ast)e.arg(0).arg(0) == (Z3_ast)e.arg(2).arg(1)) // (ite (= t 0) ? (f ? t))
        {
            unsigned int bvSize = e.get_sort().bv_size();
            expr zeroes = context->bv_val(0, bvSize);
            expr ones = context->bv_val(-1, bvSize);

            if ((e.arg(2).decl().decl_kind() == Z3_OP_BUDIV ||
                 e.arg(2).decl().decl_kind() == Z3_OP_BUDIV_I) &&
                (Z3_ast)e.arg(1) == ones)
            {
                return e.arg(2); // (ite (= t 0) 11..1 (bvudiv s t t)) -> (bvudiv s t)
            }
            else if ((e.arg(2).decl().decl_kind() == Z3_OP_BUREM ||
                      e.arg(2).decl().decl_kind() == Z3_OP_BUREM_I) &&
                     (Z3_ast)e.arg(1) == (Z3_ast)e.arg(2).arg(0))
            {
                return e.arg(2); // (ite (= t 0) s (bvurem s t)) -> (bvurem s t)
            }

        }

	expr_vector arguments(*context);
	for (int i = 0; i < numArgs; i++)
        {
	    arguments.push_back(ReduceDivRem((e.arg(i))));
        }

	expr result = dec(arguments);
        reduceDivRemCache.insert({e, result});
	return result;
    }
    else if (e.is_quantifier())
    {
        return modifyQuantifierBody(e, ReduceDivRem(e.body()));
    }

    return e;
}

void ExprSimplifier::ReconstructModel(Model &model)
{
    for (auto it = usedPasses.rbegin(); it != usedPasses.rend(); ++it) {
	(*it)->ReconstructModel(model);
    }
}
