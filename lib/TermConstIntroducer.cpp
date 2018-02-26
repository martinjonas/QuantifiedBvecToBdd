#include "TermConstIntroducer.h"
#include <string>
#include <sstream>
#include <algorithm>

using namespace z3;

bool TermConstIntroducer::isVar(expr e)
{
    if (e.is_var())
    {
        return true;
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL && !e.is_numeral())
	{
	    return true;
	}
    }

    return false;
}

z3::expr TermConstIntroducer::FlattenMul(const z3::expr &e)
{
    varsLInMul.clear();
    varsRInMul.clear();
    fillVarsInMul(e);

    auto [newExpr, mulVars] = flattenMulRec(e, {});

    for (const auto &mulVar : mulVars)
    {
	if (mulVar.op == Z3_OP_BMUL)
	{
	    newExpr = mulVar.result == mulVar.l * mulVar.r && newExpr;
	}
	else if (mulVar.op == Z3_OP_BSDIV || mulVar.op == Z3_OP_BSDIV_I)
	{
	    newExpr = mulVar.result == mulVar.l / mulVar.r && newExpr;
	}
    }

    varsLInMul.clear();
    varsRInMul.clear();

    return newExpr;
}

std::pair<z3::expr, std::set
	  <OpVar>> TermConstIntroducer::flattenMulRec(const z3::expr &e, const std::vector<Var> &boundVars)
{
    auto item = flattenMulCache.find(e);
    if (item != flattenMulCache.end() && boundVars == std::get<1>(item->second))
    {
	return {std::get<0>(item->second), std::get<2>(item->second)};
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        return {boundVars[boundVars.size() - deBruijnIndex - 1].expr, {}};
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned numArgs = e.num_args();
	auto decl_kind = f.decl_kind();

	//TODO: also BVMUL of arity > 2
	if ((decl_kind == Z3_OP_BMUL || decl_kind == Z3_OP_BSDIV || decl_kind == Z3_OP_BSDIV_I)
	    && numArgs == 2 && !e.arg(0).is_numeral() && !e.arg(1).is_numeral())
	{
  	    auto [lExpr, lNewVars] = flattenMulRec(e.arg(0), boundVars);
	    auto [rExpr, rNewVars] = flattenMulRec(e.arg(1), boundVars);

	    if (isVar(lExpr) && isVar(rExpr))
	    {
		//if bound variable, replace by a corresponding Z3 expr
		if (lExpr.is_var())
		{
		    Z3_ast ast = (Z3_ast)e.arg(0);
		    int deBruijnIndex = Z3_get_index_value(*context, ast);
		    lExpr = boundVars[boundVars.size() - deBruijnIndex - 1].expr;
		}

		//if bound variable, replace by a corresponding Z3 expr
		if (rExpr.is_var())
		{
		    Z3_ast ast = (Z3_ast)e.arg(1);
		    int deBruijnIndex = Z3_get_index_value(*context, ast);
		    rExpr = boundVars[boundVars.size() - deBruijnIndex - 1].expr;
		}

		std::stringstream newName;
		if (decl_kind == Z3_OP_BMUL)
		{
		    newName << "bvmul_" << lExpr << "_" << rExpr;
		}
		else if (decl_kind == Z3_OP_BSDIV || decl_kind == Z3_OP_BSDIV_I)
		{
		    newName << "bvsdiv_" << lExpr << "_" << rExpr;
		}

		std::set<OpVar> mulVars;
		auto newMulExpr = context->bv_const(newName.str().c_str(), e.get_sort().bv_size());

		std::set<OpVar> newVars;
		newVars.insert(lNewVars.begin(), lNewVars.end());
		newVars.insert(rNewVars.begin(), rNewVars.end());
		//add the newly created variable
		newVars.insert(OpVar(newMulExpr, decl_kind, lExpr, rExpr));

		return {newMulExpr, newVars};
	    }
	}

	std::set<OpVar> mulVars;

	expr_vector arguments(*context);
	for (uint i = 0U; i < numArgs; i++)
	{
	    auto [newExpr, newOpVars] = flattenMulRec(e.arg(i), boundVars);
	    arguments.push_back(newExpr);
	    mulVars.insert(newOpVars.begin(), newOpVars.end());
	}

	expr result = f(arguments);
	flattenMulCache.insert({(Z3_ast)e, {result, boundVars, mulVars}});
	return {result, mulVars};
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	auto newBoundVars = boundVars;

	expr_vector currentBound(*context);
	for (int i = 0; i < numBound; i++)
	{
	    sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    auto name = current_symbol.str();
	    if (s.is_bool())
	    {
		Var v(name, boundType, context->bool_const(name.c_str()));
		newBoundVars.push_back(v);
		currentBound.push_back(v.expr);
	    }
	    else if (s.is_bv())
	    {
		Var v(name, boundType, context->bv_const(name.c_str(), s.bv_size()));
		newBoundVars.push_back(v);
		currentBound.push_back(v.expr);
	    }
	    else
	    {
		std::cout << "Unsupported quantifier sort" << std::endl;
		std::cout << "unknown" << std::endl;
		abort();
	    }
	}

	auto [newBody, mulVars] = flattenMulRec(e.body(), newBoundVars);
	std::set<OpVar> quantifiedOpVars;

	for (int i = 0; i < numBound; i++)
	{
	    sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    if (s.is_bv())
	    {
		auto v = context->bv_const(current_symbol.str().c_str(), s.bv_size());
		std::copy_if(mulVars.begin(),
			     mulVars.end(),
			     std::inserter(quantifiedOpVars, quantifiedOpVars.end()),
			     [=] (auto mulVar)
			     {
				 return v.to_string() == mulVar.l.to_string() ||
				     v.to_string() == mulVar.r.to_string();

			     });

		//TODO: Do not traverse twice
		std::set<OpVar> newOpVars;
		std::copy_if(mulVars.begin(),
			     mulVars.end(),
			     std::inserter(quantifiedOpVars, quantifiedOpVars.end()),
			     [=] (auto mulVar)
			     {
				 return v.to_string() != mulVar.l.to_string() &&
				     v.to_string() != mulVar.r.to_string();

			     });
		mulVars = newOpVars;
	    }
	}

	//TODO: Add congruences also for bvsdiv
	for (const auto &mulVar : quantifiedOpVars)
	{
	    if (mulVar.op == Z3_OP_BMUL)
	    {
		newBody = mulVar.result == mulVar.l * mulVar.r && newBody;

		for (const auto &v1 : varsLInMul)
		{
		    for (const auto &v2 : varsRInMul)
		    {
			std::stringstream newName;
			newName << "bvmul_" << v1 << "_" << v2;

			auto equivOp = context->bv_const(newName.str().c_str(),
							 mulVar.result.get_sort().bv_size());

			newBody = newBody &&
			    implies(v1 == mulVar.l && v2 == mulVar.r,
				    mulVar.result == equivOp);
		    }
		}

		newBody = exists(mulVar.result, newBody.simplify());
	    }
	    else if (mulVar.op == Z3_OP_BSDIV || mulVar.op == Z3_OP_BSDIV_I)
	    {
		newBody = mulVar.result == mulVar.l / mulVar.r && newBody;
	    }
	}

	if (boundType == UNIVERSAL)
	{
	    return {forall(currentBound, newBody), mulVars};
	}
	else
	{
	    return {exists(currentBound, newBody), mulVars};
	}
    }

    std::cout << "FlattenMul: unsupported expression" << std::endl;
    std::cout << "unknown" << std::endl;
    abort();
}

bool operator < (OpVar const& lhs, OpVar const& rhs)
{
    return lhs.result.to_string() < rhs.result.to_string();
}

bool operator == (OpVar const& lhs, OpVar const& rhs)
{
    return lhs.result.to_string() == rhs.result.to_string();
}

void TermConstIntroducer::fillVarsInMul(const z3::expr &e)
{
    auto item = fillVarsCache.find((Z3_ast)e);
    if (item != fillVarsCache.end())
    {
	return;
    }

    fillVarsCache.insert((Z3_ast)e);

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned numArgs = e.num_args();
	auto decl_kind = f.decl_kind();

	//TODO: also BVMUL of arity > 2
	if (decl_kind == Z3_OP_BMUL && numArgs == 2 && isVar(e.arg(0)) && isVar(e.arg(1)))
	{
	    if (!e.arg(0).is_var())
	    {
		varsLInMul.insert(e.arg(0));
	    }

	    if (!e.arg(1).is_var())
	    {
		varsRInMul.insert(e.arg(1));
	    }
	}
	else
	{
	    for (uint i = 0U; i < numArgs; i++)
	    {
		fillVarsInMul(e.arg(i));
	    }
	}
    }
    else if (e.is_quantifier())
    {
	fillVarsInMul(e.body());
    }
}
