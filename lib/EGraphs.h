#ifndef EGraphs_h
#define EGraphs_h

#include <vector>
#include <set>
#include <map>
#include <sstream>
#include <z3++.h>


namespace EGraphs
{
	class Function
	{
		std::vector<Function*>* UsedBy;
		Function* Parent;
		std::vector<Function*>* Inputs;
		z3::expr* Value;

	public: Function(std::vector<Function*>* inputs, z3::expr* value)
	{
		this->UsedBy = new std::vector<Function*>();
		this->Parent = this;
		this->Inputs = inputs;
		this->Value = value;
		for (Function* func : *inputs)
		{
			func->UsedBy->push_back(this);
		}
	}

		  void ManualDestroy()
		  {
			  if (this->UsedBy->empty())
			  {
				  for (Function* func : *this->Inputs)
				  {
					  func->UsedBy->erase(std::remove(func->UsedBy->begin(), func->UsedBy->end(), this), func->UsedBy->end());
				  }
				  delete this->UsedBy;
				  delete this->Inputs;
				  delete this;
			  }
		  }

		  ~Function()
		  {
			  /*if (this->UsedBy->empty())
			  {
				  for (Function* func : *this->Inputs)
				  {
					  func->Inputs->erase(std::remove(func->Inputs->begin(), func->Inputs->end(), this), func->Inputs->end());
				  }
				  delete this->UsedBy;
				  delete this->Inputs;
			  }*/
		  }

	public:
		z3::expr* GetValue()
		{
			return this->Value;
		}

		unsigned getName()
		{
			return this->Value->decl().id();
		}

		Function* GetRoot()
		{
			if (this->Parent == this)
			{
				return this;
			}
			Function* root = this->Parent->GetRoot();
			this->Parent = root;
			return root;
		}

		bool operator==(const Function& other) const
		{
			if (this->Inputs->size() != other.Inputs->size() || this->getName() != other.getName())
			{
				return false;
			}
			for (size_t i = 0; i < this->Inputs->size(); i++)
			{
				if (!(*(*(this->Inputs))[i] == *(*(other.Inputs))[i]))
				{
					return false;
				}
			}
			return true;
		}

		bool operator!=(const Function& other) const
		{
			return !(*this == other);
		}

		bool IsEquivalent(Function* other)
		{
			if (this->GetRoot() == other->GetRoot())
			{
				return true;
			}
			return this->IsCongruent(other);
		}

		bool IsCongruent(Function* other)
		{
			if (this->getName() != other->getName())
			{
				return false;
			}
			for (size_t i = 0; i < this->Inputs->size(); i++)
			{
				if ((*this->Inputs)[i]->GetRoot() != (*other->Inputs)[i]->GetRoot())
				{
					return false;
				}
			}
			return true;
		}
	};

	bool TryGetRealFunction(Function* function, std::map<unsigned, std::vector<Function*>*> functions, Function** outFunction)
	{
		if (functions.find(function->getName()) == functions.end())
		{
			return false;
		}
		for (Function* realFunction : *functions[function->getName()])
		{
			if (*realFunction == *function)
			{
				*outFunction = realFunction;
				return true;
			}
		}
		return false;
	}

	class EGraph
	{

		std::map<unsigned, std::vector<Function*>*> _functions;
		std::map<Function*, std::vector<Function*>*> _class;
		std::vector<Function*> _in_equalities;
		std::set<Function*> _quantified_variables;
		z3::context* ctx;

	public: EGraph(z3::context* ctx)
		{
			this->_quantified_variables = std::set<Function*>();
			this->_functions = std::map<unsigned, std::vector<Function*>*>{};
			this->_in_equalities = std::vector<Function*>();
			this->_class = std::map<Function*, std::vector<Function*>*>();
			this->ctx = ctx;
		}

		~EGraph()
		{
			for (auto it = this->_functions.begin(); it != this->_functions.end(); it++)
			{
				for (Function* f : *it->second)
				{
					delete f->Inputs;
					delete f->UsedBy;
					delete f;
				}
				delete it->second;
			}
			for (auto it = this->_class.begin(); it != this->_class.end(); it++)
			{
				delete it->second;
			}
		}

		std::map<Function*, std::vector<Function*>*> GetClasses()
		{
			return _class;
		}

		static EGraph* ExprToEGraph(z3::expr* expr, z3::context* ctx)
		{
		    EGraph* graph = new EGraph(ctx);
		    graph->ParseAnd(expr);
		    
		    return graph;
		}

		void ParseAnd(z3::expr* expr)
		{
		    for (z3::expr e: expr->args())
		    {
		        if (e.is_and())
		        {
		            this->ParseAnd(&e);
		            continue;
		        }
		        if (e.is_eq())
		        {
		            this->ParseEq(&e);
		            continue;
		        }
		        this->ParsePredicate(&e);
		    }
		}

		void ParseEq(z3::expr* expr)
		{
			std::vector<Function*> vec = std::vector<Function*>();
			for (z3::expr arg : expr->args())
			{
				vec.push_back(this->ParseOther(&arg));
			}
		    this->AddEquality(vec[0], vec[1], expr);
		}

		// this shouldn't be used normally as Q3B deals with bitvectors, which shouldn't have predicates applied to them
		void ParsePredicate(z3::expr* expr)
		{
			std::vector<Function*>* arguments = new std::vector<Function*>();
			for (z3::expr arg : expr->args())
			{
				arguments->push_back(ParseOther(&arg));
			}
			AddPredicate(arguments, expr->decl().id(), expr);
		}

		Function* ParseOther(z3::expr* expr)
		{
		    if (!expr->is_const())
		    {
				// it's a function with >0 arguments
				std::vector<Function*>* arguments = new std::vector<Function*>();
				for (z3::expr arg : expr->args())
				{
					arguments->push_back(ParseOther(&arg));
				}
                unsigned name = expr->decl().id();
				return AddFunction(arguments, name, expr);
		    }
		    if (expr->to_string() == expr->decl().name().str())
		    {
				// it's a quantified variable
				return AddQuantifiedVariable(expr->decl().id(), expr);
		    }
			// it's a number, so not quantified
			return AddTerm(expr->delc().id(), expr);
		}

		static z3::expr Simplify(z3::expr* expr, z3::context* ctx)
		{
			if (!expr->is_and())
			{
				return *expr;
			}
		    EGraph* graph = ExprToEGraph(expr, ctx);
		    auto repr = graph->FindDefs();
		    repr = graph->RefineDefs(repr);
		    auto core = graph->FindCore(repr);
            z3::expr res = graph->ToExprString(repr, core);

		    delete graph;
		    delete repr;
		    delete core;
		    return res;
		}

		z3::expr ToExprString(std::map<Function*, Function*>* repr, std::set<Function*>* core)
		{
			z3::expr_vector arguments(*this->ctx);
			for (Function* in_equality : _in_equalities)
			{
				arguments.push_back(NodeToTerm(in_equality, repr));
			}
			for (auto elem : *repr)
			{
				if (elem.first != elem.second)
				{
					continue;
				}
				z3::expr term = NodeToTerm(elem.second, repr);
				for (Function* InSameClass : *_class[elem.second->GetRoot()])
				{
					if (InSameClass == elem.second || core->count(InSameClass) == 0)
					{
						continue;
					}
					arguments.push_back(term == NodeToTerm(InSameClass, repr));
				}
			}
			return mk_and(arguments);
		}

		z3::expr NodeToTerm(Function* node, std::map<Function*, Function*>* repr)
		{
			if (node->Inputs->size() == 0)
			{
				return *node->GetValue();
			}
			z3::expr_vector arguments(*this->ctx);
			for (Function* arg : *node->Inputs)
			{
				arguments.push_back(NodeToTerm((*repr)[arg], repr));
			}
			return (node->GetValue()->decl())(arguments);
		}

		void MakeEqual(Function* first, Function* second)
		{
			if (first->GetRoot() == second->GetRoot())
			{
				return;
			}
			Function* root = second->GetRoot();
			root->Parent = first->GetRoot();
			// concat
			this->_class[first->GetRoot()]->insert(this->_class[first->GetRoot()]->end(), this->_class[root]->begin(), this->_class[root]->end());
			delete this->_class[root];
			this->_class.erase(root);
		}

		Function* AddQuantifiedVariable(unsigned name, z3::expr* value)
		{
			Function* term = AddTerm(name, value);
			_quantified_variables.insert(term);
			return term;
		}

		Function* AddTerm(unsigned name, z3::expr* value)
		{
			if (this->_functions.find(name) == this->_functions.end())
			{
				Function* term = new Function(new std::vector<Function*>{}, value);
				this->_functions[name] = new std::vector<Function*>{ term }; // if term didn't exist, make it
				this->_class[this->_functions[name]->at(0)] = new std::vector<Function*>{ term };
			}
			return this->_functions[name]->at(0);
		}

		Function* AddFunction(std::vector<Function*>* inputs, unsigned name, z3::expr* value)
		{
			if (this->_functions.find(name) == this->_functions.end())
			{
				Function* func = new Function(inputs, value);
				this->_functions[name] = new std::vector<Function*>{ func }; // if function didn't exist, make it
				this->_class[this->_functions[name]->at(0)] = new std::vector<Function*>{ func };
				return this->_functions[name]->at(0);
			}
			Function* temporary = new Function(inputs, value);
			for (Function* func : *this->_functions[name])
			{
				if (*temporary == *func)
				{
					temporary->ManualDestroy();
					return func;
				}
			}
			this->_functions[name]->push_back(temporary);
			this->_class[this->_functions[name]->back()] = new std::vector<Function*>{ temporary };
			CheckEqualities(temporary);
			return temporary;
		}

		void CheckEqualities(Function* func)
		{
			for (size_t i = 0; i < this->_functions[func->getName()]->size() - 1; i++)
			{
				if (func->IsEquivalent((*this->_functions[func->getName()])[i]))
				{
					MakeEqual(func, (*this->_functions[func->getName()])[i]);
				}
			}
		}

		void AddEquality(Function* first, Function* second, z3::expr* value)
		{
			Function* realFirst = first;
			if (TryGetRealFunction(first, this->_functions, &realFirst))
			{
				if (first != realFirst)
				{
					first->ManualDestroy();
				}
			}

			Function* realSecond = second;
			if (TryGetRealFunction(second, this->_functions, &realSecond))
			{
				if (second != realSecond)
				{
					second->ManualDestroy();
				}
			}
			std::vector<Function*>* equality = new std::vector<Function*>{ realFirst, realSecond };
			Function* eq = this->AddFunction(equality, value);
			this->_in_equalities.push_back(eq);

			MakeEqual(realFirst, realSecond);
			for (Function* func : *realFirst->UsedBy)
			{
				CheckEqualities(func);
			}
			for (Function* func : *realSecond->UsedBy)
			{
				CheckEqualities(func);
			}
		}

		std::set<Function*>* FindCore(std::map<Function*, Function*>* repr)
		{
			std::set<Function*>* core = new std::set<Function*>();
			for (auto elem : *repr)
			{
				if (elem.first != elem.second)
				{
					continue;
				}
				core->insert(elem.second);
				for (Function* func : *_class[elem.second->GetRoot()])
				{
					if (func == elem.second || _quantified_variables.count(func) != 0)
					{
						continue;
					}

					bool equivalentFound = false;
					for (Function* InCore : *core)
					{
						if (InCore->IsCongruent(func))
						{
							equivalentFound = true;
							break;
						}
					}

					if (!equivalentFound)
					{
						core->insert(func);
					}
				}
			}
			return core;
		}

		bool IsGround(Function* function)
		{
			// this happens when the function is a Term
			if (function->Inputs->size() == 0)
			{
				for (Function* variable : _quantified_variables)
				{
					// when function is found in the list of quantified variables, return false
					if (*variable == *function)
					{
						return false;
					}
				}
				return true;
			}
			// when it is not a Term, check all its inputs
			for (Function* input : *function->Inputs)
			{
				// if at least one is not ground, return false
				if (!IsGround(input))
				{
					return false;
				}
			}
			return true;
		}

		std::map<Function*, Function*>* FindDefs()
		{
			// Initialize representative function
			std::map<Function*, Function*>* repr = new std::map<Function*, Function*>();
			std::vector<Function*> groundTerms = std::vector<Function*>();

			// process every ground term
			for (auto pair = _functions.begin(); pair != _functions.end(); pair++)
			{
				for (Function* function : *pair->second)
				{
					if (IsGround(function) && function->Inputs->size() == 0)
					{
						groundTerms.push_back(function);
					}
				}
			}
			repr = AssignRepresentatives(repr, groundTerms);

			// process leftover terms
			std::vector<Function*> leftoverTerms = std::vector<Function*>();
			for (auto pair = _functions.begin(); pair != _functions.end(); pair++)
			{
				for (Function* function : *pair->second)
				{
					if (function->Inputs->size() == 0)
					{
						leftoverTerms.push_back(function);
					}
				}
			}
			repr = AssignRepresentatives(repr, leftoverTerms);

			return repr;
		}

		std::map<Function*, Function*>* AssignRepresentatives(std::map<Function*, Function*>* repr, std::vector<Function*> toBeAssigned)
		{
			// iterate through functions and terms while possible
			for (size_t i = 0; i < toBeAssigned.size(); i++)
			{
				Function* function = toBeAssigned[i];
				// if they have a representative, skip
				if (repr->find(function) != repr->end())
				{
					continue;
				}
				for (Function* func : *_class[function->GetRoot()])
				{
					// set the representative of everything equivalent to self
					(*repr)[func] = function;
					for (Function* parent : *func->UsedBy)
					{
						bool isGround = true;
						// check if parent became ground term
						for (Function* child : *parent->Inputs)
						{
							if (repr->find(child) == repr->end())
							{
								isGround = false;
								break;
							}
						}
						// assign it later if yes
						if (isGround)
						{
							toBeAssigned.push_back(parent);
						}
					}
				}
			}
			return repr;
		}

		bool MakesCycle(Function* NewGround, std::map<Function*, Function*>* repr)
		{
			std::map<Function*, bool>* ColoredGraph = new std::map<Function*, bool>();

			// initialize false as the value for every node of EGraph at the start
			std::map<unsigned, std::vector<Function*>*>::iterator it;
			for (it = this->_functions.begin(); it != this->_functions.end(); it++)
			{
				for (Function* func : *it->second)
				{
					(*ColoredGraph)[func] = false;
				}
			}

			for (Function* descendant : *NewGround->Inputs)
			{
				if (MakesCycleAux(NewGround, repr, descendant, ColoredGraph))
				{
					delete ColoredGraph;
					return true;
				}
			}
			delete ColoredGraph;

			return false;
		}

		bool MakesCycleAux(Function* NewGround, std::map<Function*, Function*>* repr, Function* current, std::map<Function*, bool>* ColoredGraph)
		{
			if (current->GetRoot() == NewGround->GetRoot())
			{
				return true;
			}
			current = (*repr)[current];
			for (Function* descendant : *current->Inputs)
			{
				if ((*ColoredGraph)[current])
				{
					continue;
				}

				if (MakesCycleAux(NewGround, repr, descendant, ColoredGraph))
				{
					return true;
				}
				(*ColoredGraph)[current] = true;
			}
			return false;
		}

		std::map<Function*, Function*>* RefineDefs(std::map<Function*, Function*>* repr)
		{
			for (Function* function : this->_quantified_variables)
			{
				if ((*repr)[function] != function)
				{
					continue; // quantified variable already represented by something else
				}
				Function* NewGround = function;

				for (Function* InSameClass : *_class[function->GetRoot()])
				{
					if (InSameClass == function || this->_quantified_variables.count(InSameClass) != 0 || this->MakesCycle(InSameClass, repr))
					{
						continue; // quantified variable shouldn't be represented by self, another quantified variable and it shouldn't create a cycle
					}
					NewGround = InSameClass;
					break;
				}

				for (Function* InSameClass : *_class[function->GetRoot()])
				{
					(*repr)[InSameClass] = NewGround;
				}
			}
			return repr;
		}

		void AddPredicate(std::vector<Function*>* functions, z3::expr* value)
		{
			for (size_t i = 0; i < functions->size(); i++)
			{
				Function* oldFunction = (*functions)[i];
				if (TryGetRealFunction(oldFunction, this->_functions, &(*functions)[i]))
				{
					// delete
				}
			}
			Function* newFunc = this->AddFunction(functions, value);
			this->_in_equalities.push_back(newFunc);
		}
	};
}


#endif // EGraphs_h
