#include "maybeBdd.h"

bool MaybeBDD::approximationHappened = false;

MaybeBDD MaybeBDD::And(const MaybeBDD &other) const
{
    if (this->HasValue() && other.HasValue())
    {
	return MaybeBDD(*bddManager, GetBDD() & other.GetBDD());
    }

    if (this->HasValue() && this->GetBDD().IsZero())
    {
	return *this;
    }

    if (other.HasValue() && other.GetBDD().IsZero())
    {
	return other;
    }

    return MaybeBDD(*bddManager);
}

MaybeBDD MaybeBDD::Or(const MaybeBDD &other) const
{
    if (this->HasValue() && other.HasValue())
    {
	return MaybeBDD(*bddManager, GetBDD() | other.GetBDD());
    }

    if (this->HasValue() && this->GetBDD().IsOne())
    {
	return *this;
    }

    if (other.HasValue() && other.GetBDD().IsOne())
    {
	return other;
    }

    return MaybeBDD(*bddManager);
}

MaybeBDD MaybeBDD::Xor(const MaybeBDD &other) const
{
    if (this->HasValue() && other.HasValue())
    {
	return MaybeBDD(*bddManager, GetBDD() ^ other.GetBDD());
    }

    return MaybeBDD(*bddManager);
}

MaybeBDD MaybeBDD::Xnor(const MaybeBDD &other) const
{
    if (this->HasValue() && other.HasValue())
    {
	return MaybeBDD(*bddManager, GetBDD().Xnor(other.GetBDD()));
    }

    return MaybeBDD(*bddManager);
}

MaybeBDD MaybeBDD::Not() const
{
    if (this->HasValue())
    {
	return MaybeBDD(*bddManager, !GetBDD());
    }

    return MaybeBDD(*bddManager);
}

MaybeBDD MaybeBDD::Ite(const MaybeBDD &thenBdd, const MaybeBDD &elseBdd) const
{
    if (thenBdd.Equals(elseBdd))
    {
	return thenBdd;
    }

    if (this->HasValue() && thenBdd.HasValue() && elseBdd.HasValue())
    {
	return MaybeBDD(*bddManager, this->GetBDD().Ite(thenBdd.GetBDD(), elseBdd.GetBDD()));
    }

    if (this->HasValue() && this->GetBDD().IsOne())
    {
	return thenBdd;
    }

    if (this->HasValue() && this->GetBDD().IsZero())
    {
	return elseBdd;
    }

    return MaybeBDD(*bddManager);
}