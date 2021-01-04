/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolutil/LP.h>

#include <libsolutil/CommonData.h>
#include <liblangutil/Exceptions.h>

using namespace std;
using namespace solidity;
using namespace solidity::util;
using namespace solidity::smtutil;


namespace
{

vector<rational>& operator/=(vector<rational>& _data, rational const& _divisor)
{
	for (rational& x: _data)
		x /= _divisor;
	return _data;
}

vector<rational> operator-(vector<rational> const& _x, vector<rational> const& _y)
{
	vector<rational> result = vector<rational>(max(_x.size(), _y.size()), rational{});
	for (size_t i = 0; i < result.size(); ++i)
	{
		result[i] = i < _x.size() ? _x.at(i) : 0;
		result[i] -= i < _y.size() ? _y.at(i) : 0;
	}
	return result;
}


/// Add slack variables to turn the tableau into equality form.
/// At the same time, it inverts all rows with negative b.
/// TODO: Does this change the problem?
Tableau toEquationalForm(Tableau _tableau)
{
	size_t rows = _tableau.data.size();
	size_t columns = _tableau.data.at(0).size();
	for (size_t i = 1; i < rows; ++i)
	{
		solAssert(_tableau.data[i].size() == columns, "");
		solAssert(_tableau.data[i][0] >= rational{}, "");
		_tableau.data[i] += vector<bigint>(rows - 1, bigint{});
		_tableau.data[i][columns + i - 1] = 1;
	}

	return _tableau;
}

optional<size_t> findPivotColumn(Tableau const& _tableau)
{
	size_t column = 1;
	rational minValue = _tableau.data[0][column];
	for (size_t i = 2; i < _tableau.data[0].size(); ++i)
		if (_tableau.data[0][i] < minValue)
		{
			minValue = _tableau.data[0][i];
			column = i;
		}

	if (minValue >= rational{0})
		return nullopt; // found optimum
	else
		return column;
}

optional<size_t> findPivotRow(Tableau const& _tableau, size_t _pivotColumn)
{
	size_t row = 0;
	rational minRatio = rational{-1};
	for (size_t i = 1; i < _tableau.data.size(); ++i)
	{
		rational ratio = _tableau.data[i][0] / _tableau.data[i][_pivotColumn];
		// TODO check
		if ((ratio > 0 && ratio < minRatio) || minRatio < 0)
		{
			minRatio = ratio;
			row = i;
		}
	}

		// TODO What if negative but not -1?
	if (minRatio == -1)
		return nullopt; // unbounded
	else
		return row;
}

Tableau performPivot(Tableau _tableau, size_t _pivotRow, size_t _pivotColumn)
{
	rational pivot = _tableau.data[_pivotRow][_pivotColumn];
	solAssert(pivot > 0, "");
	_tableau.data[_pivotRow] /= pivot;
	solAssert(_tableau.data[_pivotRow][_pivotColumn] == rational(1), "");

	for (size_t i = 0; i < _tableau.data.size(); ++i)
		if (i != _pivotRow)
		{
			rational multiplier = _tableau.data[i][_pivotColumn];
			for (size_t j = 0; j < _tableau.data.front().size(); ++j)
				_tableau.data[i][j] -= multiplier * _tableau.data[_pivotRow][j];
		}
	return _tableau;
}

void printTableau(Tableau _tableau)
{
	cout << "------------" << endl;
	for (auto const& row: _tableau.data)
	{
		for (auto const& element: row)
			cout << element << ", ";
		cout << endl;
	}
}

}

LPResult solidity::util::simplex(Tableau _tableau)
{
	printTableau(_tableau);
	_tableau = toEquationalForm(move(_tableau));
	cout << "Equational: " << endl;
	printTableau(_tableau);

	// TODO What if there is no trivial basic solution?

	for (size_t step = 0; step <= 500; ++step)
	{
		optional<size_t> pivotColumn = findPivotColumn(_tableau);
		if (!pivotColumn)
			return LPResult::Feasible;
		optional<size_t> pivotRow = findPivotRow(_tableau, *pivotColumn);
		if (!pivotRow)
			return LPResult::Unbounded;
		_tableau = performPivot(move(_tableau), *pivotRow, *pivotColumn);
		cout << "After step " << step << endl;
		printTableau(_tableau);
	}
	return LPResult::Unknown;
}

void LPSolver::declareVariable(string const& _name, SortPointer const& _sort)
{
	solAssert(_sort && _sort->kind == Kind::Int, "");
	solAssert(!m_variables.count(_name), "");
	size_t index = m_variables.size() + 1;
	m_variables[_name] = index;
}

void LPSolver::addAssertion(Expression const& _expr)
{
	if (_expr.name == "&&")
	{
		addAssertion(_expr.arguments.at(0));
		addAssertion(_expr.arguments.at(1));
	}
	if (_expr.name == "<=")
	{
		vector<rational> constraint =
			parseLinearSum(_expr.arguments.at(0)) -
			parseLinearSum(_expr.arguments.at(1));
		constraint[0] *= -1;
		m_constraints.emplace_back(move(constraint));
	}
	else
		solAssert(false, "");

}

pair<CheckResult, vector<string>> LPSolver::check(vector<Expression> const&)
{
	vector<vector<rational>> constraints = m_constraints;
	size_t numColumns = 0;
	for (auto const& row: constraints)
		numColumns = max(numColumns, row.size());
	for (auto& row: constraints)
		row.resize(numColumns);

	Tableau tableau;
	tableau.data.push_back(vector<rational>(numColumns - 1, rational(bigint(1))));
	tableau.data += move(constraints);
	CheckResult smtResult;
	switch (simplex(tableau))
	{
	case LPResult::Feasible:
	case LPResult::Unbounded: // TODO true?
		smtResult = CheckResult::SATISFIABLE;
		break;
	case LPResult::Infeasible:
		smtResult = CheckResult::UNSATISFIABLE;
		break;
	case LPResult::Unknown:
		smtResult = CheckResult::UNKNOWN;
		break;
	}
	// TODO we could evaluate the listed variables here.
	return make_pair(smtResult, vector<string>{});
}

vector<rational> LPSolver::parseLinearSum(smtutil::Expression const& _expr) const
{
	if (_expr.arguments.empty() || _expr.name == "*")
		return parseProduct(_expr);
	else if (_expr.name == "+")
		return parseLinearSum(_expr.arguments.at(0)) + parseLinearSum(_expr.arguments.at(1));
	else if (_expr.name == "-")
		return parseLinearSum(_expr.arguments.at(0)) - parseLinearSum(_expr.arguments.at(1));
	else
		solAssert(false, "");
}

vector<rational> LPSolver::parseProduct(smtutil::Expression const& _expr) const
{
	// TODO this might be more clearly impliminted by making parseFactor return a proper vector
	// and then defining a vector * vector operator that checks that only one variable index
	// is nonzero.
	vector<rational> result;
	if (_expr.arguments.empty())
	{
		variant<rational, size_t> value = parseFactor(_expr);
		if (holds_alternative<size_t>(value))
		{
			result.resize(get<size_t>(value) + 1);
			result[get<size_t>(value)] = rational(bigint(1));
		}
		else
		{
			result.resize(1);
			result[0] = get<rational>(value);
		}
	}
	else if (_expr.name == "*")
	{
		variant<rational, size_t> left = parseFactor(_expr.arguments.at(0));
		variant<rational, size_t> right = parseFactor(_expr.arguments.at(1));
		// Only one of them can be a variable.
		solAssert(!(holds_alternative<size_t>(left) && holds_alternative<size_t>(right)), "");
		if (holds_alternative<size_t>(left))
		{
			result.resize(get<size_t>(left) + 1);
			result[get<size_t>(left)] = get<rational>(right);
		}
		else if (holds_alternative<size_t>(right))
		{
			result.resize(get<size_t>(right) + 1);
			result[get<size_t>(right)] = get<rational>(left);
		}
		else
		{
			result.resize(1);
			result[0] = get<rational>(left) * get<rational>(right);
		}
	}
	else
		solAssert(false, "");

	return result;
}

variant<rational, size_t> LPSolver::parseFactor(smtutil::Expression const& _expr) const
{
	solAssert(_expr.arguments.empty(), "");
	solAssert(!_expr.name.empty(), "");
	if ('0' <= _expr.name[0] && _expr.name[0] <= '9')
		return {rational(bigint(_expr.name))};

	size_t index = m_variables.at(_expr.name);
	solAssert(index > 0, "");
	return {index};
}
