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
#pragma once

#include <libsmtutil/SolverInterface.h>

#include <libsolutil/Common.h>

#include <boost/rational.hpp>

#include <vector>
#include <variant>

namespace solidity::util
{

using rational = boost::rational<bigint>;

/**
 * Simplex tableau with the first row representing the objective function.
 */
struct Tableau
{
	std::vector<std::vector<rational>> data;
};

enum class LPResult
{
	Unknown,
	Unbounded,
	Feasible,
	Infeasible
};

/// Solve the LP Ax <= b s.t. max c^Tx
/// The first row encodes the objective function
/// The first column encodes b
LPResult simplex(Tableau _tableau);

class LPSolver: smtutil::SolverInterface
{
public:
	void reset() {}

	void push() {}
	void pop() {}

	void declareVariable(std::string const& _name, smtutil::SortPointer const& _sort) override;

	void addAssertion(smtutil::Expression const& _expr) override;

	std::pair<smtutil::CheckResult, std::vector<std::string>>
	check(std::vector<smtutil::Expression> const& _expressionsToEvaluate) override;

private:
	/// Parses the expression and expects a linear sum of variables.
	/// Returns a vector with the first element being the constant and the
	/// other elements the factors for the respective variables.
	std::vector<rational> parseLinearSum(smtutil::Expression const& _expression) const;
	std::vector<rational> parseProduct(smtutil::Expression const& _expression) const;
	std::variant<rational, size_t> parseFactor(smtutil::Expression const& _expression) const;

	std::map<std::string, size_t> m_variables;
	std::vector<std::vector<rational>> m_constraints;
};


}
