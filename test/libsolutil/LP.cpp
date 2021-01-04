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
#include <libsmtutil/Sorts.h>
#include <test/Common.h>

#include <boost/test/unit_test.hpp>

using namespace std;
using namespace solidity::smtutil;

namespace solidity::util::test
{

BOOST_AUTO_TEST_SUITE(LP, *boost::unit_test::label("nooptions"))

BOOST_AUTO_TEST_CASE(basic)
{
	LPSolver solver;
	solver.declareVariable("x", smtutil::SortProvider::sintSort);
	solver.addAssertion(Expression("2") * Expression("x") <= Expression("10"));
	solver.check({});
}

BOOST_AUTO_TEST_SUITE_END()

}
