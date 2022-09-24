/*
 * Copyright (C) BedRock Systems Inc. 2021
 *
 * SPDX-License-Identifier:MIT-0
 */

template <typename T>
constexpr auto	// __underlying_type (T)
my_underlying (T x)
{
    return static_cast <__underlying_type (T)> (x);
}

enum my_type : unsigned { Cats, Dogs, Bunnies };

unsigned
test (my_type x)
{
    return my_underlying (Bunnies) - my_underlying (x);
}
