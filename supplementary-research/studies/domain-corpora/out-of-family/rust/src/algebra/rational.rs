//! Exact rational arithmetic, so the Groebner computation is over a field
//! and its output can be compared against published bases without
//! floating-point slack.

use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// A rational number in lowest terms with a positive denominator.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Rat {
    num: i128,
    den: i128,
}

impl Rat {
    pub const ZERO: Rat = Rat { num: 0, den: 1 };
    pub const ONE: Rat = Rat { num: 1, den: 1 };

    pub fn new(num: i128, den: i128) -> Rat {
        assert!(den != 0, "zero denominator");
        let sign = if den < 0 { -1 } else { 1 };
        let g = gcd(num, den).max(1);
        Rat {
            num: sign * num / g,
            den: sign * den / g,
        }
    }

    pub fn int(n: i128) -> Rat {
        Rat { num: n, den: 1 }
    }

    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    pub fn is_negative(self) -> bool {
        self.num < 0
    }

    pub fn inv(self) -> Rat {
        Rat::new(self.den, self.num)
    }
}

impl Add for Rat {
    type Output = Rat;
    fn add(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den + o.num * self.den, self.den * o.den)
    }
}
impl Sub for Rat {
    type Output = Rat;
    fn sub(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den - o.num * self.den, self.den * o.den)
    }
}
impl Mul for Rat {
    type Output = Rat;
    fn mul(self, o: Rat) -> Rat {
        Rat::new(self.num * o.num, self.den * o.den)
    }
}
impl Div for Rat {
    type Output = Rat;
    fn div(self, o: Rat) -> Rat {
        Rat::new(self.num * o.den, self.den * o.num)
    }
}
impl Neg for Rat {
    type Output = Rat;
    fn neg(self) -> Rat {
        Rat {
            num: -self.num,
            den: self.den,
        }
    }
}

impl fmt::Display for Rat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_is_exact_and_normalized() {
        let a = Rat::new(1, 3);
        let b = Rat::new(1, 6);
        assert_eq!(a + b, Rat::new(1, 2));
        assert_eq!(a - b, Rat::new(1, 6));
        assert_eq!(a * b, Rat::new(1, 18));
        assert_eq!(a / b, Rat::int(2));
        assert_eq!(Rat::new(2, -4).to_string(), "-1/2");
        assert!((a - a).is_zero());
    }
}
