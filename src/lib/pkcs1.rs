/*++ @file

  Copyright ©2021 Liu Yi, efikarl@yeah.net

  This program is just made available under the terms and conditions of the
  MIT license: http://www.efikarl.com/mit-license.html

  THE PROGRAM IS DISTRIBUTED UNDER THE MIT LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
--*/

use num_traits::{Zero,One};
use num_bigint::{BigUint,RandBigInt,BigInt,Sign};
use rand::Rng;

const N_SIZE_LO_LIMIT :u64 = 1;

trait Prime<T> {
    fn random_prime(bits: u64) -> T;

    fn is_prime(&self) -> bool;
    fn prime_test_of_trial_division(&self) -> bool;
    fn prime_test_of_fermat(&self) -> bool;
    fn prime_test_of_miller(&self) -> bool;
}

impl Prime<BigUint> for BigUint {
    fn random_prime(bits: u64) -> BigUint {
        let bits = if bits < 8 {
            8
        } else {
            bits
        };

        let mut rng = rand::thread_rng();
        loop {
            let n: BigUint = rng.gen_biguint(bits as u64);
            if n.is_prime() == true {
                return n;
            }
        }
    }

    fn is_prime(&self) -> bool {
        let ref x1 = BigUint::one();
        let ref x2 = x1 + x1;

        if self % x2 == BigUint::zero() {
            return false;
        }

        if !self.prime_test_of_fermat() {
            return false;
        }

        if !self.prime_test_of_miller() {
            return false;
        }

        return true;
    }

    fn prime_test_of_trial_division(&self) -> bool {
        let ref x0 = BigUint::zero();
        let ref x2 = BigUint::one() + BigUint::one();

        let mut u = BigUint::one() + BigUint::one();
        loop {
            u = u + BigUint::one();
            if self % x2 == *x0 {
                continue;
            }
            if &u > &self.sqrt() {
                break;
            } else {
                if self % &u == *x0 {
                    return false;
                }
            }
        }

        // println!("p = {:?}", self);
        return true;
    }

    fn prime_test_of_fermat(&self) -> bool {
        let ref x1 = BigUint::one();

        let mut b = x1 + x1;
        let ref n_minus_1 = self - x1;
        loop {
            if b >= BigUint::from_slice(&[16]) || &b > self {
                break;
            }
            let ref result = b.modpow(&n_minus_1, self);
            if result != x1 {
                return false;
            }

            b = b + x1;
        }

        return true;
    }

    fn prime_test_of_miller(&self) -> bool {
        let ref x1 = BigUint::one();
        let ref x2 = x1 + x1;

        if self == x2 {
            return true;
        }
        // Miller-Rabin's Test
        let mut b = x1 + x1;
        let ref n_minus_1 = self - x1;
        loop {
            if b >= BigUint::from_slice(&[8]) || &b > self {
                break;
            }

            // if n-1 = m*2^s, z = b^(n-1) % n = b^(m*2^s) % n, m is odd number
            let s = n_minus_1.trailing_zeros();
            let m = if let Some(s) = s {
                n_minus_1 >> s
            } else {
                // never to here, if and only if n is even number
                return false;
            };

            let mut x = b.modpow(&m, self);
            let mut result; 
            for _ in s {
                result = x.modpow(&(x1+x1), self);
                // if n is a prime, the solution of x^2≡1(mod n) shall be 1 or (n-1)
                if &result == x1 && &x != x1 &&  &x != n_minus_1 {
                    return false;
                }
                x = result;
            }
            // if n is a prime, then b^(n-1)≡1 (mod n), so result shall be 1
            if &x != x1 {
                return false;
            }

            b = b + x1;
        }

        // println!("p = {:?}", self);
        return true;
    }
}

#[derive(Clone, Debug)]
struct Key {
    p       : BigUint,
    q       : BigUint,
    n       : BigUint,
    e       : BigUint,
    d       : BigUint,
    u       : u64,
}

#[derive(Clone, Debug)]
pub struct Rsa {
    inner   : Key,
}

impl Rsa {
    pub fn new(bits: u64) -> Self {
        let mut k = Rsa::init(bits);

        while !k.check() {
            k = Rsa::init(bits);
        }
        // println!("{:#?}", k);

        k
    }

    pub fn init(bits: u64) -> Self {
        let x1 = BigUint::one();

        let mut p;
        let mut q;
        let mut n;
        loop {
            p = BigUint::random_prime(bits);
            q = BigUint::random_prime(bits);
            if p == q {
                continue;
            }
            n = &p * &q;
            if n.bits() >= (N_SIZE_LO_LIMIT * 8) {
                break;
            }
        }
        // :l is \lambda(n) in (pkcs) #1
        let l = (&p - &x1) * (&q - &x1);
        let e = Self::calculate_e(&l, &n);
        let d = Self::calculate_d(&l, &n, &e);
        let u = Self::random_epdp_unit(&n);

        Self { inner: Key { p, q, n, e, d, u } }
    }

    pub fn ek(&self) -> (BigUint, BigUint) {
        (self.inner.n.clone(), self.inner.e.clone())
    }

    pub fn dk(&self) -> (BigUint, BigUint) {
        (self.inner.n.clone(), self.inner.d.clone())
    }

    pub fn ep(&self, m: &BigUint) -> BigUint {
        let c = m.modpow(&self.inner.e, &self.inner.n);
        c
    }

    pub fn dp(&self, c: &BigUint) -> BigUint {
        let m = c.modpow(&self.inner.d, &self.inner.n);
        m
    }

    fn gcd(a: &BigUint, b: &BigUint) -> BigUint {
        let max;
        let min;
        if a > b {
            max = a;
            min = b;
        } else {
            max = b;
            min = a;
        }
        if min.is_zero() {
            return max.clone();
        }

        Self::gcd(min, &(max % min))
    }

    fn gcd_ex(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
        let mut q;
        let mut d;
        let mut r;
        if a > b {
            d = a.clone(); r = b.clone();
        } else {
            d = b.clone(); r = a.clone();
        }
        let mut u = BigInt::one();
        let mut v = BigInt::zero();
        let mut s = BigInt::zero();
        let mut t = BigInt::one();

        while !r.is_zero() {
            // q, r = divmod(d, r)
            let p = r.clone(); q = &d / &r; r = &d % &r; d = p;
            // gcd(a, b) = ax + by
            let p = u; u = s.clone(); s = p - &q * &s;
            let p = v; v = t.clone(); t = p - &q * &t; 
        }
        
        if a > b {
            return (d, u, v);
        } else {
            return (d, v, u);
        }
    }

    fn random_epdp_unit(n: &BigUint) -> u64 {
        let u = n.bits();

        let mut rng = rand::thread_rng();
        let r = rng.gen_range((u>>1)..u);

        let u = r >> 3;
        let u = if u == 0 {
            N_SIZE_LO_LIMIT
        } else {
            u
        };
        // println!("u = {}", u);

        u
    }

    fn calculate_e(l: &BigUint, n: &BigUint) -> BigUint {
        let mut rng = rand::thread_rng();
        loop {
            let u = rng.gen_biguint_range(&BigUint::new(vec![3]), n);
            if Self::gcd(l, &u).is_one() {
                // println!("e = {:?}", u);
                return u;
            }
        }
    }

    fn calculate_d(l: &BigUint, n: &BigUint, e: &BigUint) -> BigUint {
        let (_, _, d) = Self::gcd_ex (
            &BigInt::from_slice(Sign::Plus, l.to_u32_digits().as_slice()),
            &BigInt::from_slice(Sign::Plus, e.to_u32_digits().as_slice()),
        );

        let n_as_int = BigInt::from_slice(Sign::Plus, n.to_u32_digits().as_slice());
        let d = &d % &n_as_int;
        let d = if d < BigInt::zero() { d + n_as_int } else { d };

        d.to_biguint().unwrap()
    }

    fn check(&self) -> bool {
        let x1 = BigUint::one();
        let rsa = Self::init(8);
        
        let l = (&rsa.inner.p - &x1) * (&rsa.inner.q - &x1);
        if &rsa.inner.e * &rsa.inner.d % l != x1 {
            return false;
        }
        let mut i_m = BigUint::zero();
        loop {
            if i_m >= BigUint::from_slice(&[8]) {
                break;
            }
            let o_c = rsa.ep(&i_m);
            let o_m = rsa.dp(&o_c);
            if i_m != o_m {
                return false;
            }

            i_m += BigUint::one();
        }
        return true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rsa_ep_dp_test() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);

        let ref n = &rsa.inner.p * &rsa.inner.q;
        assert_eq!(&rsa.inner.n, n);

        let ref l = (&rsa.inner.p - BigUint::one()) * (&rsa.inner.p - BigUint::one());
        assert!(Rsa::gcd(&rsa.inner.e, l) == BigUint::one());

        let mut i_m = BigUint::zero();
        loop {
            if &i_m >= &rsa.inner.n {
                break;
            }
            let o_c = rsa.ep(&i_m);
            let o_m = rsa.dp(&o_c);
            assert_eq!(i_m, o_m);

            println!("i_m = {}", i_m);
            println!("o_c = {}", o_c);
            println!("o_m = {}", o_m);

            i_m += BigUint::one();
        }
    }

    #[test]
    fn rsa_prime_test() {
        let rsa = Rsa::new(1024);
        println!("{:#?}", rsa);
    }
}
