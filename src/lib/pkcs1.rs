/*++ @file

  Copyright ©2021 Liu Yi, efikarl@yeah.net

  This program is just made available under the terms and conditions of the
  MIT license: http://www.efikarl.com/mit-license.html

  THE PROGRAM IS DISTRIBUTED UNDER THE MIT LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
--*/

use num_traits::{Zero,One};
use num_bigint::{BigUint,RandBigInt};

const N_SIZE_LO_LIMIT :u64 = 1;

trait Prime<T> {
    fn random_prime(bits: u64) -> T;

    fn is_prime(&self) -> bool;
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
        let ref x0 = BigUint::zero();
        let ref x2 = BigUint::one() + BigUint::one();
    
        if self % x2 == *x0 {
            return false;
        }

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
        let x1 = BigUint::one();

        let mut p;
        let mut q;
        let mut n;
        loop {
            p = BigUint::random_prime(bits);
            q = BigUint::random_prime(bits);
            n = &p * &q;
            if n.bits() >= (N_SIZE_LO_LIMIT * 8) {
                break;
            }
        }
        let l = (&p - &x1) * (&q - &x1);
        let e = Self::calculate_e(&l, &n);
        let d = Self::calculate_d(&l, &e);
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

    fn random_epdp_unit(n: &BigUint) -> u64 {
        let u = n.bits();

        use rand::Rng;
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

    fn calculate_e(lambda_n: &BigUint, n: &BigUint) -> BigUint {
        let mut rng = rand::thread_rng();
        loop {
            let u = rng.gen_biguint_range(&BigUint::new(vec![3]), n);
            if Self::gcd(lambda_n, &u).is_one() {
                // println!("e = {:?}", u);
                return u;
            }
        }
    }

    fn calculate_d(lambda_n: &BigUint, e: &BigUint) -> BigUint {
        let ref x0 = BigUint::zero();
        let ref x1 = BigUint::one();
    
        let mut u = BigUint::zero();
        loop {
            u = u + BigUint::one();
            if (e * &u - x1) % lambda_n == *x0 {
                // println!("d = {:?}", u);
                return u
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rsa_ep_dp_test() {
        let rsa = Rsa::new(8);
        println!("{:#?}", rsa);
        assert_eq!(&rsa.inner.n, &(&rsa.inner.p * &rsa.inner.q));
        assert!(&rsa.inner.e < &rsa.inner.n);
        assert!(Rsa::gcd(&rsa.inner.e, &((&rsa.inner.p - BigUint::one())*(&rsa.inner.p - BigUint::one()))) == BigUint::one());

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
}
