/*++ @file

  Copyright ©2021 Liu Yi, efikarl@yeah.net

  This program is just made available under the terms and conditions of the
  MIT license: http://www.efikarl.com/mit-license.html

  THE PROGRAM IS DISTRIBUTED UNDER THE MIT LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
--*/

use num_traits::{Zero,One};
use num_bigint::{BigUint,RandBigInt};
use rand::Rng;

const N_SIZE_LO_LIMIT :u64 = 1;
const P_MR_TEST_TIMES :u64 = 8;
const P_MR_BASE_LIMIT :u32 = 0xFF;

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
        let ref x1 = BigUint::one();
        let ref x2 = x1 + x1;

        if self == x2 {
            return true;
        }
        if self % x2 == BigUint::zero() {
            return false;
        }
        // Miller-Rabin's Test
        let ref n_minus_1 = self - x1;
        let mut mrt_times = 1;
        loop {
            if mrt_times > P_MR_TEST_TIMES {
                break;
            }

            let mut rng = rand::thread_rng();
            let b = rng.gen_range(BigUint::one()..BigUint::from_slice(&[P_MR_BASE_LIMIT])); // todo: ref n_minus_1 when SampleUniform

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

            mrt_times = mrt_times + 1;
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
            if p == q {
                continue;
            }
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

    #[test]
    fn rsa_prime_check() {
        let rsa = Rsa::new(16);
        println!("{:#?}", rsa);
    }
}
