use algebra::{PairingCurve, PairingEngine};

use crate::SynthesisError;
use std::io::{self, Read, Result as IoResult, Write};
use algebra::{bytes::FromBytes, curves::AffineCurve as CurveAffine};
use algebra::bytes::ToBytes;
use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};
mod r1cs_to_sap;

mod generator;
mod prover;
mod verifier;

#[cfg(test)]
mod test;

pub use self::{generator::*, prover::*, verifier::*};

#[derive(Clone)]
pub struct Proof<E: PairingEngine> {
    pub a: E::G1Affine,
    pub b: E::G2Affine,
    pub c: E::G1Affine,
}

impl<E: PairingEngine> ToBytes for Proof<E> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.a.write(&mut writer)?;
        self.b.write(&mut writer)?;
        self.c.write(&mut writer)
    }
}

impl<E: PairingEngine> PartialEq for Proof<E> {
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a && self.b == other.b && self.c == other.c
    }
}

impl<E: PairingEngine> Default for Proof<E> {
    fn default() -> Self {
        Self {
            a: E::G1Affine::default(),
            b: E::G2Affine::default(),
            c: E::G1Affine::default(),
        }
    }
}

impl<E:PairingEngine> FromBytes for Proof<E> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let a = E::G1Affine::read(&mut reader).and_then(|e| if e.is_zero() {
            Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
        } else {
            Ok(e)
        })?;
        let b = E::G2Affine::read(&mut reader).and_then(|e| if e.is_zero() {
            Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
        } else {
            Ok(e)
        })?;
        let c = E::G1Affine::read(&mut reader).and_then(|e| if e.is_zero() {
            Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
        } else {
            Ok(e)
        })?;

        Ok(Self { a, b, c })
    }
}

#[derive(Clone)]
pub struct VerifyingKey<E: PairingEngine> {
    pub h_g2:       E::G2Affine,
    pub g_alpha_g1: E::G1Affine,
    pub h_beta_g2:  E::G2Affine,
    pub g_gamma_g1: E::G1Affine,
    pub h_gamma_g2: E::G2Affine,
    pub query:      Vec<E::G1Affine>,
}

impl<E: PairingEngine> ToBytes for VerifyingKey<E> {
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.h_g2.write(&mut writer)?;
        self.g_alpha_g1.write(&mut writer)?;
        self.h_beta_g2.write(&mut writer)?;
        self.g_gamma_g1.write(&mut writer)?;
        self.h_gamma_g2.write(&mut writer)?;
        for q in &self.query {
            q.write(&mut writer)?;
        }
        Ok(())
    }
}

impl<E:PairingEngine> FromBytes for VerifyingKey<E> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let h_g2 = E::G2Affine::read(&mut reader).map_err(|e|
            io::Error::new(io::ErrorKind::InvalidData, e))?;
        let g_alpha_g1 = E::G1Affine::read(&mut reader).map_err(|e|
            io::Error::new(io::ErrorKind::InvalidData, e))?;
        let h_beta_g2 = E::G2Affine::read(&mut reader).map_err(|e|
            io::Error::new(io::ErrorKind::InvalidData, e))?;
        let g_gamma_g1 = E::G1Affine::read(&mut reader).map_err(|e|
            io::Error::new(io::ErrorKind::InvalidData, e))?;
        let h_gamma_g2 = E::G2Affine::read(&mut reader).map_err(|e|
            io::Error::new(io::ErrorKind::InvalidData, e))?;

        let ic_len = reader.read_u32::<BigEndian>()? as usize;
        let mut query = vec![];

        for _ in 0..ic_len {
            let g1 = E::G1Affine::read(&mut reader)
                .map_err(|e|io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })?;
            query.push(g1);
        }

        Ok(VerifyingKey {
            h_g2,
            g_alpha_g1,
            h_beta_g2,
            g_gamma_g1,
            h_gamma_g2,
           query 
        })
    }
}


impl<E: PairingEngine> Default for VerifyingKey<E> {
    fn default() -> Self {
        Self {
            h_g2:       E::G2Affine::default(),
            g_alpha_g1: E::G1Affine::default(),
            h_beta_g2:  E::G2Affine::default(),
            g_gamma_g1: E::G1Affine::default(),
            h_gamma_g2: E::G2Affine::default(),
            query:      Vec::new(),
        }
    }
}

impl<E: PairingEngine> PartialEq for VerifyingKey<E> {
    fn eq(&self, other: &Self) -> bool {
        self.h_g2 == other.h_g2
            && self.g_alpha_g1 == other.g_alpha_g1
            && self.h_beta_g2 == other.h_beta_g2
            && self.g_gamma_g1 == other.g_gamma_g1
            && self.h_gamma_g2 == other.h_gamma_g2
            && self.query == other.query
    }
}

#[derive(Clone)]
pub struct Parameters<E: PairingEngine> {
    pub vk:           VerifyingKey<E>,
    pub a_query:      Vec<E::G1Affine>,
    pub b_query:      Vec<E::G2Affine>,
    pub c_query_1:    Vec<E::G1Affine>,
    pub c_query_2:    Vec<E::G1Affine>,
    pub g_gamma_z:    E::G1Affine,
    pub h_gamma_z:    E::G2Affine,
    pub g_ab_gamma_z: E::G1Affine,
    pub g_gamma2_z2:  E::G1Affine,
    pub g_gamma2_z_t: Vec<E::G1Affine>,
}

impl<E: PairingEngine> PartialEq for Parameters<E> {
    fn eq(&self, other: &Self) -> bool {
        self.vk == other.vk
            && self.a_query == other.a_query
            && self.b_query == other.b_query
            && self.c_query_1 == other.c_query_1
            && self.c_query_2 == other.c_query_2
            && self.g_gamma_z == other.g_gamma_z
            && self.h_gamma_z == other.h_gamma_z
            && self.g_ab_gamma_z == other.g_ab_gamma_z
            && self.g_gamma2_z2 == other.g_gamma2_z2
            && self.g_gamma2_z_t == other.g_gamma2_z_t
    }
}

impl<E: PairingEngine> ToBytes for Parameters<E> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.vk.write(&mut writer)?;

        writer.write_u32::<BigEndian>(self.a_query.len() as u32)?;
        for v in &self.a_query[..] {
            v.write(&mut writer)?;
        }

        writer.write_u32::<BigEndian>(self.b_query.len() as u32)?;
        for v in &self.b_query[..] {
            v.write(&mut writer)?;
        }

        writer.write_u32::<BigEndian>(self.c_query_1.len() as u32)?;
        for v in &self.c_query_1[..] {
            v.write(&mut writer)?;
        }

        writer.write_u32::<BigEndian>(self.c_query_2.len() as u32)?;
        for v in &self.c_query_2[..] {
            v.write(&mut writer)?;
        }

        writer.write_u32::<BigEndian>(self.g_gamma2_z_t.len() as u32)?;
        for v in &self.g_gamma2_z_t[..] {
            v.write(&mut writer)?;
        }

        self.g_gamma_z.write(&mut writer)?;
        self.h_gamma_z.write(&mut writer)?;
        self.g_ab_gamma_z.write(&mut writer)?;
        self.g_gamma2_z2.write(&mut writer)?;

        Ok(())
    }
}

impl<E:PairingEngine> FromBytes for Parameters<E> {
    #[inline]
    fn read<R: Read>(mut reader: R) -> IoResult<Self> {
        let vk = VerifyingKey::read(&mut reader)?;


        let read_g1 = |mut r: &mut R| -> io::Result<E::G1Affine> {
            E::G1Affine::read(&mut r)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })
        };

        let read_g2 = |mut r: &mut R| -> io::Result<E::G2Affine> {
            E::G2Affine::read(&mut r)
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
                .and_then(|e| if e.is_zero() {
                    Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
                } else {
                    Ok(e)
                })
        };

        let mut a_query = vec![];
        let mut b_query = vec![];
        let mut c_query_1 = vec![];
        let mut c_query_2 = vec![];
        let mut g_gamma2_z_t = vec![];


        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                a_query.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                b_query.push(read_g2(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                c_query_1.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                c_query_2.push(read_g1(&mut reader)?);
            }
        }

        {
            let len = reader.read_u32::<BigEndian>()? as usize;
            for _ in 0..len {
                g_gamma2_z_t.push(read_g1(&mut reader)?);
            }
        }
        
        let g_gamma_z = read_g1(&mut reader)?;
        let h_gamma_z = read_g2(&mut reader)?;
        let g_ab_gamma_z = read_g1(&mut reader)?;
        let g_gamma2_z2 = read_g1(&mut reader)?;

        Ok(Parameters {
            vk: vk,
            a_query: a_query,
            b_query: b_query,
            c_query_1: c_query_1,
            c_query_2: c_query_2,
            g_gamma_z: g_gamma_z,
            h_gamma_z: h_gamma_z,
            g_ab_gamma_z: g_ab_gamma_z,
            g_gamma2_z2: g_gamma2_z2,
            g_gamma2_z_t: g_gamma2_z_t
        })
    }
}



#[derive(Clone)]
pub struct PreparedVerifyingKey<E: PairingEngine> {
    pub vk:                VerifyingKey<E>,
    pub g_alpha:           E::G1Affine,
    pub h_beta:            E::G2Affine,
    pub g_alpha_h_beta_ml: E::Fqk,
    pub g_gamma_pc:        <E::G1Affine as PairingCurve>::Prepared,
    pub h_gamma_pc:        <E::G2Affine as PairingCurve>::Prepared,
    pub h_pc:              <E::G2Affine as PairingCurve>::Prepared,
    pub query:             Vec<E::G1Affine>,
}

impl<E: PairingEngine> From<PreparedVerifyingKey<E>> for VerifyingKey<E> {
    fn from(other: PreparedVerifyingKey<E>) -> Self {
        other.vk
    }
}

impl<E: PairingEngine> From<VerifyingKey<E>> for PreparedVerifyingKey<E> {
    fn from(other: VerifyingKey<E>) -> Self {
        prepare_verifying_key(&other)
    }
}

impl<E: PairingEngine> Default for PreparedVerifyingKey<E> {
    fn default() -> Self {
        Self {
            vk:                VerifyingKey::default(),
            g_alpha:           E::G1Affine::default(),
            h_beta:            E::G2Affine::default(),
            g_alpha_h_beta_ml: E::Fqk::default(),
            g_gamma_pc:        <E::G1Affine as PairingCurve>::Prepared::default(),
            h_gamma_pc:        <E::G2Affine as PairingCurve>::Prepared::default(),
            h_pc:              <E::G2Affine as PairingCurve>::Prepared::default(),
            query:             Vec::new(),
        }
    }
}

impl<E: PairingEngine> ToBytes for PreparedVerifyingKey<E> {
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.vk.write(&mut writer)?;
        self.g_alpha.write(&mut writer)?;
        self.h_beta.write(&mut writer)?;
        self.g_alpha_h_beta_ml.write(&mut writer)?;
        self.g_gamma_pc.write(&mut writer)?;
        self.h_gamma_pc.write(&mut writer)?;
        self.h_pc.write(&mut writer)?;
        for q in &self.query {
            q.write(&mut writer)?;
        }
        Ok(())
    }
}

impl<E: PairingEngine> Parameters<E> {
    pub fn get_vk(&self, _: usize) -> Result<VerifyingKey<E>, SynthesisError> {
        Ok(self.vk.clone())
    }

    pub fn get_a_query(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((&self.a_query[1..num_inputs], &self.a_query[num_inputs..]))
    }

    pub fn get_b_query(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G2Affine], &[E::G2Affine]), SynthesisError> {
        Ok((&self.b_query[1..num_inputs], &self.b_query[num_inputs..]))
    }

    pub fn get_c_query_1(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((
            &self.c_query_1[0..num_inputs],
            &self.c_query_1[num_inputs..],
        ))
    }

    pub fn get_c_query_2(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((
            &self.c_query_2[1..num_inputs],
            &self.c_query_2[num_inputs..],
        ))
    }

    pub fn get_g_gamma_z(&self) -> Result<E::G1Affine, SynthesisError> {
        Ok(self.g_gamma_z)
    }

    pub fn get_h_gamma_z(&self) -> Result<E::G2Affine, SynthesisError> {
        Ok(self.h_gamma_z)
    }

    pub fn get_g_ab_gamma_z(&self) -> Result<E::G1Affine, SynthesisError> {
        Ok(self.g_ab_gamma_z)
    }

    pub fn get_g_gamma2_z2(&self) -> Result<E::G1Affine, SynthesisError> {
        Ok(self.g_gamma2_z2)
    }

    pub fn get_g_gamma2_z_t(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((
            &self.g_gamma2_z_t[0..num_inputs],
            &self.g_gamma2_z_t[num_inputs..],
        ))
    }

    pub fn get_a_query_full(&self) -> Result<&[E::G1Affine], SynthesisError> {
        Ok(&self.a_query)
    }

    pub fn get_b_query_full(&self) -> Result<&[E::G2Affine], SynthesisError> {
        Ok(&self.b_query)
    }

    pub fn get_c_query_1_full(&self) -> Result<&[E::G1Affine], SynthesisError> {
        Ok(&self.c_query_1)
    }

    pub fn get_c_query_2_full(&self) -> Result<&[E::G1Affine], SynthesisError> {
        Ok(&self.c_query_2)
    }

    pub fn get_g_gamma2_z_t_full(&self) -> Result<&[E::G1Affine], SynthesisError> {
        Ok(&self.g_gamma2_z_t)
    }
}
