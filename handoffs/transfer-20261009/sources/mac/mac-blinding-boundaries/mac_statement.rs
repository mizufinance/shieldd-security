// Pinned actual Statement::fields and encoding wrapper controls in disposable source copy.
use crate::{audit,encryption::{Core,Extended,Metadata,Policy,Published},group::Point,
    transfer::{OutputStatement,SpendStatement,Statement,VolumeStatement},encoding};
use commonware_codec::Encode;
use commonware_cryptography::bls12381::primitives::group::Scalar;
use commonware_math::algebra::{Additive,Ring};
fn p(x:u64,y:u64)->Point<u64>{Point{x,y}}
fn tagged()->Statement<u64>{Statement{
 rk:p(1,2),anchor:3,
 outputs:[OutputStatement{note:4,recovery:5},OutputStatement{note:6,recovery:7}],
 balance:p(8,9),routing_tags:[10,11],routing_parameter:12,
 volume:VolumeStatement{nullifier:13,commitment:14,day_start:15,context:16},
 spends:[SpendStatement{nullifier:17},SpendStatement{nullifier:18}],
 asset_anchor:19,compliance_anchor:20,timestamp:45,
 audit:Published{detection:[21,22,23,24],
  sender_core:Core{epk:p(25,26),c2:27,ciphertext:28,confirmation:46},
  sender_ext:Extended{epk:p(29,30),c2:31,ciphertext:[32,33,34]},
  output_core:Core{epk:p(35,36),c2:37,ciphertext:38,confirmation:47},
  output_ext:Extended{epk:p(39,40),c2:41,ciphertext:[42,43,44]},
  metadata:Metadata{policy:Policy{ring_id:48,policy_id:49,resource:50,permission:51,
    timestamp:999},salts:[52,53,54,55],audit_epoch:56},
  ownership:[audit::Ciphertext{r:p(57,58),c:p(59,60)},
    audit::Ciphertext{r:p(61,62),c:p(63,64)}]}}}
#[test]
fn mac_statement_tagged_all64(){
 let s=tagged();let expected:Vec<u64>=(1..=64).collect();
 assert_eq!(s.fields().to_vec(),expected);
 println!("MAC_STATEMENT_TAGS {:?}",s.fields());
 for value in s.fields() {
  let scalar=Scalar::from(value);let fq=encoding::native_field(&scalar);
  let mut expected=[0u8;32];expected[..8].copy_from_slice(&value.to_le_bytes());
  assert_eq!(fq.to_bytes(),expected,"each of all64 tagged positions has exact canonical SDK encoding");
  assert_eq!(encoding::field(&fq),scalar,"all64 actual codec wrapper inverse values");
 }
 println!("MAC_STATEMENT_ALL64_CODEC PASS");
 let mut swapped=s.clone();std::mem::swap(&mut swapped.audit.sender_core.confirmation,
   &mut swapped.audit.output_core.confirmation);
 assert_ne!(swapped.fields().to_vec(),expected,"core confirmations are bound at distinct positions");
 let mut wrong=s.clone();wrong.audit.metadata.policy.timestamp=1000;
 assert_eq!(wrong.fields(),s.fields(),"Transfer binds top-level timestamp; Published policy timestamp is not appended");
 let mut changed=s;changed.timestamp=1000;
 assert_ne!(changed.fields().to_vec(),expected,"Transfer top-level timestamp is bound");
 println!("MAC_STATEMENT_CONTROLS confirmation_swap top_level_timestamp metadata_timestamp_excluded");
}
#[test]
fn mac_statement_encoding_endpoints(){
 let cases=[("zero",Scalar::zero()),("one",Scalar::one()),
  ("u128_max",Scalar::from_limbs([u64::MAX,u64::MAX,0,0])),("field_max",-Scalar::one())];
 for (label,scalar) in cases {
  let fq=encoding::native_field(&scalar);let actual=fq.to_bytes();
  let mut expected:[u8;32]=scalar.encode().as_ref().try_into().unwrap();expected.reverse();
  assert_eq!(actual,expected,"canonical SDK little-endian / Commonware big-endian");
  assert_eq!(encoding::field(&fq),scalar,"actual inverse wrapper");
  println!("MAC_ENCODING {label} {:?}",actual);
 }
}
