use crate::{catalogue,proof::Family};
#[test]
fn mac_blinding_exact_sparse_row_certificates() {
    use commonware_codec::Encode;
    let compiled=catalogue::compile(Family::Transfer).unwrap();
    println!("MAC_CERT_RELATION digest={} domain={} public={} blocks={:?}",hex::encode(compiled.relation.digest()),compiled.relation.domain_size(),compiled.relation.public_inputs(),compiled.relation.blocks());
    for index in [200510,200768] {
        let (squared,linear)=compiled.relation.mac_diagnostic_row_certificate(index);
        println!("MAC_CERT_ROW index={index} squared={:?} linear={:?}",squared.iter().map(|(i,c)|(*i,hex::encode(c.encode()))).collect::<Vec<_>>(),linear.iter().map(|(i,c)|(*i,hex::encode(c.encode()))).collect::<Vec<_>>());
    }
}
