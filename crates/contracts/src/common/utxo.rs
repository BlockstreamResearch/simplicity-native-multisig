use simplicityhl::elements::{OutPoint, TxOut, TxOutSecrets};

/// Minimal UTXO data needed by the covenant SDK.
#[derive(Debug, Clone)]
pub struct Utxo {
    pub outpoint: OutPoint,
    pub txout: TxOut,
    pub secrets: Option<TxOutSecrets>,
}
