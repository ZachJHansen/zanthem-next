#[derive(Copy, Clone)]
pub enum Version {
    Original,
    AbstractGringoCompliant,
}

mod basics;
mod tau_b_cl;
mod val_agc;
mod val_original;

pub mod tau_star;
