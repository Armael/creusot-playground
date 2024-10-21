#![feature(ptr_metadata)]

#![cfg_attr(not(creusot),feature(stmt_expr_attributes,proc_macro_hygiene))]
#![cfg_attr(not(creusot),allow(unused_imports,dead_code,unused_variables,unused_assignments))]

pub mod rawptr;
pub mod gptr;
// pub mod list2;
pub mod list2_cleaned;
