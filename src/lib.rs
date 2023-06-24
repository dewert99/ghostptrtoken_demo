#![feature(strict_provenance)]
#![feature(min_specialization)]
#![feature(allocator_api)]
// #![feature(stmt_expr_attributes)]
// #![register_tool(creusot)]

#![allow(dead_code)]
#![allow(path_statements)]
// mod linked_list;
mod lazy_allocator;
mod lemmas;
mod bump_allocator;