#![feature(strict_provenance)]
#![feature(min_specialization)]
#![feature(allocator_api)]
// #![feature(stmt_expr_attributes)]
// #![register_tool(creusot)]
#![allow(dead_code)]
#![allow(path_statements)]
mod bump_allocator;
mod lazy_allocator;
mod lemmas;
mod linked_list;
mod my_box;
mod inv;
mod lazy_allocator_inv;
mod linked_list_inv;
mod my_box_inv;