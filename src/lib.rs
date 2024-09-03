#![feature(strict_provenance)]
#![feature(min_specialization)]
#![feature(allocator_api)]
// #![feature(stmt_expr_attributes)]
// #![register_tool(creusot)]
#![allow(dead_code)]
#![allow(path_statements)]
mod bump_allocator;
mod lazy_allocator;
mod linked_list;
mod my_box;
mod bfs;
mod hashset;